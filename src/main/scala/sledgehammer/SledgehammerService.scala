package sledgehammer

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.{MLFunction2, MLValue}
import de.unruh.isabelle.mlvalue.MLValue.{compileFunction, compileFunction0}
import de.unruh.isabelle.pure.{Theory, ToplevelState, Transition => IsaTransition}
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import scala.concurrent.{Future, Await}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SledgehammerService(implicit isabelle: Isabelle) {

    private val setupThy = Theory("Main") 

    // Import necessary structures
    private val sledgehammerStruct = setupThy.importMLStructureNow("Sledgehammer")
    private val commandsStruct     = setupThy.importMLStructureNow("Sledgehammer_Commands")
    private val proverStruct       = setupThy.importMLStructureNow("Sledgehammer_Prover")
    
    // Nitpick Structures
    private val nitpickStruct      = setupThy.importMLStructureNow("Nitpick")
    private val nitpickCmdStruct   = setupThy.importMLStructureNow("Nitpick_Commands")

    lazy val init_toplevel: de.unruh.isabelle.mlvalue.MLFunction0[ToplevelState] = 
        compileFunction0[ToplevelState]("fn () => Toplevel.make_state NONE")

    lazy val parse_text: de.unruh.isabelle.mlvalue.MLFunction2[Theory, String, List[(IsaTransition, String)]] = 
        compileFunction[Theory, String, List[(IsaTransition, String)]](
            """fn (thy, text) => let
                    |  val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
                    |  fun addtext symbols [tr] = [(tr, implode symbols)]
                    |    | addtext _ [] = []
                    |    | addtext symbols (tr::nextTr::trs) = let
                    |        val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
                    |        in (tr, implode this) :: addtext rest (nextTr::trs) end
                    |  in addtext (Symbol.explode text) transitions end""".stripMargin
        )

    lazy val command_exception: de.unruh.isabelle.mlvalue.MLFunction3[Boolean, IsaTransition, ToplevelState, ToplevelState] = 
        compileFunction[Boolean, IsaTransition, ToplevelState, ToplevelState](
            "fn (int, tr, st) => Toplevel.command_exception int tr st"
        )

    lazy val sledgehammerML: de.unruh.isabelle.mlvalue.MLFunction4[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))] = 
    compileFunction[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))](
        s""" fn (state, thy, adds, dels) =>
        |    let
        |       val override = {add=[],del=[],only=false};
        |       fun go_run (state, thy) =
        |          let
        |             val p_state = Toplevel.proof_of state;
        |             val params = ${commandsStruct}.default_params thy
        |                [("provers", "cvc5 verit z3 e spass vampire zipperposition"),
        |                   ("timeout","30"),
        |                   ("verbose","true"), 
        |                   ("slices", "96"),
        |                   ("try0", "true"), 
        |                   ("max_proofs", "1")];
        |             val results = ${sledgehammerStruct}.run_sledgehammer params ${proverStruct}.Normal NONE 1 override p_state;
        |             val (result, (outcome, step)) = results;
        |           in
        |             (result, (${sledgehammerStruct}.short_string_of_sledgehammer_outcome outcome, [XML.content_of (YXML.parse_body step)]))
        |           end;
        |    in
        |      Timeout.apply (Time.fromSeconds 90) go_run (state, thy) end
        |""".stripMargin
    )

    // IMPROVED: Parsing YXML to plain text
    lazy val nitpickML: MLFunction2[ToplevelState, Theory, String] = 
    compileFunction[ToplevelState, Theory, String](
        s""" fn (state, thy) =>
        |    let
        |       val p_state = Toplevel.proof_of state;
        |       
        |       (* Use default params to avoid type errors *)
        |       val params = ${nitpickCmdStruct}.default_params thy 
        |           [("timeout", "10"), ("expect", "genuine"), ("batch_size", "1")];
        |       
        |       val mode = ${nitpickStruct}.Auto_Try; 
        |       val i = 1;      
        |       val step = 0;   
        |       
        |       val (outcome, messages) = ${nitpickStruct}.pick_nits_in_subgoal p_state params mode i step;
        |       
        |       (* CRITICAL FIX: Clean YXML markup from messages *)
        |       val cleaned_msgs = map (fn s => XML.content_of (YXML.parse_body s)) messages;
        |       val combined_msg = space_implode "\\n" cleaned_msgs;
        |    in
        |       if combined_msg = "" then outcome else combined_msg
        |    end
        |""".stripMargin
    )

    def call_sledgehammer(currentState: ToplevelState, currentThy: Theory): (Boolean, (String, List[String])) = {
        val sledgeFuture = Future {
            sledgehammerML(currentState, currentThy, Nil, Nil).force.retrieveNow
        }
        try {
            Await.result(sledgeFuture, 95.seconds)
        } catch {
            case _: Exception => (false, ("Timeout or Error", List()))
        }
    }

    def call_nitpick(currentState: ToplevelState, currentThy: Theory): String = {
        val nitpickFuture = Future {
            nitpickML(currentState, currentThy).force.retrieveNow
        }
        try {
            Await.result(nitpickFuture, 15.seconds)
        } catch {
            case e: Exception => 
                println(s"!!! NITPICK CRASHED !!!")
                println(s"Error Message: ${e.getMessage}")
                "Nitpick timeout or error"
        }
    }

    def extractProof(message: String): String = {
        val pattern = """Try this:\s+(.+?)\s+\(\d+(?:\.\d+)?\s+\w+\)$""".r
        message match {
            case pattern(proof) => proof.trim
            case _ => if (message.contains("Try this:")) message.split("Try this:").last.split("\\(").head.trim else ""
        }
    }
}