// This file is heavily inspired by the work done on Portal to ISAbelle (PISA)
// for more information on PISA, go to https://github.com/albertqjiang/Portal-to-ISAbelle
// For this file in particular, go to
// https://github.com/albertqjiang/Portal-to-ISAbelle/blob/main/src/main/scala/pisa/agent/RepHammer.scala


package sledgehammer

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.mlvalue.{MLFunction4, MLValue}
import de.unruh.isabelle.mlvalue.MLValue.{compileFunction, compileFunction0}
import de.unruh.isabelle.pure.{Theory, ToplevelState, Transition => IsaTransition}
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import scala.concurrent.{Future, Await}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

class SledgehammerService(implicit isabelle: Isabelle) {

    // Helper theory to load structures safely
    private val setupThy = Theory("Main") 

    // Safely import structures using the API (Matches your old code logic)
    private val sledgehammerStruct = setupThy.importMLStructureNow("Sledgehammer")
    private val commandsStruct     = setupThy.importMLStructureNow("Sledgehammer_Commands")
    private val proverStruct       = setupThy.importMLStructureNow("Sledgehammer_Prover")

    lazy val init_toplevel: de.unruh.isabelle.mlvalue.MLFunction0[ToplevelState] = 
        compileFunction0[ToplevelState]("Toplevel.init_toplevel")

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

    lazy val sledgehammerML: MLFunction4[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))] = 
    compileFunction[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))](
        s""" fn (state, thy, adds, dels) =>
        |    let
        |       val override = {add=[],del=[],only=false};
        |       fun go_run (state, thy) =
        |          let
        |             val p_state = Toplevel.proof_of state;
        |             val params = ${commandsStruct}.default_params thy
        |                [("provers", "e zipperposition cvc4"),
        |                   ("timeout","30"),
        |                   ("verbose","true"), 
        |                   ("slices", "96"),
        |                   ("try0", "true"), 
        |                   ("max_proofs", "1")];
        |             val results = ${sledgehammerStruct}.run_sledgehammer params ${proverStruct}.Normal NONE 1 override p_state;
        |             val (result, (outcome, step)) = results;
        |           in
        |             (result, (${sledgehammerStruct}.short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
        |           end;
        |    in
        |      Timeout.apply (Time.fromSeconds 90) go_run (state, thy) end
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

    def extractProof(message: String): String = {
        val pattern = """Try this:\s+(.+?)\s+\(\d+(?:\.\d+)?\s+\w+\)$""".r
        message match {
            case pattern(proof) => proof.trim
            case _ => if (message.contains("Try this:")) message.split("Try this:").last.split("\\(").head.trim else ""
        }
    }
}