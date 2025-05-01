// This file is heavily inspired by the work done on Portal to ISAbelle (PISA)
// for more information on PISA, go to https://github.com/albertqjiang/Portal-to-ISAbelle
// For this file in particular, go to
// https://github.com/albertqjiang/Portal-to-ISAbelle/blob/main/src/main/scala/pisa/agent/RepHammer.scala

import TheoryManager._

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.control.Isabelle.Setup
import de.unruh.isabelle.mlvalue.MLFunction4
import de.unruh.isabelle.mlvalue.MLValue.{compileFunction, compileFunction0}
import de.unruh.isabelle.mlvalue.AdHocConverter
import de.unruh.isabelle.pure.{Theory, TheoryHeader, ToplevelState}
import de.unruh.isabelle.control.{Isabelle, OperationCollection}
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.{Position, Theory, TheoryHeader}

import scala.concurrent.Future
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.concurrent._
import scala.concurrent.duration._
import scala.util.control.NonFatal
import java.util.concurrent.TimeoutException


import java.nio.file.{Path, Paths}
import scala.util.control.Breaks.{break, breakable}

import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global

import extract._
import inject._

object sledgehammer {

    // Expose a public method to run Sledgehammer on a theory text
    def call_sledgehammer (theoryText: String, filePath: String): (Boolean, (String, List[String])) = {
        
        val isabelleHome: Path = Paths.get("/home/eaj123/Isabellm/Isabelle2022")
        val setup: Setup = Setup(isabelleHome = isabelleHome)
        val theoryManager: TheoryManager = new TheoryManager(
            path_to_isa_bin="/home/eaj123/Isabellm/Isabelle2022",
            wd="/home/eaj123/Isabellm/Test"
        )

        implicit val isabelle: Isabelle = new Isabelle(setup)

        val theorySource = TheoryManager.Text(
        theoryText,
        Paths.get(filePath).toAbsolutePath
        )

        val thy0 = theoryManager.beginTheory(theorySource)
        val init_toplevel = compileFunction0[ToplevelState]("Toplevel.init_toplevel")
        var toplevel = init_toplevel().force.retrieveNow
        
        // Parse and execute transitions
        val parse_text = compileFunction[Theory, String, List[(Transition.T, String)]](
        """fn (thy, text) => let
                |  val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
                |  fun addtext symbols [tr] =
                |        [(tr, implode symbols)]
                |    | addtext _ [] = []
                |    | addtext symbols (tr::nextTr::trs) = let
                |        val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
                |        in (tr, implode this) :: addtext rest (nextTr::trs) end
                |  in addtext (Symbol.explode text) transitions end""".stripMargin
        )

        val command_exception = compileFunction[Boolean, Transition.T, ToplevelState, ToplevelState](
            "fn (int, tr, st) => Toplevel.command_exception int tr st"
        )
        
        breakable {
            for ((transition, text) <- parse_text(thy0, theorySource.text).force.retrieveNow) {
                //println(s"""Transition: "${text.strip}"""")
                toplevel = command_exception(true, transition, toplevel).retrieveNow.force  
            }
        }


        val thy_for_sledgehammer = thy0
        val Sledgehammer: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer")
        val Sledgehammer_Commands: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Commands")
        val Sledgehammer_Prover: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Prover")
      
        val sledgehammerML: MLFunction4[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))] =
            compileFunction[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))](
                s""" fn (state, thy, adds, dels) =>
                |    let
                |       val override = {add=[],del=[],only=false};
                |       fun go_run (state, thy) =
                |          let
                |             val p_state = Toplevel.proof_of state;
                |             val ctxt = Proof.context_of p_state;
                |             val params = ${Sledgehammer_Commands}.default_params thy
                |                [("provers", "e"),("timeout","30"),("verbose","true")];
                |             val results = ${Sledgehammer}.run_sledgehammer params ${Sledgehammer_Prover}.Normal NONE 1 override p_state;
                |             val (result, (outcome, step)) = results;
                |           in
                |             (result, (${Sledgehammer}.short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
                |           end;
                |    in
                |      Timeout.apply (Time.fromSeconds 35) go_run (state, thy) end
                |""".stripMargin
        )
        
        val sledgeFuture = Future {
            sledgehammerML(
                toplevel,
                thy0,
                List[String](), // Added Names
                List[String]()  // Deleted Names
            ).force.retrieveNow
            }

        try {
            Await.result(sledgeFuture, 30.seconds)
        } catch {
            case _: TimeoutException =>
                (false, ("Timeout", List()))
        } finally {
            isabelle.destroy()
        }   

    }

    def sledgehammerAll(filePath: String, lineNumber: Int, isabelleError: String): Unit = {

        val command = extractCommand(isabelleError)
        println(s"Command: $command")
        val all_text = extractToKeyword(filePath, lineNumber, command)
        println("Failed to finish proof. Running Sledgehammer...")
        val (success, (message, solution)) = call_sledgehammer(all_text, filePath)

        if (success) {
            println("Sledgehammer found a solution!")
            val proof = extractProof(solution.head)
            println(proof)
            extractKeyword(filePath, lineNumber, command)
            injectProof(filePath, lineNumber, proof)
        } else {
            println("Sledgehammer failed to find a solution.")
            extractKeyword(filePath, lineNumber, command)
            injectProof(filePath, lineNumber, "sorry")
        }
    }

    def extractProof(message: String) = {

        val pattern = """Try this:\s+(.*)\s+\(\d+\s+ms\)""".r
        message match {
            case pattern(proof) => proof.trim
            case _ => ""
        }
    }
}