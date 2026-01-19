package utils

// FUNCTIONALITY FOR DEALING WITH ISABELLE BUILD TIMEOUTS

import scala.io.Source
import java.io.{File, PrintWriter}

object timeout {

    val statementKeywords = Set(
        "lemma ", "theorem ", "proposition ", "corollary "
    )

    val otherKeywords = Set(
        "datatype ", "definition ", "fun ", "value ", "section", "record", "text", "locale ", "end", "inductive_set"
    )

    val tacticKeywords = Set(
        "blast", "metis", "auto"
    )

    // Helper to safely read lines and close the file handle immediately
    private def getLinesSafe(filePath: String): List[String] = {
        val source = Source.fromFile(filePath)
        try {
            source.getLines().toList
        } finally {
            source.close()
        }
    }

    def findLines(filePath: String, lemmaName: String): (Int, Int) = {
        // FIXED: Uses getLinesSafe
        val lines = getLinesSafe(filePath)
        
        val lemmaLineOpt = lines.zipWithIndex.find {
            case (line, _) => line.contains(lemmaName)
        }.map(_._2)

        lemmaLineOpt match {
            case Some(lemmaLine) =>
                val proofEndLine = lines.drop(lemmaLine + 1).zipWithIndex.collectFirst {
                    case (line, index) if statementKeywords.exists(line.contains) || otherKeywords.exists(line.contains) =>
                        lemmaLine + 1 + index
                }
                proofEndLine match {
                    case Some(endLine) => (lemmaLine, endLine)
                    case None => (lemmaLine, lines.size - 1)
                }
            case None => (-1, -1)
        }
    }

    def tacticSearch(filePath: String, start: Int, end: Int): Int = {
        // FIXED: Uses getLinesSafe
        val lines = getLinesSafe(filePath)
        
        (start to end).collectFirst {
          case i if tacticKeywords.exists(kw =>
            lines(i).toLowerCase.contains(kw) && !lines(i).contains("(*SAFE*)")
          ) => i
        }.getOrElse(-1)
    }

    def assmsFix(filePath: String, lemmaName: String): Boolean = {
        val (startLine, endLine) = findLines(filePath, lemmaName)
        if (startLine == -1 || endLine == -1) return false

        // FIXED: Uses getLinesSafe
        val lines = getLinesSafe(filePath)
        
        val proofStartIdx = (startLine to endLine).find(i => lines(i).trim.startsWith("proof")).getOrElse(-1)
        if (proofStartIdx == -1) return false

        val lemmaSection = lines.slice(startLine, endLine + 1)
        val proofLineRelIdx = proofStartIdx - startLine
        val usesAssmsAnywhere = lemmaSection.exists(_.contains("assms"))
        val alreadyCorrect = proofLineRelIdx > 0 && lemmaSection(proofLineRelIdx - 1).trim == "using assms"

        if (usesAssmsAnywhere && !alreadyCorrect) {
            val (beforeProof, afterProof) = lemmaSection.splitAt(proofLineRelIdx)
            val newLemmaSection = beforeProof ++ List("  using assms") ++ afterProof
            val newFile = lines.take(startLine) ++ newLemmaSection ++ lines.drop(endLine + 1)
            
            val writer = new PrintWriter(new File(filePath))
            try {
                newFile.foreach(writer.println)
                return true
            } finally {
                writer.close()
            }
        }
        false
    }

    def localeFix(filePath: String, lemmaName: String): Boolean = {
        // FIXED: Uses getLinesSafe
        val lines = getLinesSafe(filePath)
        
        case class Locale(name: String, start: Int, end: Int, assumptions: List[String])
        val localeStartPattern = raw"""locale\s+(\w+)\s*=\s*.*""".r
        val assumesPattern = raw"""assumes\s+(.*)""".r
    
        var locales = List[Locale]()
        var idx = 0

        while (idx < lines.length) {
            lines(idx) match {
                case localeStartPattern(name) =>
                    val start = idx
                    var assumptions = List[String]()
                    var foundBegin = false
                    idx += 1
                    while (idx < lines.length && !foundBegin) {
                        val line = lines(idx).trim
                        line match {
                            case assumesPattern(assms) =>
                                assumptions ++= assms.split("""\s+and\s+""").map(_.takeWhile(_ != ':').trim)
                            case l if l == "begin" => foundBegin = true
                            case _ =>
                        }
                        idx += 1
                    }
                    var depth = 1
                    while (idx < lines.length && depth > 0) {
                        if (lines(idx).trim == "end") depth -= 1
                        else if (lines(idx).contains("locale ")) depth += 1
                        idx += 1
                    }
                    locales ::= Locale(name, start, idx - 1, assumptions)
                case _ => idx += 1
            }
        }
    
        val (startLine, endLine) = findLines(filePath, lemmaName)
        if (startLine == -1 || endLine == -1) return false
    
        val lemmaLocaleOpt = locales.find(l => startLine >= l.start && endLine <= l.end)
        lemmaLocaleOpt.map { locale =>
            val proofStartIdx = (startLine to endLine).find(i => lines(i).trim.startsWith("proof")).getOrElse(-1)
            if (proofStartIdx != -1) {
                val lemmaSection = lines.slice(startLine, endLine + 1)
                val proofLineRelIdx = proofStartIdx - startLine
                val alreadyUsing = proofLineRelIdx > 0 && lemmaSection(proofLineRelIdx - 1).trim.startsWith("using")
    
                if (!alreadyUsing && locale.assumptions.nonEmpty) {
                    val (beforeProof, afterProof) = lemmaSection.splitAt(proofLineRelIdx)
                    val newFile = lines.take(startLine) ++ beforeProof ++ List("  using " + locale.assumptions.mkString(" ")) ++ afterProof ++ lines.drop(endLine + 1)
                    val writer = new PrintWriter(new File(filePath))
                    try { 
                        newFile.foreach(writer.println)
                        true 
                    } finally { 
                        writer.close() 
                    }
                } else false
            } else false
        }.getOrElse(false)
    }
}