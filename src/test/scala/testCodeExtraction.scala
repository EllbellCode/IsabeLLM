import scala.util.matching.Regex
import llm.llmOutput._

object testCodeExtraction {

    def main(args: Array[String]): Unit = {
        val testInputs = List(

            // Test case 1: pure isabelle code including lemma statement
            """
           lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
            using assms
            proof (induct ts)
            case Nil
            then show ?case by simp
            next
            case (Cons y ys)
            then show ?case
            proof (cases "t = y")
                case True
                then show ?thesis by auto
            next
                case False
                then show ?thesis using Cons by simp
            qed 
            qed
            """,

            // Test case 2: Code in backticks
            """
            here is the isabelle proof
            ```
            lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
            using assms
            proof (induct ts)
            case Nil
            then show ?case by simp
            next
            case (Cons y ys)
            then show ?case
            proof (cases "t = y")
                case True
                then show ?thesis by auto
            next
                case False
                then show ?thesis using Cons by simp
            qed 
            qed
            ```
            placeholder text
            """,

            // Test case 3: Code in backticks with an isabelle label
            """
            ```isabelle
            lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
            using assms
            proof (induct ts)
            case Nil
            then show ?case by simp
            next
            case (Cons y ys)
            then show ?case
            proof (cases "t = y")
                case True
                then show ?thesis by auto
            next
                case False
                then show ?thesis using Cons by simp
            qed 
            qed
            ```
            """,

            // Test case 4: Code in backticks with a random label with nested qeds containint whitespaces
            """
            ```sadasfdafsds
            lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
            using assms
            proof (induct ts)
            case Nil
            then show ?case by simp
            next
            case (Cons y ys)
            then show ?case
            proof (cases "t = y")
                case True
                then show ?thesis by auto
            next
                case False
                then show ?thesis using Cons by simp
                qed 
            qed
            ```
            """,

            // Test case 5: no backticks or qed
            """
            lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
            using assms by (smt empty_iff empty_set m1)
            """,
            """
           lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
proof (induct n arbitrary: d t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  { fix r r'
    assume "nCheck (Suc n) d t" "r \<in> nLongest t" "r' \<in> nLongest t"
    obtain x ts where t_def: "t = nNode x ts" using nTree.exhaust by blast
    then obtain p where p_in_ts: "p \<in> set ts" 
      and h_diff: "\<forall>p'\<in>set ts - {p}. nHeight p - nHeight p' > d" 
      and check_p: "nCheck n d p" 
      using Suc.prems(1) by force
    from p_in_ts h_diff have fold_eq: "foldr max (map nHeight ts) 0 = nHeight p"
      using foldr_max_eq2 by (metis in_setD)
    from `r \<in> nLongest t` `r' \<in> nLongest t` t_def 
    have "take (Suc n) r = x # take n (tl r)" "take (Suc n) r' = x # take n (tl r')"
      by (simp_all add: hd_Cons_tl nLongest.simps)
    moreover have "tl r \<in> nLongest p" "tl r' \<in> nLongest p" 
      using sub_branch[OF t_def[symmetric]] Suc.prems(2-) sub_branch p_in_ts h_diff check_p
      by (metis list.set_intros(1))+
    ultimately have "take (Suc n) r = take (Suc n) r'" 
      using Suc.hyps[OF check_p] by auto
  }
  then show ?case by blast
qed
            """
        )

        testInputs.zipWithIndex.foreach { case (input, idx) =>
            println(s"\n=== Test Case ${idx + 1} ===")
            val result = extractCode(input, """lemma subtree_height:
            assumes "t \<in> set ts" 
            shows "foldr max (map nHeight ts) 0 \<ge> nHeight t""")
            println(result)
        }
    }
}