theory test
 imports Main
begin

datatype 'a nTree =
  nNode 'a "'a nTree list"

fun nHeight :: "'a nTree \<Rightarrow> nat" where
  "nHeight (nNode x []) = 1"
| "nHeight (nNode x (t # ts)) = Suc (foldr max (map nHeight (t # ts)) 0)"

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

lemma height_mono_n: 
  "nHeight t < nHeight t' \<Longrightarrow> 
   nHeight t \<ge> foldr max (map nHeight ts) 0 \<Longrightarrow>
   nHeight (nNode x (t#ts)) < nHeight (nNode x (t'#ts))"
proof -
  assume h_t_lt: "nHeight t < nHeight t'"
  assume h_t_ge: "nHeight t \<ge> foldr max (map nHeight ts) 0"

  have "nHeight (nNode x (t#ts)) = Suc (foldr max (map nHeight (t#ts)) 0)"
    by auto
  also have "... = Suc (max (nHeight t) (foldr max (map nHeight ts) 0))"
    by simp
  also have "... = Suc (nHeight t)"
    by (simp add: h_t_ge)
  finally have h_node_t: "nHeight (nNode x (t#ts)) = Suc (nHeight t)" .

  have "nHeight (nNode x (t'#ts)) = Suc (foldr max (map nHeight (t'#ts)) 0)"
    by auto
  also have "... = Suc (max (nHeight t') (foldr max (map nHeight ts) 0))"
    by simp
  also have "... = Suc (nHeight t')"
    using h_t_ge h_t_lt by auto
  finally have h_node_t': "nHeight (nNode x (t'#ts)) = Suc (nHeight t')" .
  
  show "nHeight (nNode x (t#ts)) < nHeight (nNode x (t'#ts))"
  using h_node_t h_node_t' h_t_lt by linarith
qed 

lemma obtainmax:
  assumes "ts \<noteq> []"
  shows "\<exists>t' \<in> set ts. \<forall>t'' \<in> set ts - {t'}. nHeight t'' \<le> nHeight t'"
 proof -
  let ?S = "set (map nHeight ts)"
  have "?S \<noteq> {}" using assms by auto
  moreover have "finite ?S" by simp
  ultimately have "Max ?S \<in> ?S" using Max_in by blast
  then obtain t' where "t' \<in> set ts" and max_height: "nHeight t' = Max ?S"
    by (smt (verit, ccfv_threshold) image_iff list.set_map)
  then have "\<forall>t'' \<in> set ts. nHeight t'' \<le> nHeight t'"
    using Max_ge \<open>finite ?S\<close> \<open>?S \<noteq> {}\<close> max_height by auto
  then show ?thesis using \<open>t' \<in> set ts\<close> by auto
qed

lemma foldr_max_eq:
  assumes "t' \<in> set ts" 
    and "\<forall>t'' \<in> set ts - {t'}. nHeight t'' \<le> nHeight t'"
  shows "foldr max (map nHeight ts) 0 = nHeight t'"
  using assms
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts')
  then show ?case
  proof (cases "t = t'")
    case True
    have "foldr max (map nHeight (t # ts')) 0 = max (nHeight t) (foldr max (map nHeight ts') 0)"
      by simp
    also have "... = max (nHeight t') (foldr max (map nHeight ts') 0)"
      using True by simp
    also have "... = nHeight t'"
    proof -
      from Cons.prems have "\<forall>t''\<in>set ts'. nHeight t'' \<le> nHeight t'"
        using True by auto
      then have "foldr max (map nHeight ts') 0 \<le> nHeight t'"
 sorry
      moreover have "nHeight t' \<ge> 1"
        by (induction t') auto
      ultimately show ?thesis
        by linarith
    qed
    finally show ?thesis by simp
  next
    case False
    then have "t' \<in> set ts'"
      using Cons.prems(1) by auto
    moreover have "\<forall>t''\<in>set ts' - {t'}. nHeight t'' \<le> nHeight t'"
      using Cons.prems(2) False by auto
    ultimately have "foldr max (map nHeight ts') 0 = nHeight t'"
      using Cons.hyps by simp
    moreover have "nHeight t \<le> nHeight t'"
      using Cons.prems(2) False by auto
    ultimately show ?thesis
      by (simp add: max.absorb3)
  qed
qed
end
