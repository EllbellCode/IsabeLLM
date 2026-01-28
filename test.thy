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
proof (induction ts arbitrary: t')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs=[]")
    case True
    then have "x = t'" using Cons(2) by simp
    then show ?thesis using True by simp
  next
    case False
    show ?thesis
    proof (cases "x = t'")
      case t1: True
      then obtain tmax where *: "tmax \<in> set xs" and **: "\<forall>t''\<in>set xs - {tmax}. nHeight t'' \<le> nHeight tmax" using False obtainmax by auto
      with Cons have ***: "foldr max (map nHeight xs) 0 = nHeight tmax" by simp
      show ?thesis
      proof (cases "nHeight x \<ge> nHeight tmax")
        case True
        then have "foldr max (map nHeight (x # xs)) 0 = nHeight x" using *** by auto
        then show ?thesis using t1 by blast
      next
        case False
        then have "foldr max (map nHeight (x # xs)) 0 = nHeight tmax" using *** by auto
        then show ?thesis using t1 * Cons(3) False by auto
      qed
    next
      case False
      then have "t' \<in> set (xs)" using Cons by auto
      moreover from False have *: "nHeight x \<le> nHeight t'" using Cons(3) by simp
      ultimately have "foldr max (map nHeight xs) 0 = nHeight t'" using Cons by auto
      then show ?thesis using * by auto
    qed
  qed
qed

lemma foldr_max_eq2:
  assumes "t' \<in> set ts" 
  and "\<forall>t'' \<in> set ts - {t'}. nHeight t'' < nHeight t'"
shows "foldr max (map nHeight ts) 0 = nHeight t'"
  using foldr_max_eq
  using assms(1) assms(2) order_less_imp_le by blast

fun nPaths :: "'a nTree \<Rightarrow> 'a list list" where
"nPaths (nNode x []) = [[x]]"
|"nPaths (nNode x (t#ts)) = map (\<lambda>p. x # p) (concat (map nPaths (t # ts)))"

fun nLongest :: "'a nTree \<Rightarrow> 'a list set" where
"nLongest t = set (filter (\<lambda>s. length s = nHeight t) (nPaths t))"

lemma height_eq_len:
  assumes "p \<in> nLongest t"
  shows "nHeight t = length p"
  using assms unfolding nLongest.simps by auto
 
lemma branch_height:
  assumes  "p \<in> set (nPaths t)"
  shows "nHeight t \<ge> length p"
  using assms
proof (induct t arbitrary: p)
  case (nNode x ts)
  then show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using nNode by simp
  next
    case (Cons t' ts')
    then obtain p' where p': "p = x # p'" and p'_in: "p' \<in> set (concat (map nPaths (t' # ts')))"
      using nNode(2) by auto
    then obtain sub where sub_in: "sub \<in> set (t' # ts')" and p'_paths: "p' \<in> set (nPaths sub)"
      by auto
    have "nHeight sub \<ge> length p'" using nNode.hyps by presburger
    moreover have "foldr max (map nHeight (t' # ts')) 0 \<ge> nHeight sub"
      using subtree_height[OF sub_in] .
    ultimately show ?thesis using Cons p' by auto
  qed
qed
end