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
    with nNode show ?thesis by simp
  next
    case (Cons t ts')
   
    with nNode(2) obtain sub_branch where 
      sub_branch_conc: "p = x # sub_branch" and 
      sub_branch_set: "sub_branch \<in> set (concat (map nPaths (t # ts')))"
      by auto

    then obtain sub_tree  where 
      sub_tree_set : "sub_tree \<in> set (t # ts')" and  
      branch_in_tree: "sub_branch \<in> set (nPaths sub_tree)"
      by auto

    have tree_ge_branch:  "nHeight sub_tree \<ge> length sub_branch"
 using branch_in_tree local.Cons nNode.hyps sub_tree_set by presburger

    moreover have "foldr max (map nHeight (t # ts')) 0 \<ge> nHeight sub_tree"
      by (meson sub_tree_set subtree_height)

    ultimately show ?thesis
      using local.Cons sub_branch_conc by force
  qed
qed

lemma sub_longest:
  assumes "t = nNode n (x#xs)"
      and "p \<in> nLongest t"
      and "p = n # p'"
    shows "\<exists>t'' \<in> set (x#xs). p' \<in> nLongest t''"
proof -
  from assms(2) have p_len: "length p = nHeight t"
    unfolding nLongest.simps by auto
  with assms(3) have len_p': "length p' = nHeight t - 1"
    by auto

  from assms(1) have t_height: "nHeight t = Suc (foldr max (map nHeight (x#xs)) 0)"
    by auto

  from len_p' t_height have len_p'_eq: "length p' = foldr max (map nHeight (x#xs)) 0"
    by simp

  from assms(1,2,3) obtain t'' where t''_def: "t'' \<in> set (x#xs)" "p' \<in> set (nPaths t'')"
    by auto

  have "nHeight t'' = length p'"
  proof -
    from t''_def(1) have "foldr max (map nHeight (x#xs)) 0 \<ge> nHeight t''"
      using subtree_height by fastforce
    moreover from t''_def(2) have "nHeight t'' \<ge> length p'"
      using branch_height by fastforce
    ultimately show ?thesis
      using len_p'_eq by linarith
  qed

  with t''_def show ?thesis
    unfolding nLongest.simps by auto
qed

lemma sub_branch:
  assumes "t = nNode n (x#xs)"
      and "p \<in> nLongest t"
      and "t' \<in> set (x#xs)"
      and "\<forall>t'' \<in> set (x#xs) - {t'}. nHeight t'' < nHeight t'" 
    obtains p' where "p' \<in> nLongest t'" and "p = n # p'"
proof -
  from assms(2)[unfolded nLongest.simps] 
  have p_def: "p \<in> set (filter (\<lambda>s. length s = nHeight t) (nPaths t))" by simp

  from assms(1) have "nHeight t = Suc (foldr max (map nHeight (x#xs)) 0)"
    by simp
  then have "nHeight t = Suc (nHeight t')"
    using foldr_max_eq2[OF assms(3,4)] by simp 
  moreover from p_def obtain p' where "p = n # p'" 
    using assms by auto
  
  ultimately have len_p': "length p' = nHeight t'"
    using assms by auto

  from assms(3-4) have "\<forall>t'' \<in> set (x#xs). nHeight t'' \<le> nHeight t'"
    using order.strict_implies_order by auto 

  from `p = n # p'`
  have "p' \<in> set (concat (map nPaths (x#xs)))"
    using p_def assms(1) unfolding nPaths.simps by auto 

  then obtain t'' where t'_def: "t'' \<in> set (x#xs)" "p' \<in> set (nPaths t'')"
    by auto 

  have "nHeight t'' = length p'"
  proof -
    from t'_def(2) have "nHeight t'' \<ge> length p'"
      using branch_height by fastforce 
    moreover from `\<forall>t'' \<in> set (x#xs). nHeight t'' \<le> nHeight t'` t'_def(1)
    have "nHeight t'' \<le> nHeight t'" by auto 
    ultimately show ?thesis using len_p' by linarith 
  qed 

  with t'_def(2) have "p' \<in> nLongest t''"
    unfolding nLongest.simps by auto 

  have "t'' = t'" using assms by (metis \<open>nHeight t'' = length p'\<close> insert_Diff_single insert_iff len_p' less_irrefl_nat t'_def(1))

  with \<open>p' \<in> nLongest t''\<close> \<open>p = n # p'\<close> 
  show thesis using that by blast 
qed

fun nCheck :: "nat \<Rightarrow> nat \<Rightarrow> 'a nTree \<Rightarrow> bool" where
"nCheck 0 d t = True"
| "nCheck (Suc n) d (nNode x t) = (\<exists>p \<in> set t. (\<forall>p' \<in> set t - {p}. nHeight p - nHeight p' > d) \<and> nCheck n d p)"

lemma n_check_case_condition_1:
  assumes "nCheck (Suc n) d (nNode x t)"
  shows "(\<exists>p \<in> set t. nCheck n d p)"
  using assms by auto 

lemma n_check_case_condition_2:
  assumes "nCheck (Suc n) d (nNode x t)"
  shows "(\<exists>p \<in> set t. (\<forall>p' \<in> set t - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)))"
  using assms by fastforce

lemma n_check_weaken_distance_Node: 
  assumes "nCheck n (Suc d) t"
  shows "nCheck n d t"
  using assms
proof (induction n arbitrary: d t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain x ts where t_def: "t = nNode x ts" by (cases t) auto
  from Suc.prems t_def obtain p where 
    p_in_ts: "p \<in> set ts" and
    height_prop: "\<forall>p'\<in>set ts - {p}. nHeight p - nHeight p' > Suc d" and
    check_p: "nCheck n (Suc d) p"
    by auto
  from Suc.IH[OF check_p] have "nCheck n d p" .
  moreover have "\<forall>p'\<in>set ts - {p}. nHeight p - nHeight p' > d"
 using Suc_lessD height_prop by blast
  ultimately show ?case 
    using p_in_ts t_def by auto
qed

lemma n_check_weaken_depth_Node:
  assumes "nCheck (Suc n) d t"
  shows "nCheck n d t"
  using assms
proof (induction n arbitrary: d t)
  case 0
  then show ?case by (cases t) auto
next
  case (Suc n)
  then obtain x ts where t_def: "t = nNode x ts" by (cases t) auto
  then obtain p where 
    p_in_ts: "p \<in> set ts" and
    height_prop: "\<forall>p'\<in>set ts - {p}. nHeight p - nHeight p' > d" and
    check_p: "nCheck (Suc n) d p"
    using Suc.prems by auto
  from Suc.IH[OF check_p] have "nCheck n d p" .
  with p_in_ts height_prop show ?case using t_def by auto
qed

lemma n_common_prefix:
  "\<forall>r r'. nCheck n d t \<and> r\<in>nLongest t \<and> r'\<in>nLongest t \<longrightarrow> take n r = take n r'"
sorry



end