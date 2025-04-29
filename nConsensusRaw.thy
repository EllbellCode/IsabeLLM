theory nConsensusRaw
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

proposition height_mono_n: "nHeight t < nHeight t' \<Longrightarrow> nHeight t \<ge> (foldr max (map nHeight ts) 0) \<Longrightarrow>
                            nHeight (nNode x (t#ts)) < nHeight (nNode x (t'#ts))"
proof -
  assume "nHeight t < nHeight t'"
  and "nHeight t \<ge> foldr max (map nHeight ts) 0"
  then have "nHeight (nNode x (t # ts)) = Suc (max (nHeight t) (foldr max (map nHeight ts) 0))" 
    by simp
  also have "... < Suc (max (nHeight t') (foldr max (map nHeight ts) 0))" 
    using `nHeight t < nHeight t'` by (simp add: \<open>foldr max (map nHeight ts) 0 \<le> nHeight t\<close>)
  also have "... = nHeight (nNode x (t' # ts))" 
    by simp
  thus "nHeight (nNode x (t # ts)) < nHeight (nNode x (t' # ts))" 
    by (metis calculation)
qed

lemma obtainmax:
  assumes "ts \<noteq> []"
  shows "\<exists>t' \<in> set ts. \<forall>t'' \<in> set ts - {t'}. nHeight t'' \<le> nHeight t'"
  using assms
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  show ?case
  proof (cases "ts = []")
    case True
    then show ?thesis using Cons by simp
  next
    case False
    then obtain t' where *: "t'\<in>set ts" and **: " \<forall>t''\<in>set ts - {t'}. nHeight t'' \<le> nHeight t'" using Cons(1) by blast
    show ?thesis
    proof (cases "nHeight a \<ge> nHeight t'")
      case True
      then show ?thesis using ** by force
    next
      case False
      then show ?thesis using * ** by fastforce
    qed
  qed
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
proof -
  from assms have "p \<in> set (filter (\<lambda>s. length s = nHeight t) (nPaths t))" by simp
  then have "p \<in> set (nPaths t) \<and> length p = nHeight t" by auto
  then have "nHeight t = length p" by simp
  then show ?thesis by simp
qed

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
      using Cons sub_tree_set nNode.hyps branch_in_tree by blast

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
  from assms(2) have "p \<in> set (filter (\<lambda>s. length s = nHeight t) (nPaths t))"
    by simp
  
  then have path_props: "p \<in> set (nPaths t) \<and> length p = nHeight t" 
    by simp

  then have "p \<in> set (map (\<lambda>f. n # f) (concat (map nPaths (x#xs))))" 
    using assms(1) by simp
    
  then obtain ps where ps_def: "ps \<in> set (concat (map nPaths (x#xs))) \<and> p' = ps"
    using assms(3) by auto
    
  then obtain t'' where t''_def: "t'' \<in> set (x#xs) \<and> ps \<in> set (nPaths t'')"
    by auto

  have *: "nHeight t = Suc (foldr max (map nHeight (x#xs)) 0)" using assms(1) by simp
    
  obtain tmax 
    where tmax_props: "tmax \<in> set (x#xs)" 
      and **: "\<forall>t'''\<in>set (x#xs) - {tmax}. nHeight t''' \<le> nHeight tmax"
    using obtainmax assms(1) by blast

  hence "foldr max (map nHeight (x#xs)) 0 = nHeight tmax"
    using foldr_max_eq by blast
    
  with path_props have "length p = Suc (nHeight tmax)"
    using * by simp
    
  with assms(3) have ***: "length p' = nHeight tmax"
    by simp
    
  have "nHeight t'' \<le> nHeight tmax"
    using t''_def tmax_props ** by auto
    
  moreover have "nHeight t'' \<ge> length ps"
    by (simp add: t''_def branch_height)
    
  ultimately have "nHeight t'' = length p'"
    using *** ps_def by fastforce
    
  thus ?thesis
    using ps_def t''_def by auto
qed

lemma sub_branch:
  assumes "t = nNode n (x#xs)"
      and "p \<in> nLongest t"
      and "t' \<in> set (x#xs)"
      and "(\<forall>t'' \<in> set (x#xs) - {t'}. nHeight t'' < nHeight t')" 
    obtains p' where "p' \<in> nLongest t'" and "p = n # p'"
proof -
  from assms(1) have
      t_def: "t = nNode n (x#xs)" by assumption
  from assms(2) have 
      p_in: "p \<in> set (filter (\<lambda>s. length s = nHeight t) (nPaths t))" by simp
  from p_in have
      p_path: "p \<in> set(nPaths t)" and 
      p_length: "length p = nHeight t" by auto
  from p_path t_def obtain p' where 
      p'_def: "p = n # p'" by auto

  then obtain t'' where 
      t''_def: "t'' \<in> set (x#xs)" and
      p'_path: "p' \<in>  nLongest t''" using sub_longest[OF assms(1) assms(2)] by auto
  from assms(4) and t''_def have 
      not_tallest: "t'' \<noteq> t' \<Longrightarrow> nHeight t'' < nHeight t'" by auto
  with t''_def have 
      max_height: "nHeight t'' \<le> nHeight t'" by fastforce

  from p_length have "length p' = nHeight t - 1" by (simp add: p'_def)

  from p'_path have "length p' = nHeight t''" using height_eq_len by auto

  with p_length p'_def t_def have 
      sub_height: "1 + nHeight t'' = nHeight t" by simp
  from t_def have 
      sub_height_unfold: "nHeight t = 1 + foldr max (map nHeight (x#xs)) 0" by simp
  have "nHeight t'' = foldr max (map nHeight (x#xs)) 0" by (metis sub_height sub_height_unfold diff_Suc_1' plus_1_eq_Suc)

  with max_height have
       t''_t'_height: "nHeight t'' = nHeight t'" by (metis assms(3) assms(4) foldr_max_eq2)
  have t''_t': "t'' = t'" using not_tallest t''_t'_height by auto

  have p'_in: "p' \<in> set(nPaths t')" using t''_t' p'_path by auto

  have "length p' = nHeight t'" by (simp add: \<open>length p' = nHeight t''\<close> t''_t')

  hence "p' \<in> set (filter (\<lambda>s. length s = nHeight t') (nPaths t'))" using p'_in by auto
  hence "p' \<in> nLongest t'" by auto

  with p'_def show ?thesis using that by blast
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
proof (induction n arbitrary: t)
  case 0
  then show ?case by simp
next
  case IH: (Suc nat)
  show ?case
  proof (cases t)
    case (nNode x1 x2)
    then obtain p where *:"p \<in> set x2" and **:"\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > Suc d)" and ***: "nCheck nat (Suc d) p" using IH nNode nCheck.simps(2)[of nat "Suc d" x1 x2] by blast
    then have "\<exists>p \<in> set x2. (\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)) \<and> nCheck nat d p"
    proof -
      have "p \<in> set x2" using * by simp
      moreover have "\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)" using ** by fastforce
      moreover have "nCheck nat d p" using *** IH by simp
      ultimately show ?thesis by blast
    qed
    then show ?thesis using assms IH nNode
      by (smt (verit) nCheck.simps(2) not_less_eq not_less_iff_gr_or_eq)
  qed
qed

lemma n_check_weaken_depth_Node:
  assumes "nCheck (Suc n) d t"
  shows "nCheck n d t"
  using assms
proof (induction n arbitrary: t)
  case 0
  then show ?case by simp
next
  case IH: (Suc nat)
  show ?case
  proof (cases t)
    case (nNode x1 x2)
    show ?thesis
    proof (cases x2)
      case Nil
      then show ?thesis using IH nNode by auto
    next
 case con: (Cons t ts)
  then obtain p where *:"p \<in> set x2" and **:"\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)" and ***: "nCheck nat d p" using IH nNode nCheck.simps(2)[of "(Suc nat)" "d" x1 x2] by blast
  then have "\<exists>p \<in> set x2. (\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)) \<and> nCheck nat d p"
      proof -
        have "p \<in> set x2" using * .
        moreover have "\<forall>p' \<in> set x2 - {p}. (nHeight p' = 0 \<or> nHeight p - nHeight p' > d)" using ** by fastforce
        moreover have "nCheck nat d p" using *** IH by simp
        ultimately show ?thesis by blast
      qed
      then show ?thesis using assms IH nNode by auto
    qed
  qed
qed

lemma n_common_prefix:
  "\<forall>r r'. nCheck n d t \<and> r\<in>nLongest t \<and> r'\<in>nLongest t \<longrightarrow> take n r = take n r'"
proof (induction n arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (rule allI impI)+
    fix r r'
    assume a1 : "nCheck (Suc n) d t \<and> r \<in> nLongest t \<and> r' \<in> nLongest t"
    then have *: "nCheck (Suc n) d t" and **: "r \<in> nLongest t" and ***: "r' \<in> nLongest t" by auto
    obtain v xs where t_def: "t = nNode v xs" using nTree.exhaust by auto

    then obtain p where p_def: "p \<in> set xs"
      and height_cond: "\<forall>p' \<in> set xs - {p}. nHeight p - nHeight p' > d"
      and check_p: "nCheck n d p" using * t_def by fastforce

    have ****:"\<forall>t''\<in>set xs - {p}. nHeight t'' < nHeight p" using height_cond by force

    then obtain p' where " p' \<in> nLongest p" and r_def: "r = v # p'"
      by (smt (verit, best) "**" sub_branch list.set_cases p_def t_def) 
    (*Show the tail of longest paths are in p*)
    then have r_in_p: "tl r \<in> nLongest p" by auto
    
    from **** obtain p'' where "p'' \<in> nLongest p" and r'_def:  "r' = v # p''" 
      by (smt (verit, ccfv_SIG) "***" sub_branch list.set_cases p_def t_def) 

    then have r'_in_p: "tl r' \<in> nLongest p" by auto
    then have take_tl : "take n (tl r) = take n (tl r')" using Suc check_p r'_in_p r_in_p by blast

    (*Combining head and tail in take function*)
    have hd_take_r : "(hd r) # take n (tl r) = take (Suc n) r"
      by (simp add: r_def)
    have hd_take_r' : "(hd r') # take n (tl r') = take (Suc n) r'"
      by (simp add: r'_def)

    then show "take (Suc n) r = take (Suc n) r'" using r_def r'_def hd_take_r hd_take_r' take_tl by simp  
  qed
qed

record 'a event =
  Honest :: bool
  State :: "'a nTree"

definition count::"bool \<Rightarrow> ('a event) list \<Rightarrow> nat" where
  "count b = List.length \<circ> filter (\<lambda>x. Honest x = b)"

lemma count_true_base[simp]:
  "count True [] = 0" unfolding count_def by simp

lemma count_false_base[simp]:
  "count False [] = 0" unfolding count_def by simp

lemma count_honest_true_ind[simp]:
  assumes "Honest e"
    shows "count True (e#es) = Suc (count True es)" unfolding count_def using assms by simp

lemma count_honest_false_ind[simp]:
  assumes "Honest e"
  shows "count False (e#es) = count False es" 
  unfolding count_def using assms by simp

lemma count_dhonest_false_ind[simp]:
  assumes "\<not> Honest e"
  shows "count False (e#es) = Suc (count False es)" unfolding count_def 
  using assms by simp

lemma count_dhonest_true_ind[simp]:
  assumes "\<not> Honest e"
  shows "count True (e#es) = count True es" unfolding count_def 
  using assms by simp

locale mining =
    fixes add :: "'a nTree \<Rightarrow> 'a nTree"
    assumes m1: "add  (nNode x ts) = nNode x ys \<and> (\<exists> t' \<in> set ts. set ys = insert (add t') (set ts  - {t'}))"
        and m2: "\<exists>e. add (nNode x []) = nNode x [nNode e []]"  
begin

lemma mining_cases:
    fixes x ts
    obtains (mined) "add  (nNode x ts) = nNode x ys \<and> (\<exists> t' \<in> set ts. set ys = insert (add t') (set ts  - {t'}))"
    using m1 by auto

lemma height_add:"nHeight (add t) = nHeight t \<or> nHeight (add t) = Suc (nHeight t)"
proof (induct t)
  case (nNode x ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
    proof -
      have *: "nHeight (nNode x ts) = 1" using nHeight.simps(1) Nil by auto
      have "\<exists>e.  add (nNode x ts) =  (nNode x [nNode e []])" by (simp add: local.Nil m2)
      then obtain e where " add (nNode x ts) =  (nNode x [nNode e []])" by auto
      then have "nHeight (add (nNode x ts)) = 2" by auto
      then show ?thesis using * by auto 
    qed
  next
    case (Cons t ts')
    then show ?thesis
    proof -
      obtain ys where
        ys_def: "add (nNode x (t # ts')) = nNode x ys" and
                "\<exists>t'\<in>set (t # ts'). set ys = insert (add t') (set (t # ts') - {t'})"
      using m1 by presburger

      then obtain t' where 
        t'_def: "t' \<in> set (t # ts')" and 
        ys_set: "set ys = insert (add t') (set (t # ts') - {t'})" 
      by blast

      then  have "nHeight (nNode x ys) \<le> Suc (max (nHeight (add t')) (foldr max (map nHeight (filter (\<lambda>x. x \<noteq> t') (t # ts'))) 0))"   
        by (metis le_SucI max.cobounded1 mining_cases nHeight.simps(1)
            nTree.exhaust)
    
      then show ?thesis
      by (metis m1)
  qed
qed
qed

lemma nCheck_add: "nCheck n (Suc d) t \<longrightarrow> 
                          (nHeight t < nHeight (add t) \<and> nCheck n (Suc (Suc d)) (add t)) \<or> 
                          (nHeight t = nHeight (add t) \<and>  nCheck n (Suc d) (add t)) \<or> 
                          (nHeight t = nHeight (add t) \<and>  nCheck n d (add t))"
  by (metis m1 nTree.exhaust)
 
   corollary check_add_cases:
    assumes "nCheck n (Suc d) t"
    obtains "nCheck n (Suc (Suc d)) (add t)" | "nCheck n (Suc d) (add t)" | "nCheck n d (add t)"
     using assms nCheck_add by auto
end

locale honest = mining +
  assumes h : "add  (nNode x ts) = nNode x ys \<and> (\<exists> t' \<in> set ts. set ys = insert (add t') (set ts  - {t'}) \<and> foldr max (map nHeight ts) 0 = nheight t')"
begin

lemma mining_cases:
  fixes x ts
  obtains (mined) "add  (nNode x ts) = nNode x ys \<and> (\<exists> t' \<in> set ts. set ys = insert (add t') (set ts  - {t'}) \<and> foldr max (map nHeight ts) 0 = nheight t')"
  using h by auto

lemma height_add: "nHeight (add t) = Suc (nHeight t)"
proof (induct t)
  case (nNode x ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis
    proof -  
      obtain e where "add (nNode x []) = nNode x [nNode e []]"
        using m2 by blast
      hence "nHeight (add (nNode x [])) = Suc (foldr max (map nHeight [nNode e []]) 0)"
        by simp
      also have "... = Suc (max (nHeight (nNode e [])) 0)"
        by simp
      also have "... = Suc (max 1 0)"
        by auto
      also have "... = Suc 1"
        by simp
      also have "... = 2"
        by simp
      finally have "nHeight (add (nNode x [])) = 2" .
      moreover have "nHeight (nNode x []) = 1"
        by auto
      ultimately show ?thesis
         by (simp add: local.Nil)
    qed
  next
    case (Cons t ts')
    then obtain ys where
        ys_def: "add (nNode x (t # ts')) = nNode x ys" and
                "\<exists>t'\<in>set (t # ts'). set ys = insert (add t') (set (t # ts') - {t'}) \<and> foldr max (map nHeight (t # ts')) 0 = nHeight t'"
       by (meson mining_cases)
   
    then obtain t' where 
        t'_def: "t' \<in> set (t # ts')" and 
        ys_set: "set ys = insert (add t') (set (t # ts') - {t'})" and
        max_eq: "foldr max (map nHeight (t # ts')) 0 = nHeight t'"
        by blast
      
    have "foldr max (map nHeight ys) 0 = nHeight (add t')"
      by (meson h)

    then show ?thesis
    using m1[of undefined "[]" "[_]"] by fastforce
    
  qed
qed

lemma nCheck_add:
  "nCheck n depth t \<longrightarrow> nCheck n (Suc depth) (add t)"
proof (induct t arbitrary: n depth) 
  case (nNode x ts)
  show ?case
  proof (cases ts)
    case Nil
    then show ?thesis using m2
    by (metis List.insert_def insert_Nil list.distinct(1) nCheck.simps(1) n_check_case_condition_1 old.nat.exhaust)
  next
    case (Cons t ts')
   
    then obtain ys where ys_def: "add (nNode x (t # ts')) = nNode x ys"
      and "\<exists>t'\<in>set (t # ts'). set ys = insert (add t') (set (t # ts') - {t'})"
      using m1 by presburger
    then obtain t' where t'_def: "t' \<in> set (t # ts')"
      and ys_set: "set ys = insert (add t') (set (t # ts') - {t'})" by blast
 
    show ?thesis
    proof -
    
      obtain p where p_def: "p \<in> set (t # ts')"
        and p_check: "nCheck n depth p"
        and p_height: "\<forall>p'\<in>set (t # ts') - {p}. nHeight p - nHeight p' > depth"
        by (smt all_not_in_conv m1 set_empty2)
       

      have "add t' \<in> set ys" using ys_set t'_def by auto
      moreover have "nCheck n (Suc depth) (add t')"
        by (smt empty_iff empty_set m1) 
      moreover have "\<forall>p'\<in>set ys - {add t'}. nHeight (add t') - nHeight p' > Suc depth"
        by (smt all_not_in_conv m1 set_empty)
      ultimately have "nCheck n (Suc depth) (add (nNode x (t # ts')))"
        by (smt empty_iff empty_set m1)
      then show ?thesis by (simp add: local.Cons)
    qed
  qed
qed

end

locale blockchain =
  honest hadd + mining dadd
  for hadd::"'a nTree \<Rightarrow> 'a nTree" and dadd::"'a nTree \<Rightarrow> 'a nTree" +
  fixes depth::nat
    and t0::"'a nTree"
  assumes b1: "nCheck depth (Suc (nHeight t0 - depth)) t0"
      and b2: "nHeight t0 > depth"
begin

inductive_set traces :: "('a event list) set" where
  honest_base: "[\<lparr>Honest = True, State = hadd t0\<rparr>] \<in> traces"
| dishonest_base: "[\<lparr>Honest = False, State = dadd t0\<rparr>] \<in> traces"
| honest_induct: "\<lbrakk>t \<in> traces\<rbrakk> \<Longrightarrow> \<lparr>Honest = True, State = hadd (State (hd t))\<rparr> # t \<in> traces"
| dishonest_induct: "\<lbrakk>t \<in> traces; count False t < count True t + (nHeight t0 - depth)\<rbrakk> \<Longrightarrow> 
                     \<lparr>Honest = False, State = dadd (State (hd t))\<rparr> # t \<in> traces"

lemma bounded_dishonest_mining:
  fixes t
  assumes "t \<in> traces"
  shows "count True t + (nHeight t0 - depth) \<ge> count False t"
  using assms
  using b2 by (induction rule:traces.induct; simp)

lemma bounded_check:
  fixes t
  assumes "t \<in> traces"
  shows "nCheck depth (Suc (count True t + (nHeight t0 - depth) - count False t)) (State (hd t))"
using assms
proof (induction rule: traces.induct)
  case (honest_base)
  then show ?case
   by (simp add: b1 honest.nCheck_add honest_axioms)
next
  case (dishonest_base)
  then show ?case
    by (metis One_nat_def Suc_pred' add_eq_if b1 b2 count_dhonest_false_ind count_dhonest_true_ind count_false_base count_true_base list.sel(1) mining.check_add_cases mining_axioms n_check_weaken_distance_Node select_convs(1) select_convs(2) zero_less_diff)
next
  case (honest_induct t)
  then show ?case
    by (simp add: Suc_diff_le bounded_dishonest_mining honest.nCheck_add honest_axioms)   
next
  case (dishonest_induct t)
  then show ?case
    by (metis Suc_diff_Suc count_dhonest_false_ind count_dhonest_true_ind list.sel(1) mining.check_add_cases mining_axioms n_check_weaken_distance_Node select_convs(1) select_convs(2))
qed

theorem n_consensus:
  fixes t
  assumes "t \<in> traces"
  and "p \<in> nLongest (State (hd t))"
  and "p' \<in> nLongest (State (hd t))"
shows "take depth p = take depth p'"
proof -
  have "nCheck depth (Suc (count True t + (nHeight t0 - depth) - count False t)) (State (hd t))"
    using assms(1) by (rule bounded_check)
  then show ?thesis
    using assms(2,3) n_common_prefix by blast
qed
end

end