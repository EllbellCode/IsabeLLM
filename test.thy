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
    by (simp add: nHeight.simps)
  also have "... = Suc (max (nHeight t) (foldr max (map nHeight ts) 0))"
    by simp
  also have "... = Suc (nHeight t)"
    using h_t_ge by (simp add: max.absorb1)
  finally have h_node_t: "nHeight (nNode x (t#ts)) = Suc (nHeight t)" .

  have "nHeight (nNode x (t'#ts)) = Suc (foldr max (map nHeight (t'#ts)) 0)"
    by (simp add: nHeight.simps)
  also have "... = Suc (max (nHeight t') (foldr max (map nHeight ts) 0))"
    by simp
  also have "... = Suc (nHeight t')"
    using h_t_ge h_t_lt by (simp add: max.absorb1 less_imp_le)
  finally have h_node_t': "nHeight (nNode x (t'#ts)) = Suc (nHeight t')" .

  show "nHeight (nNode x (t#ts)) < nHeight (nNode x (t'#ts))"
  using h_node_t h_node_t' h_t_lt by linarith
qed

lemma obtainmax:
  assumes "ts \<noteq> []"
  shows "\<exists>t' \<in> set ts. \<forall>t'' \<in> set ts - {t'}. nHeight t'' \<le> nHeight t'"
proof -
  have "finite (nHeight ` set ts)" by simp
  moreover have "nHeight ` set ts \<noteq> {}" using assms by auto
  then obtain m where "m \<in> nHeight ` set ts" and "\<forall>m' \<in> nHeight ` set ts. m' \<le> m"
by (meson List.finite_set Max_ge Max_in finite_imageI)
  then obtain t' where "t' \<in> set ts" and "nHeight t' = m" by auto
  then have "\<forall>t'' \<in> set ts - {t'}. nHeight t'' \<le> nHeight t'"
    using \<open>\<forall>m' \<in> nHeight ` set ts. m' \<le> m\<close> by auto
  then show ?thesis using \<open>t' \<in> set ts\<close> by blast
qed
end 
