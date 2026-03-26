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
proof (induction ts arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then have "t \<in> set (y # ys)" by blast (*SAFE*)
  proof (cases "t = y")
    case True
    then have "foldr max (map nHeight (y # ys)) 0 = max (nHeight y) (foldr max (map nHeight ys) 0)" by simp
    also have "... \<ge> nHeight y" by (simp add: le_maxI1)
    also have "nHeight y = nHeight t" using True by simp
    finally show ?case .
  next
    case False
    then have "t \<in> set ys" using \<open>t \<in> set (y # ys)\<close> by auto
    then have IH: "foldr max (map nHeight ys) 0 \<ge> nHeight t" using Cons.hyps by auto
    have "foldr max (map nHeight (y # ys)) 0 = max (nHeight y) (foldr max (map nHeight ys) 0)" by simp
    also have "... \<ge> foldr max (map nHeight ys) 0" by (simp add: le_maxI2)
    also have "... \<ge> nHeight t" using IH .
    finally show ?case .
  qed
qed
end