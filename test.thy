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

end
