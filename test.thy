theory test
  imports Main
begin

(* N-ARY TREE ***********************************************************************************)

(* Node with value of type 'a and list of children of type 'b *)
datatype 'a nTree =
  nNode 'a "'a nTree list"


(*Count the number of nodes in a nTree*)
fun nNodes :: "'a nTree \<Rightarrow> nat" where
  "nNodes (nNode x []) = 1"
| "nNodes (nNode x (t # ts)) = Suc (foldr (+) (map nNodes (t # ts)) 0)"


(* HEIGHT ***************************************************************************)



(*Calculates the height of a tree*)
fun nHeight :: "'a nTree \<Rightarrow> nat" where
  "nHeight (nNode x []) = 1"
| "nHeight (nNode x (t # ts)) = Suc (foldr max (map nHeight (t # ts)) 0)"

(*if t is a tree in a set of trees ts
then t is less than or equal to the maximum height of all the trees in ts*)
lemma foldr_max_ge:
  assumes "x \<in> set xs"
  shows "foldr max xs (0::nat) \<ge> x"
  using assms
  by (induct xs) auto

lemma subtree_height:
  assumes "t \<in> set ts" 
  shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
  using assms foldr_max_ge[of "nHeight t" "map nHeight ts"] by auto
end

(** 
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
**)