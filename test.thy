theory test
  imports Main
begin

datatype 'a nTree =
  nNode 'a "'a nTree list"


fun nNodes :: "'a nTree \<Rightarrow> nat" where
  "nNodes (nNode x []) = 1"
| "nNodes (nNode x (t # ts)) = Suc (foldr (+) (map nNodes (t # ts)) 0)"

fun nHeight :: "'a nTree \<Rightarrow> nat" where
  "nHeight (nNode x []) = 1"
| "nHeight (nNode x (t # ts)) = Suc (foldr max (map nHeight (t # ts)) 0)"

lemma subtree_height:
  assumes "t \<in> set ts" 
  shows "foldr max (map nHeight ts) 0 \<ge> nHeight t"
  sorry

end