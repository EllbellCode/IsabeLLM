theory ConsensusRaw
  imports Main
begin

datatype 'a tree =
    Tip
  | Node "'a tree" 'a "'a tree"

primrec height :: "'a tree \<Rightarrow> nat" where
  "height Tip = 0"
| "height (Node l e r) = Suc (max (height l) (height r))"

proposition height_mono_l: "height r \<le> height l \<Longrightarrow> height l < height l' \<Longrightarrow> 
                            height (Node l e r) < height (Node l' e r)"
  by (induction l; simp)

proposition height_mono_r: "height l \<le> height r \<Longrightarrow> height r < height r' \<Longrightarrow>
                            height (Node l e r) < height (Node l e r')"
by (induction r; simp)

primrec longest:: "'a tree \<Rightarrow> ('a list) set" where
  "longest Tip = {[]}"
| "longest (Node l e r) = { e # p | p. p \<in> (if height l > height r then longest l else if height r > height l then longest r else longest l \<union> longest r)}"

fun check :: "nat \<Rightarrow> nat \<Rightarrow> 'a tree \<Rightarrow> bool" where
  "check 0 d t = True"
| "check (Suc n) d Tip = False"
| "check (Suc n) d (Node l e r) =
    (
    ( (height l - height r > d) \<and> (check n d l) ) \<or>
    ( (height r - height l > d) \<and> (check n d r) )
    )"

lemma check_weaken_distance:
  assumes "check n (Suc x) t"
    shows "check n x t"
using assms by (induction rule: check.induct, auto)

proposition check_weaken_depth:
  assumes "check (Suc x) d t"
  shows "check x d t"
using assms by (induction rule: check.induct, auto)

lemma common_prefix:
  "\<forall>p p'. check n d t \<and> p\<in>longest t \<and> p'\<in>longest t \<longrightarrow> take n p = take n p'"
proof (induction rule: check.induct[of "\<lambda>n d t. \<forall>p p'.
       check n d t \<and> p \<in> longest t \<and> p' \<in> longest t \<longrightarrow> take n p = take n p'"])
  case (1 d t)
  then show ?case by simp
next
  case (2 n d)
  then show ?case by simp
next
  case (3 n d l e r)
  show ?case
  proof (rule+, (erule conjE)+)
    fix p p'
    assume a1: "check (Suc n) d (Node l e r)"
       and a2: "p \<in> longest (Node l e r)"
       and a3: "p' \<in> longest (Node l e r)"
    from a1 consider (1) "d < height l - height r \<and> check n d l" | (2) "d < height r - height l \<and> check n d r" by auto
    then show "take (Suc n) p = take (Suc n) p'"
    proof cases
      case 1
      then have "height r < height l" by auto
      then have "tl p \<in> longest l" and "tl p' \<in> longest l" using a2 a3 by auto
      then have "take n (tl p) = take n (tl p')" using 1 3 by blast
      moreover have "take (Suc n) p = hd p # take n (tl p)" using a2 by auto
      moreover have "take (Suc n) p' = hd p' # take n (tl p')" using a3 by auto
      moreover have "hd p = hd p'" using a2 a3 by auto
      ultimately show ?thesis by simp
    next
      case 2 (*symmetric*)
      then have "height l < height r" by auto
      then have "tl p \<in> longest r" and "tl p' \<in> longest r" using a2 a3 by auto
      then have "take n (tl p) = take n (tl p')" using 2 3 by blast
      moreover have "take (Suc n) p = hd p # take n (tl p)" using a2 by auto
      moreover have "take (Suc n) p' = hd p' # take n (tl p')" using a3 by auto
      moreover have "hd p = hd p'" using a2 a3 by auto
      ultimately show ?thesis by simp
    qed
  qed
qed

record 'a event =
  Honest :: bool
  State :: "'a tree"

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
    shows "count False (e#es) = count False es" unfolding count_def using assms by simp

lemma count_dhonest_false_ind[simp]:
  assumes "\<not> Honest e"
  shows "count False (e#es) = Suc (count False es)" unfolding count_def using assms by simp

lemma count_dhonest_true_ind[simp]:
  assumes "\<not> Honest e"
  shows "count True (e#es) = count True es" unfolding count_def using assms by simp

locale mining =
    fixes add :: "'a tree \<Rightarrow> 'a tree"
    assumes m1: "\<exists>e. add Tip = Node Tip e Tip"
        and m2: "\<And>l e r. add (Node l e r) = Node (add l) e r \<or> add (Node l e r) = Node l e (add r)"
begin

  lemma mining_cases:
    fixes l e r
    obtains (l) "add (Node l e r) = Node (add l) e r"
          | (r) "add (Node l e r) = Node l e (add r)"
    using m2 by auto

  lemma height_add:"height (add t) = height t \<or> height (add t) = Suc (height t)"
  proof (induction t)
    case Tip
    then show ?case using m1 by auto
  next
    case (Node l e r)
    show ?case
    proof (cases rule: mining_cases[of l e r])
      case l
      moreover from this have "height (add (Node l e r)) = height (Node (add l) e r)" by simp
      ultimately show ?thesis using Node(1) by auto
    next
      case r
      moreover from this have "height (add (Node l e r)) = height (Node l e (add r))" by simp
      ultimately show ?thesis using Node(2) by auto
    qed
  qed

lemma check_add:
"check n (Suc d) t \<longrightarrow> (height t < height (add t) \<and> check n (Suc (Suc d)) (add t)) \<or> 
                       (height t = height (add t) \<and> check n (Suc d) (add t)) \<or> 
                       (height t = height (add t) \<and> check n d (add t))"
  proof (induction rule: check.induct[of "\<lambda>n d t. check n (Suc d) t \<longrightarrow> height t < height (add t) \<and> check n (Suc (Suc d)) (add t) \<or> height t = height (add t) \<and> check n (Suc d) (add t) \<or> height t = height (add t) \<and> check n d (add t)"])
    case (1 d t)
    then show ?case using height_add[of t] by auto
  next
    case (2 n d)
    then show ?case by simp
  next
    case (3 n d l e r)
    show ?case
    proof
      assume "check (Suc n) (Suc d) (Node l e r)"
      then consider (l) "Suc d < height l - height r \<and> check n (Suc d) l" | (r) "Suc d < height r - height l \<and> check n (Suc d) r" by auto
      then show "height (Node l e r) < height (add (Node l e r)) \<and> check (Suc n) (Suc (Suc d)) (add (Node l e r)) \<or>
      height (Node l e r) = height (add (Node l e r)) \<and> check (Suc n) (Suc d) (add (Node l e r)) \<or>
      height (Node l e r) = height (add (Node l e r)) \<and> check (Suc n) d (add (Node l e r))"
      proof (cases)
        case l
        then consider "height l < height (add l) \<and> check n (Suc (Suc d)) (add l)" | "height l = height (add l) \<and> check n (Suc d) (add l)" | "height l = height (add l) \<and> check n d (add l)" using 3 by auto
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            moreover have "check (Suc n) (Suc (Suc d)) (Node (add l) e r)" using 1 l by auto
            moreover have "height (Node l e r) < height (add (Node l e r))" using 1 l l2 by auto
            ultimately show ?thesis by simp
          next
            case r
            consider "height (add r) = height r" | "height (add r) = Suc (height r)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using l l1 r by auto
              ultimately show ?thesis by simp
            next
              case x: 2
              moreover have "height l > Suc (height r)" using l by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height l - height (add r)" using x l by auto
                moreover have "check n d l" using l check_weaken_distance[of n d l] by simp
                ultimately show ?thesis using r by simp
              qed
              ultimately show ?thesis by simp
            qed
          qed
        next
          case 2 (*symmetric to case 1*)
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            moreover have "check (Suc n) (Suc d) (Node (add l) e r)" using 2 l by auto
            moreover have "height (Node l e r) = height (add (Node l e r))" using 2 l2 by auto
            ultimately show ?thesis by simp
          next
            case r
            consider "height (add r) = height r" | "height (add r) = Suc (height r)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using l l1 r by auto
              ultimately show ?thesis by simp
            next
              case x: 2
              moreover have "height l > Suc (height r)" using l by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height l - height (add r)" using x l by auto
                moreover have "check n d l" using l check_weaken_distance[of n d l] by simp
                ultimately show ?thesis using r by simp
              qed
              ultimately show ?thesis by simp
            qed
          qed
        next
          case 3 (*symmetric to case 2*)
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            moreover have "check (Suc n) d (Node (add l) e r)" using 3 l by auto
            moreover have "height (Node l e r) = height (add (Node l e r))" using 3 l2 by auto
            ultimately show ?thesis by simp
          next
            case r
            consider "height (add r) = height r" | "height (add r) = Suc (height r)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using l l1 r by auto
              ultimately show ?thesis by simp
            next
              case x: 2
              moreover have "height l > Suc (height r)" using l by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using r by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height l - height (add r)" using x l by auto
                moreover have "check n d l" using l check_weaken_distance[of n d l] by simp
                ultimately show ?thesis using r by simp
              qed
              ultimately show ?thesis by simp
            qed
          qed
        qed
      next
        case r (*symmetric to l case*)
        then consider "height r < height (add r) \<and> check n (Suc (Suc d)) (add r)" | "height r = height (add r) \<and> check n (Suc d) (add r)" | "height r = height (add r) \<and> check n d (add r)" using 3 by auto
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            consider "height (add l) = height l" | "height (add l) = Suc (height l)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using l1 l2 r by auto
              ultimately show ?thesis by simp
            next
              case x: 2
              moreover have "height r > Suc (height l)" using r by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height r - height (add l)" using x r by auto
                moreover have "check n d r" using r check_weaken_distance[of n d r] by simp
                ultimately show ?thesis using l2 by simp
              qed
              ultimately show ?thesis by simp
            qed
          next
            case r2:r
            moreover have "check (Suc n) (Suc (Suc d)) (Node l e (add r))" using 1 r by auto
            moreover have "height (Node l e r) < height (add (Node l e r))" using 1 r r2 by auto
            ultimately show ?thesis by simp
          qed
        next
          case 2
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            consider "height (add l) = height l" | "height (add l) = Suc (height l)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using l2 l1 r by auto
              ultimately show ?thesis by simp
            next
              case x: 2 (*symmetric to 1*)
              moreover have "height r > Suc (height l)" using r by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height r - height (add l)" using x r by auto
                moreover have "check n d r" using r check_weaken_distance[of n d r] by simp
                ultimately show ?thesis using l2 by simp
              qed
              ultimately show ?thesis by simp
            qed
          next
            case r2: r
            moreover have "check (Suc n) (Suc d) (Node l e (add r))" using 2 r by auto
            moreover have "height (Node l e r) = height (add (Node l e r))" using 2 r2 by auto
            ultimately show ?thesis by simp
          qed
        next
          case 3 (*symmetric to 2*)
          then show ?thesis
          proof (cases rule: mining_cases[of l e r])
            case l2: l
            consider "height (add l) = height l" | "height (add l) = Suc (height l)" using height_add by auto
            then show ?thesis
            proof cases
              case l1: 1
              then have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) (Suc d) (add (Node l e r))" using r l1 l2 by auto
              ultimately show ?thesis by simp
            next
              case x: 2
              moreover have "height r > Suc (height l)" using r by auto
              ultimately have "height (Node l e r) = height (add (Node l e r))" using l2 by simp
              moreover have "check (Suc n) d (add (Node l e r))"
              proof -
                have "d < height r - height (add l)" using x r by auto
                moreover have "check n d r" using r check_weaken_distance[of n d r] by simp
                ultimately show ?thesis using l2 by simp
              qed
              ultimately show ?thesis by simp
            qed
          next
            case r2: r
            moreover have "check (Suc n) d (Node l e (add r))" using 3 r by auto
            moreover have "height (Node l e r) = height (add (Node l e r))" using 3 r2 by auto
            ultimately show ?thesis by simp
          qed
        qed
      qed
    qed
  qed

  corollary check_add_cases:
    assumes "check n (Suc d) t"
    obtains "check n (Suc (Suc d)) (add t)" | "check n (Suc d) (add t)" | "check n d (add t)"
    using assms check_add by blast
end

locale honest = mining +
  assumes h1: "\<And>l e r. height l \<ge> height r \<and> add (Node l e r) = Node (add l) e r \<or> 
                       height r \<ge> height l \<and> add (Node l e r) = Node l e (add r)"
begin

lemma mining_cases:
  fixes l e r
  obtains (l) "height l \<ge> height r \<and> add (Node l e r) = Node (add l) e r"
        | (r) "height r \<ge> height l \<and> add (Node l e r) = Node l e (add r)"
  using h1 by auto

lemma height_add: "height (add t) = Suc (height t)"
proof (induction t)
  case Tip
  then show ?case using m1 by auto
next
  case (Node l e r)
  show ?case
  proof (cases rule: mining_cases[of r l e])
    case l
    moreover from this have "height (add (Node l e r)) = height (Node (add l) e r)" by simp
    ultimately show ?thesis using Node(1) by simp
  next
    case r
    moreover from this have "height (add (Node l e r)) = height (Node l e (add r))" by simp
    ultimately show ?thesis using Node(2) by simp
  qed
qed

lemma check_add[rule_format]:
  "check n depth t \<longrightarrow> check n (Suc depth) (add t)"
proof (induction rule: check.induct[of "\<lambda>n d t. check n d t \<longrightarrow> check n (Suc d) (add t)"])
  case (1 d t)
  then show ?case by simp
next
  case (2 n d)
  then show ?case by simp
next
  case (3 n d l e r)
  show ?case
  proof
    assume "check (Suc n) d (Node l e r)"
    then consider "d < height l - height r \<and> check n d l" | "d < height r - height l \<and> check n d r" by auto
    then show "check (Suc n) (Suc d) (add (Node l e r))"
    proof cases
      case 1
      then have "add (Node l e r) = Node (add l) e r" using h1 by fastforce
      moreover have "check (Suc n) (Suc d) (Node (add l) e r)"
      proof -
        from 1 have "Suc d < height (add l) - height r" using height_add by auto
        moreover have "check n (Suc d) (add l)" using 1 3 by simp
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    next
      case 2
      then have "add (Node l e r) = Node l e (add r)" using h1 by force
      moreover have "check (Suc n) (Suc d) (Node l e (add r))"
      proof -
        from 2 have "Suc d < height (add r) - height l" using height_add by auto
        moreover have "check n (Suc d) (add r)" using 2 3 by simp
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
  qed
qed

end

locale blockchain =
  honest hadd + mining dadd
  for hadd::"'a tree \<Rightarrow> 'a tree" and dadd::"'a tree \<Rightarrow> 'a tree" +
  fixes depth::nat
    and t0::"'a tree"
  assumes b1: "check depth (Suc (height t0 - depth)) t0"
      and b2: "height t0 > depth"
begin

inductive_set traces :: "('a event list) set" where
  honest_base: "[\<lparr>Honest = True, State = hadd t0\<rparr>] \<in> traces"
| dishonest_base: "[\<lparr>Honest = False, State = dadd t0\<rparr>] \<in> traces"
| honest_induct: "\<lbrakk>t \<in> traces\<rbrakk> \<Longrightarrow> \<lparr>Honest = True, State = hadd (State (hd t))\<rparr> # t \<in> traces"
| dishonest_induct: "\<lbrakk>t \<in> traces; count False t < count True t + (height t0 - depth)\<rbrakk> \<Longrightarrow> 
                     \<lparr>Honest = False, State = dadd (State (hd t))\<rparr> # t \<in> traces"

lemma bounded_dishonest_mining:
  fixes t
  assumes "t \<in> traces"
  shows "count True t + (height t0 - depth) \<ge> count False t"
  using assms
  using b2 by (induction rule:traces.induct; simp)

lemma bounded_check:
  fixes t
  assumes "t \<in> traces"
  shows "check depth (Suc (count True t + (height t0 - depth) - count False t)) (State (hd t))"
  using assms
proof (induction rule:traces.induct)
  case honest_base
  define t where "t = [\<lparr>Honest = True, State = hadd t0\<rparr>]"
  then have "Suc (count True t + (height t0 - depth) - count False t) = Suc (Suc (height t0 - depth))" by simp
  moreover from b1 have "check depth (Suc (Suc (height t0 - depth))) (hadd t0)" using honest.check_add[of hadd depth "Suc (height t0 - depth)" t0] by (simp add: honest_axioms)
  ultimately show ?case unfolding t_def by simp
next
  case dishonest_base
  define t where "t = [\<lparr>Honest = False, State = dadd t0\<rparr>]"
  then have *: "Suc (count True t + (height t0 - depth) - count False t) = (height t0 - depth)" using b2 by simp
  
  show ?case
  proof (cases rule: check_add_cases[OF b1])
    case 1
    then have "check depth (Suc (height t0 - depth)) (dadd t0)" using * unfolding t_def using check_weaken_distance by simp
    then show ?thesis using * unfolding t_def using check_weaken_distance by simp
  next
    case 2
    then show ?thesis using * unfolding t_def using check_weaken_distance by auto
  next
    case 3
    then show ?thesis using * unfolding t_def by simp
  qed
next
  case (honest_induct t)
  define t' where "t' = \<lparr>Honest = True, State = hadd (State (hd t))\<rparr> # t"
  moreover have "Suc (count True t + (height t0 - depth)) > count False t" using honest_induct bounded_dishonest_mining[OF honest_induct(1)] by simp
  ultimately have "count True t' + (height t0 - depth) - count False t' = Suc (count True t + (height t0 - depth) - count False t)" by simp
  moreover from honest_induct have "check depth (Suc (Suc (count True t + (height t0 - depth) - count False t))) (hadd (State (hd t)))" using honest.check_add[OF honest_axioms, of depth "Suc (count True t + (height t0 - depth) - count False t)" "(State (hd t))"] by (simp add: honest_axioms)
  ultimately show ?case unfolding t'_def using check_weaken_distance[of depth "Suc (count True t + (height t0 - depth) - count False t)" "hadd (State (hd t))"] by simp
next
  case (dishonest_induct t)
  define t' where "t' = \<lparr>Honest = False, State = dadd (State (hd t))\<rparr> # t"
  then have *: "count True t' + (height t0 - depth) - count False t' = count True t + (height t0 - depth) - Suc (count False t)" by simp

  have "check depth (Suc (count True t' + (height t0 - depth) - count False t')) (State (hd t'))"
  proof (cases rule: check_add_cases[OF dishonest_induct(3)])
    case 1
    then have "check depth (Suc ((count True t + (height t0 - depth) - (count False t)))) (dadd (State (hd t)))" using check_weaken_distance[of depth "(Suc (count True t + (height t0 - depth)- count False t))" "(dadd (State (hd t)))"] by simp
    then have "check depth (((count True t + (height t0 - depth) - (count False t)))) (dadd (State (hd t)))" using check_weaken_distance[of depth "(count True t + (height t0 - depth)- count False t)" "(dadd (State (hd t)))"] by simp
    moreover have "count True t + (height t0 - depth) > (count False t)" using dishonest_induct(2) by simp
    ultimately have "check depth (Suc (count True t + (height t0 - depth) - Suc (count False t))) (dadd (State (hd t)))" using Suc_diff_Suc by simp
    then show ?thesis using * unfolding t'_def by simp
  next
    case 2
    then have "check depth (((count True t + (height t0 - depth) - (count False t)))) (dadd (State (hd t)))" using check_weaken_distance[of depth "(count True t + (height t0 - depth)- count False t)" "(dadd (State (hd t)))"] by simp
    moreover have "count True t + (height t0 - depth) > (count False t)" using dishonest_induct(2) by simp
    ultimately have "check depth (Suc (count True t + (height t0 - depth) - Suc (count False t))) (dadd (State (hd t)))" using Suc_diff_Suc by simp
    then show ?thesis using * unfolding t'_def by simp
  next
    case 3
    moreover have "count True t + (height t0 - depth) > (count False t)" using dishonest_induct(2) by simp
    ultimately have "check depth (Suc (count True t + (height t0 - depth) - Suc (count False t))) (dadd (State (hd t)))" using Suc_diff_Suc by simp
    then show ?thesis using * unfolding t'_def by simp
  qed
  then show ?case unfolding t'_def by simp
qed

theorem consensus:
  fixes t
  assumes "t \<in> traces"
  and "p \<in> longest (State (hd t))"
  and "p' \<in> longest (State (hd t))"
shows "take depth p = take depth p'"
using assms(2,3) common_prefix[of depth "Suc (count True t + (height t0 - depth) - count False t)" "(State (hd t))"] bounded_check[OF assms(1)] by blast
end

end