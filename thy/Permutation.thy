theory Permutation
imports Main "HOL-Library.FSet" MoreList
begin

text \<open>Permutation type\<close>

lemma distinct_perm [simp]:
  assumes "set p = {0..<length p}"
  shows "distinct p"
  using assms
  by (simp add: card_distinct)
                                              
typedef perm = "{p::nat list. set p = {0..<length p}}"
  morphisms perm_list Abs_perm
  by (rule_tac x="[]" in exI, auto)

setup_lifting type_definition_perm

text \<open>Domain of a permutation is always  the set of the form {0..<n}\<close>
lift_definition perm_dom :: "perm \<Rightarrow> nat" is
  "length"
  done

lemma perm_list_set [simp]:
  shows "set (perm_list p) = {0..<perm_dom p}"
  by transfer simp

text \<open>Permutation as a function that acts on {0..<n}\<close>

definition perm_fun' :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "perm_fun' p = (\<lambda> k. if k < length p then p ! k else undefined)"

lift_definition perm_fun :: "perm \<Rightarrow> nat \<Rightarrow> nat" is perm_fun'
  done

lemma permEqI:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" 
          "\<forall> v < n. perm_fun p1 v = perm_fun p2 v" 
  shows "p1 = p2"
  using assms
  by transfer (auto simp add: perm_fun'_def nth_equalityI)

lemma perm_fun_inj:
  assumes "perm_dom p = n" "v1 < n" "v2 < n" "perm_fun p v1 = perm_fun p v2"
  shows "v1 = v2"
  using assms
  by (metis distinct_perm nth_eq_iff_index_eq perm_dom.rep_eq perm_fun'_def perm_fun.rep_eq perm_list_set)

definition is_perm_fun :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_perm_fun n p \<longleftrightarrow> bij_betw p {0..<n} {0..<n}"

lemma is_perm_fun [simp]: 
  "is_perm_fun (perm_dom p) (perm_fun p)"
proof transfer
  fix p
  assume *: "set p = {0..<length p}"
  let ?f = "\<lambda> k. if k < length p then p ! k else undefined"
  show "is_perm_fun (length p) (perm_fun' p)"
    unfolding is_perm_fun_def perm_fun'_def bij_betw_def
  proof
    show "inj_on ?f {0..<length p}"
      using distinct_perm[OF *]
      by (simp add: nth_eq_iff_index_eq inj_on_def perm_fun'_def)
  next
    show "?f ` {0..<length p} = {0..<length p}"
    proof safe
      fix k
      assume "k \<in> {0..<length p}"
      then show "?f k \<in> {0..<length p}"
        using *
        by (metis atLeastLessThan_iff nth_mem)
    next
      fix k
      assume "k \<in> {0..<length p}"
      then show "k \<in> ?f ` {0..<length p}"
        using *
        by (simp add: nth_image)
    qed
  qed
qed

lemma is_perm_fun_comp [simp]:
  assumes "is_perm_fun n f" "is_perm_fun n g"
  shows "is_perm_fun n (f \<circ> g)"
  using assms
  unfolding is_perm_fun_def
  using bij_betw_trans by blast

definition inv_perm_fun :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "inv_perm_fun n f = (\<lambda> y. (THE x. x < n \<and> f x = y))"

lemma inv_perm_fun:
  assumes "is_perm_fun n f" "x < n" "f x = y" 
  shows "inv_perm_fun n f y = x"
proof-
  have "\<exists>! x. x < n \<and> f x = y"
    using assms
    unfolding is_perm_fun_def
    by (metis atLeast0LessThan bij_betw_iff_bijections lessThan_iff)
  then show ?thesis
    using assms(2-3)
    unfolding inv_perm_fun_def
    by (simp add: the1_equality)
qed

lemma inv_perm_fun_perm_fun:
  assumes "is_perm_fun n f"
  shows "is_perm_fun n (inv_perm_fun n f)" 
  using assms
  unfolding is_perm_fun_def bij_betw_def
  by (smt (z3) assms atLeastLessThan_iff f_the_inv_into_f image_cong image_iff inj_on_cong inj_on_the_inv_into inv_perm_fun the_inv_into_onto)

text \<open>Each bijective function gives rise to a permutation\<close>

definition make_perm' :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat list" where
  "make_perm' n f = 
     (if is_perm_fun n f then map f [0..<n] else [])"

lift_definition make_perm :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> perm" is make_perm'
  unfolding make_perm'_def is_perm_fun_def
  by (auto simp add: bij_betw_def)

lemma perm_dom_make_perm[simp]:
  assumes "is_perm_fun n f"
  shows "perm_dom (make_perm n f) = n"
  using assms
  by transfer (simp add: make_perm'_def)

lemma perm_fun_make_perm [simp]:
  assumes "is_perm_fun n f" "x < n"
  shows "perm_fun (make_perm n f) x = f x"
  using assms
  by transfer (simp add: make_perm'_def perm_fun'_def)

lemma make_perm_perm_fun [simp]:
  assumes "perm_dom p = n"
  shows "make_perm n (perm_fun p) = p"
proof-
  have "is_perm_fun n (perm_fun p)"
    using assms is_perm_fun by auto
  thus ?thesis
    using assms
    by transfer (smt (z3) make_perm'_def perm_fun'_def atLeast0LessThan lessThan_iff map_eq_conv map_nth set_upt)
qed

lemma make_perm_cong:
  assumes "\<forall> v < n. f1 v = f2 v" "is_perm_fun n f1" "is_perm_fun n f2"
  shows "make_perm n f1 = make_perm n f2"
  using assms
  by transfer (simp add: make_perm'_def)

subsection \<open>Permutation group\<close>

definition perm_id' :: "nat \<Rightarrow> nat list" where
 "perm_id' n = [0..<n]"

lift_definition perm_id :: "nat \<Rightarrow> perm" is perm_id'
  by (simp add: perm_id'_def)

lemma perm_fun_perm_id [simp]:
  assumes "x < n"
  shows "perm_fun (perm_id n) x = x"
  using assms
  by transfer (auto simp add: perm_id'_def perm_fun'_def)


definition perm_inv' :: "nat list \<Rightarrow> nat list" where
  "perm_inv' p = map (index_of p) [0..<length p]"

lift_definition perm_inv :: "perm \<Rightarrow> perm" is perm_inv'
proof-
  fix xs
  assume *: "set xs = {0..<length xs}"
  show "set (perm_inv' xs) = {0..<length (perm_inv' xs)}" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      using * index_of_in_set[of _ xs]
      by (auto simp add: perm_inv'_def)
  next
    show "?rhs \<subseteq> ?lhs"
      using *
      by (smt (verit, ccfv_SIG) atLeastLessThan_iff distinct_perm image_iff index_of_in_set length_map map_nth nth_eq_iff_index_eq nth_mem perm_inv'_def set_map set_upt subsetI)
  qed
qed

lemma perm_dom_perm_inv [simp]:
  "perm_dom (perm_inv p) = perm_dom p"
  by transfer (auto simp add: perm_inv'_def)

lemma perm_inv_inv [simp]:
  shows "perm_inv (perm_inv p) = p"
proof transfer
  fix p
  assume *: "set p = {0..<length p}"
  show "perm_inv' (perm_inv' p) = p"
  proof (rule nth_equalityI)
    show "length (perm_inv' (perm_inv' p)) = length p"
      unfolding perm_inv'_def
      by auto
  next
    fix i
    assume "i < length (perm_inv' (perm_inv' p))"
    then show "perm_inv' (perm_inv' p) ! i = p ! i"
      using *
      unfolding perm_inv'_def
      by (smt (verit, ccfv_SIG) atLeast0LessThan distinct_Ex1 distinct_perm index_of_in_set length_map lessThan_iff map_nth nth_map nth_mem set_upt)
  qed
qed

lemma perm_inv_perm_id [simp]:
  shows "perm_inv (perm_id n) = perm_id n"
  by (smt (verit, ccfv_SIG) atLeast0LessThan diff_zero index_of_in_set length_upt lessThan_iff nth_map permEqI perm_dom.rep_eq perm_dom_perm_inv perm_fun'_def perm_fun.rep_eq perm_fun_perm_id perm_id'_def perm_id.rep_eq perm_inv'_def perm_inv.rep_eq perm_list_set)

lemma perm_fun_perm_inv_range:
  assumes "perm_dom p = n"
  shows "\<forall> x < n. (perm_fun (perm_inv p)) x < n"
  using assms
  by transfer (auto simp add: perm_fun'_def perm_inv'_def index_of_in_set)

lemma perm_fun_perm_inv1_comp:
  assumes "perm_dom p = n"
  shows "\<forall> x < n. ((perm_fun p) \<circ> (perm_fun (perm_inv p))) x = x"
  using assms
  by transfer (auto simp add: perm_fun'_def perm_inv'_def index_of_in_set)

lemma perm_fun_perm_inv2_comp:
  assumes "perm_dom p = n"
  shows "\<forall> x < n. ((perm_fun (perm_inv p)) \<circ> (perm_fun p)) x = x"
  using assms
  by transfer (smt (verit, ccfv_threshold) add.left_neutral diff_zero distinct_Ex1 distinct_perm index_of_in_set length_map length_upt lessThan_atLeast0 lessThan_iff nth_map nth_mem nth_upt o_def perm_fun'_def perm_inv'_def)

lemma perm_fun_perm_inv1 [simp]:
  assumes "perm_dom p = n" "x < n"
  shows "perm_fun p (perm_fun (perm_inv p) x) = x"
  using assms
  using perm_fun_perm_inv1_comp
  by auto

lemma perm_fun_perm_inv2 [simp]:
  assumes "perm_dom p = n" "x < n"
  shows "perm_fun (perm_inv p) (perm_fun p x) = x"
  using assms
  using perm_fun_perm_inv2_comp
  by auto

lemma perm_inv_make_perm1 [simp]:
  assumes "is_perm_fun n f" "v < n"
  shows "f (perm_fun (perm_inv (make_perm n f)) v) = v"
  using assms
  by (metis perm_dom_make_perm perm_fun_make_perm perm_fun_perm_inv1 perm_fun_perm_inv_range)

lemma perm_inv_make_perm2 [simp]:
  assumes "is_perm_fun n f" "v < n"
  shows "perm_fun (perm_inv (make_perm n f)) (f v) = v"
  using assms
  by (metis perm_dom_make_perm perm_fun_make_perm perm_fun_perm_inv2)

lemma make_perm_inv_perm_fun:
  assumes "is_perm_fun n f"
  shows "make_perm n (inv_perm_fun n f) = perm_inv (make_perm n f)"
  using assms
proof transfer
  fix n f
  assume *: "is_perm_fun n f"
  have "\<forall>x\<in>{0..<n}. inv_perm_fun n f x = index_of (map f [0..<n]) x"
  proof
    fix x
    assume "x \<in> {0..<n}"
    show "inv_perm_fun n f x = index_of (map f [0..<n]) x"
      by (smt (z3) "*" \<open>x \<in> {0..<n}\<close> add.left_neutral bij_betw_def diff_zero index_of_in_set inv_perm_fun is_perm_fun_def length_map length_upt nth_map_upt set_map set_upt)
  qed
  then show "make_perm' n (inv_perm_fun n f) = perm_inv' (make_perm' n f)"
    using *
    by (auto simp add: make_perm'_def inv_perm_fun_perm_fun perm_inv'_def)
qed


definition perm_comp' :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "perm_comp' p1 p2 = 
     (if length p1 = length p2 then 
         map (perm_fun' p1) p2
      else
        [])"

lift_definition perm_comp :: "perm \<Rightarrow> perm \<Rightarrow> perm" is perm_comp'
  apply (auto simp add: perm_comp'_def perm_fun'_def)
  apply (metis IntI atLeast0LessThan imageI in_set_conv_nth lessThan_iff mem_Collect_eq)
  done

lemma perm_dom_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n"
  shows "perm_dom (perm_comp p1 p2) = n"
  using assms
  by transfer (auto simp add: perm_comp'_def)

lemma perm_fun_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n"
  shows "\<forall> x < n. perm_fun (perm_comp p1 p2) x = (perm_fun p1 \<circ> perm_fun p2) x"
  using assms
proof transfer
  fix p1 p2 n
  assume *: "length p1 = n" "length p2 = n" "set p1 = {0..<length p1}" "set p2 = {0..<length p2}"
  then show "\<forall> x < n. perm_fun' (perm_comp' p1 p2) x = (perm_fun' p1 \<circ> perm_fun' p2) x" 
    by (auto simp add: perm_fun'_def perm_comp'_def)
qed

lemma perm_comp_assoc:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" "perm_dom p3 = n"
  shows "perm_comp (perm_comp p1 p2) p3 = perm_comp p1 (perm_comp p2 p3)"
  sorry

lemma perm_comp_make_perm [simp]:
  assumes "is_perm_fun n p1" "is_perm_fun n p2" 
  shows "perm_comp (make_perm n p1) (make_perm n p2) = make_perm n (p1 \<circ> p2)"
  using assms
proof-
  have "is_perm_fun n (p1 \<circ> p2)"
    using assms
    by simp
  then show ?thesis
    using assms
    by transfer (auto simp add: perm_comp'_def make_perm'_def perm_fun'_def is_perm_fun_def bij_betw_def)
qed

lemma perm_comp_perm_id_1 [simp]:
  assumes "perm_dom p = n"
  shows "perm_comp (perm_id n) p = p"
  using assms
  by transfer (metis (mono_tags, lifting) atLeast0LessThan distinct_card distinct_perm eq_onp_same_args length_remdups_card_conv lessThan_iff map_idI perm_comp'_def perm_fun.abs_eq perm_fun_perm_id perm_id'_def perm_id.abs_eq remdups_upt set_upt)

lemma perm_comp_perm_id_2 [simp]:
  assumes "perm_dom p = n"
  shows "perm_comp p (perm_id n) = p"
  using assms
  by transfer (smt (z3) atLeast0LessThan distinct_card distinct_perm length_remdups_card_conv lessThan_iff map_eq_conv map_nth perm_comp'_def perm_fun'_def perm_id'_def remdups_upt set_upt)

lemma perm_comp_perm_inv1 [simp]:
  assumes "perm_dom p = n"
  shows "perm_comp (perm_inv p) p = perm_id n"
  using assms
proof transfer
  fix p n
  assume "set p = {0..<length p}" "length p = n"
  have "map (\<lambda> k. map (index_of p) [0..<length p] ! k) p = [0..<length p]"
  proof-
    let ?f = "(\<lambda> k. map (index_of p) [0..<length p] ! k)"
    let ?g = "\<lambda> i. p ! i"

    have *: "\<forall> x < length p. (?f \<circ> ?g) x = x"
    proof safe
      fix x
      assume "x < length p"
      then show "(?f \<circ> ?g) x = x"
        using \<open>set p = {0..<length p}\<close> index_of_in_set[of "p ! x" p]
        by (metis atLeastLessThan_iff comp_def distinct_perm length_map map_nth nth_eq_iff_index_eq nth_map nth_mem set_upt)
    qed

    have "p = map (\<lambda> i. p ! i) [0..<length p]"
      by (simp add: map_nth)
    then have "map ?f p = map (?f \<circ> (\<lambda> i. p ! i)) [0..<length p]"
      by (metis map_map)
    then show ?thesis
      using *
      by (metis atLeast0LessThan lessThan_iff map_idI set_upt)
  qed

  then show "perm_comp' (perm_inv' p) p = perm_id' n"
    using \<open>length p = n\<close> \<open>set p = {0..<length p}\<close> 
    unfolding perm_comp'_def perm_inv'_def perm_id'_def perm_fun'_def
    by (smt (verit, ccfv_SIG) atLeast0LessThan length_map lessThan_iff map_eq_conv)
qed

lemma perm_comp_perm_inv2 [simp]:
  assumes "perm_dom p = n"
  shows "perm_comp p (perm_inv p) = perm_id n"
  by (metis assms perm_comp_perm_inv1 perm_dom_perm_inv perm_inv_inv)

lemma perm_inv_solve:
  assumes "perm_dom p1 = n" "perm_dom p2 = n"  "perm_comp p1 p2 = perm_id n"
  shows "p1 = perm_inv p2"
  using assms
  sorry

lemma perm_inv_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n"
  shows "perm_inv (perm_comp p1 p2) = perm_comp (perm_inv p2) (perm_inv p1)"
proof (rule perm_inv_solve[symmetric])
  show "perm_comp (perm_comp (perm_inv p2) (perm_inv p1)) (perm_comp p1 p2) = perm_id n"
    by (metis assms(1) assms(2) perm_comp_assoc perm_comp_perm_id_1 perm_comp_perm_inv1 perm_dom_perm_comp perm_dom_perm_inv)
qed (simp_all add: assms)

subsection \<open>Action on collections (lists, sets, finite sets)\<close>

definition perm_fun_pair :: "perm \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat" where
  "perm_fun_pair p x = (perm_fun p (fst x), perm_fun p (snd x))"

lemma perm_fun_pair [simp]:
  shows "perm_fun_pair p (x, y) = (perm_fun p x, perm_fun p y)"
  unfolding perm_fun_pair_def
  by auto

definition perm_fun_list_f :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list" where
  "perm_fun_list_f p xs = map p xs"

definition perm_fun_list :: "perm \<Rightarrow> nat list \<Rightarrow> nat list" where
  "perm_fun_list p xs = map (perm_fun p) xs"

definition perm_fun_set_f :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> nat set" where
  "perm_fun_set_f p S = p ` S"

definition perm_fun_set :: "perm \<Rightarrow> nat set \<Rightarrow> nat set" where
  "perm_fun_set p S = (perm_fun p) ` S"

definition perm_fun_fset_f :: "(nat \<Rightarrow> nat) \<Rightarrow> nat fset \<Rightarrow> nat fset" where
  "perm_fun_fset_f p S = p |`| S"

definition perm_fun_fset :: "perm \<Rightarrow> nat fset \<Rightarrow> nat fset" where
  "perm_fun_fset p S = (perm_fun p) |`| S"

lemma perm_fun_list_Nil [simp]:
  shows "perm_fun_list p [] = []"
  by (simp add: perm_fun_list_def)

lemma perm_fun_list_Cons [simp]:
  shows "perm_fun_list p (x # xs) = (perm_fun p x) # perm_fun_list p xs"
  by (simp add: perm_fun_list_def)

lemma perm_fun_set_Empty [simp]:
  shows "perm_fun_set p {} = {}"
  by (simp add: perm_fun_set_def)

lemma perm_fun_fset_Empty [simp]:
  shows "perm_fun_fset p {||} = {||}"
  by (simp add: perm_fun_fset_def)

lemma perm_fun_pair_perm_id [simp]:
  assumes "x < n" "y < n"
  shows "perm_fun_pair (perm_id n) (x, y) = (x, y)"
  using assms
  by simp

lemma perm_fun_list_perm_id [simp]:
  assumes "set l \<subseteq> {0..<n}"
  shows "perm_fun_list (perm_id n) l = l"
  using assms
  unfolding perm_fun_list_def
  by (induction l, auto)

lemma perm_fun_set_perm_id [simp]:
  assumes "S \<subseteq> {0..<n}"
  shows "perm_fun_set (perm_id n) S = S"
  using assms
  unfolding perm_fun_set_def
  by force

lemma perm_fun_pair_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" "x < n" "y < n"
  shows "perm_fun_pair (perm_comp p1 p2) (x, y) = 
         perm_fun_pair p1 (perm_fun_pair p2 (x, y))"
  using assms
  by simp

lemma perm_fun_list_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" "set l \<subseteq> {0..<n}"
  shows "perm_fun_list (perm_comp p1 p2) l = perm_fun_list p1 (perm_fun_list p2 l)"
  using assms
  unfolding perm_fun_list_def
  by (induction l) auto

lemma perm_fun_set_perm_comp [simp]:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" "S \<subseteq> {0..<n}"
  shows "perm_fun_set (perm_comp p1 p2) S = perm_fun_set p1 (perm_fun_set p2 S)"
  using assms
  unfolding perm_fun_set_def
  by force

lemma perm_inv_perm_list [simp]: 
  assumes "perm_dom p = n"
  shows "perm_fun_list (perm_inv p) [0..<n] = perm_list (perm_inv p)"
  using assms
  unfolding perm_fun_list_def
  by transfer (auto simp add: perm_fun'_def perm_inv'_def)

lemma perm_fun_list_perm_inv [simp]:
  assumes "perm_dom p = n" "set xs \<subseteq> {0..<n}"
  shows "perm_fun_list (perm_inv p) (perm_fun_list p xs) = xs"
  using assms
  by (metis perm_comp_perm_inv1 perm_dom_perm_inv perm_fun_list_perm_comp perm_fun_list_perm_id)

end