theory McKayPiperno
imports GraphIsomorphism
        More_List_Lexord Option_Lexord
       "HOL-Library.FSet" "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
       "HOL-Library.Word"
begin

section \<open>Isomorphism checking\<close>

(* list of individualized vertices from leaves towards root *)
type_synonym vertex_list = "nat list" 

definition is_vertex_list :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "is_vertex_list G \<nu> \<equiv> distinct \<nu> \<and> set \<nu> \<subseteq> {0..<num_vertices G}"

lemma is_vertex_list_empty [simp]:
  shows "is_vertex_list G []"
  by (simp add: is_vertex_list_def)

lemma is_vertex_list_cons:
 assumes "is_vertex_list G (v # \<nu>)"
 shows "is_vertex_list G \<nu>" "v \<notin> set \<nu>" "v < num_vertices G"
 using assms
 by (auto simp add: is_vertex_list_def)

lemma is_vertex_list_cons_I:
 assumes "is_vertex_list G \<nu>" "v < num_vertices G" "v \<notin> set \<nu>"
 shows "is_vertex_list G (v # \<nu>)"
 using assms
 by (simp add: is_vertex_list_def)

lemma is_vertex_list_rev [simp]:
  assumes "is_vertex_list G \<nu>"
  shows "is_vertex_list G (rev \<nu>)"
  using assms
  by (simp add: is_vertex_list_def)

lemma is_vertex_list_perm [simp]:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G \<nu>" 
  shows "is_vertex_list (perm_graph p G) (perm_fun_list p \<nu>)"
proof-
  have "distinct (map (perm_fun p) \<nu>)"
    using assms is_perm_fun[of p]
    by (auto simp add: distinct_map is_vertex_list_def is_perm_fun_def bij_betw_def inj_on_def)
  then show ?thesis
    using assms
    unfolding is_vertex_list_def perm_fun_list_def
    by auto
qed  

locale refinement_function =
  fixes \<R> :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> coloring"
  assumes \<R>_finer [simp]: 
    "\<And> \<nu> G. \<lbrakk>is_vertex_list G \<nu>\<rbrakk> \<Longrightarrow> 
               finer (\<R> G \<nu>) (colors G)"
  assumes \<R>_cells [simp]:
    "\<And> \<nu> G. \<lbrakk>is_vertex_list G \<nu>; v \<in> set \<nu>\<rbrakk> \<Longrightarrow> 
               {v} \<in> set (cells (\<R> G \<nu>))"
  assumes \<R>_perm [simp]:
    "\<And> \<nu> G p. \<lbrakk>is_vertex_list G \<nu>; 
               perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow> 
                   \<R> (perm_graph p G) (perm_fun_list p \<nu>) = 
                   perm_coloring p (\<R> G \<nu>)"
begin

lemma \<R>_length:
  assumes "is_vertex_list G \<nu>"
  shows "length (\<R> G \<nu>) = length (colors G)"
  using assms \<R>_finer finer_length 
  by presburger

lemma \<R>_length' [simp]:
  assumes "is_vertex_list G \<nu>"
  shows "length (\<R> G \<nu>) = num_vertices G"
  using assms
  by (simp add: \<R>_length) 

lemma num_colors_\<R>_geq:
  assumes "is_vertex_list G \<nu>"
  shows "Coloring.num_colors (\<R> G \<nu>) \<ge> List.length \<nu>"
proof-
  let ?f = "\<lambda> (v::vertex). {v}"
  have "card (set (cells (\<R> G \<nu>))) \<ge> card (set \<nu>)"
  proof (rule card_inj_on_le)
    show "inj_on ?f (set \<nu>)"
      by simp
  next
    show "finite (set (cells (\<R> G \<nu>)))"
      by simp
  next
    show "(\<lambda>v. {v}) ` set \<nu> \<subseteq> set (cells (\<R> G \<nu>))"
      using \<R>_cells[OF assms]
      by auto
  qed
  then show ?thesis
    by (metis assms card_length distinct_card is_vertex_list_def le_trans length_cells)
qed  

lemma \<R>_perm_perm [simp]:
  assumes "is_vertex_list G \<nu>" "perm_dom p = num_vertices G"  "vertex G v"
  shows "Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) (perm_fun p v) = 
         Coloring.color_fun (\<R> G \<nu>) v"
proof (subst \<R>_perm)
  show "Coloring.color_fun (perm_coloring p (\<R> G \<nu>)) (perm_fun p v) = 
        Coloring.color_fun (\<R> G \<nu>) v"
    using assms
    using \<R>_length length_colors_num_vertices perm_coloring_perm_fun 
    by presburger
qed (simp_all add: assms)

lemma \<R>_perm_perm_image [simp]:
  assumes "is_vertex_list G \<nu>" "perm_dom p = num_vertices G"
  shows "(Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) ` {0..<num_vertices G} = 
         (Coloring.color_fun (\<R> G \<nu>)) ` {0..<num_vertices G})" (is "?lhs = ?rhs")
proof safe
  fix x
  assume "x \<in> {0..<num_vertices G}"
  then obtain x' where "x' \<in> {0..<num_vertices G}" "perm_fun p x' = x"
    by (metis assms(2) atLeastLessThan_iff bot_nat_0.extremum perm_fun_perm_inv1 perm_fun_perm_inv_range)
  then show "Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) x \<in> Coloring.color_fun (\<R> G \<nu>) ` {0..<num_vertices G}"
    using assms
    by auto
next
  fix x
  assume "x \<in> {0..<num_vertices G}"
  then have "perm_fun p x \<in> {0..<num_vertices G}"
    by (simp add: assms(2)) 
  then have "Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) (perm_fun p x) \<in> Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) ` {0..<num_vertices G}"
    by simp
  then show "Coloring.color_fun (\<R> G \<nu>) x \<in> Coloring.color_fun (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) ` {0..<num_vertices G}"
    using assms `x \<in> {0..<num_vertices G}`
    by auto
qed

lemma \<R>_perm_length [simp]:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G \<nu>"
  shows "Coloring.length (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) = 
         Coloring.length (\<R> G \<nu>)"
  using assms
  by auto

lemma \<R>_perm_colors [simp]:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G \<nu>"
  shows "Coloring.colors (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) = 
         Coloring.colors (\<R> G \<nu>)"
  using assms all_colors_list
  by (subst Coloring.all_colors_list)+
     (metis (full_types) \<R>_perm_perm_image all_colors atLeastLessThan_upt distinct_remdups list.set_map \<R>_length' \<R>_perm_length sorted_distinct_set_unique sorted_remdups sorted_sort)
  
lemma \<R>_perm_num_colors [simp]:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G \<nu>"
  shows "Coloring.num_colors (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) = 
         Coloring.num_colors (\<R> G \<nu>)"
  using assms
  by (metis Coloring.colors_def \<R>_perm_colors length_cells length_map map_nth)

lemma \<R>_perm_discrete_iff [simp]:
  assumes "perm_dom p = num_vertices G" "is_vertex_list G \<nu>"
  shows "discrete (\<R> (perm_graph p G) (perm_fun_list p \<nu>)) \<longleftrightarrow>
         discrete (\<R> G \<nu>)"
  using assms
  unfolding discrete_def
  by simp

text \<open> Permutation given by a discrete coloring in a tree leaf \<close>

definition leaf_perm :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> perm" where 
  "leaf_perm G \<nu> = discrete_coloring_perm (\<R> G \<nu>)"

lemma leaf_perm_perm_dom [simp]:
  assumes "discrete (\<R> G \<nu>)" "is_vertex_list G \<nu>"
  shows "perm_dom (leaf_perm G \<nu>) = num_vertices G"
  using assms
  unfolding leaf_perm_def
  by simp

lemma leaf_perm_perm_fun [simp]:
  assumes "discrete (\<R> G \<nu>)" "is_vertex_list G \<nu>" "vertex G v"
  shows "perm_fun (leaf_perm G \<nu>) v = Coloring.color_fun (\<R> G \<nu>) v"
  using assms
  unfolding leaf_perm_def
  by simp

lemma leaf_perm_perm [simp]:
  assumes "discrete (\<R> G \<nu>)" "is_vertex_list G \<nu>" "vertex G v"
  assumes "perm_dom p = num_vertices G" 
  shows "perm_fun (leaf_perm (perm_graph p G) (perm_fun_list p \<nu>)) (perm_fun p v) = 
         perm_fun (leaf_perm G \<nu>) v"
  using assms
  by (simp del: \<R>_perm)

end

locale target_cell_selector = refinement_function + 
  fixes \<T> :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> nat fset"
  assumes \<T>_discrete: 
    "\<And> \<nu> G. \<lbrakk>is_vertex_list G \<nu>; discrete (\<R> G \<nu>)\<rbrakk> \<Longrightarrow> 
             \<T> G \<nu> = {||}"
  assumes \<T>_non_discrete:
    "\<And> \<nu> G. \<lbrakk>is_vertex_list G \<nu>; \<not> discrete (\<R> G \<nu>)\<rbrakk> \<Longrightarrow> 
               fset (\<T> G \<nu>) \<in> set (cells (\<R> G \<nu>)) \<and> 
               fcard (\<T> G \<nu>) > 1"
  assumes \<T>_perm:
    "\<And> \<nu> G p. \<lbrakk>is_vertex_list G \<nu>; 
               perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow> 
               \<T> (perm_graph p G) (perm_fun_list p \<nu>) = perm_fun_fset p (\<T> G \<nu>)"
begin

lemma is_vertex_list_T_extend:  
  assumes "is_vertex_list G \<nu>" "v' \<in> fset (\<T> G \<nu>)"
  shows "is_vertex_list G (v' # \<nu>)"
proof-
  have "vertex G v'"
  proof-
    have "\<not> discrete (\<R> G \<nu>)"
      using \<T>_discrete[OF assms(1)] assms(2)
      by auto
    then have "fset (\<T> G \<nu>) \<in> set (cells (\<R> G \<nu>))"
      using \<T>_non_discrete[OF assms(1)]
      by auto
    then obtain c where "c \<in> set (Coloring.colors (\<R> G \<nu>))"
                        "v' \<in> cell (\<R> G \<nu>) c"
      using \<open>v' \<in> fset (\<T> G \<nu>)\<close>
      unfolding cells_def
      by auto
    thus ?thesis
      unfolding cell_def
      by (simp add: \<R>_length assms(1))
  qed

  moreover

  have "v' \<notin> set \<nu>"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "{v'} \<in> set (cells (\<R> G \<nu>))"
      using \<R>_cells[OF assms(1)]
      by simp
    have "\<not> discrete (\<R> G \<nu>)"
      using \<T>_discrete[OF assms(1)] assms(2)
      by auto
    then have "fset (\<T> G \<nu>) \<in> set (cells (\<R> G \<nu>))" 
              "fcard (\<T> G \<nu>) > 1"
      using \<T>_non_discrete[OF assms(1)]
      by auto
    have "{v'} = fset (\<T> G \<nu>)"
      using cells_disjunct
      using \<open>fset (\<T> G \<nu>) \<in> set (cells (\<R> G \<nu>))\<close> 
            \<open>{v'} \<in> set (cells (\<R> G \<nu>))\<close> assms(2)
      by (smt (verit, ccfv_SIG) cells_ok cells_ok_def disjoint_insert(2) in_set_conv_nth)
    then show False
      using `fcard (\<T> G \<nu>) > 1`
      by (metis One_nat_def card.empty card.insert empty_iff fcard.rep_eq finite.intros(1) neq_iff)
  qed

  ultimately

  show ?thesis
    using \<open>is_vertex_list G \<nu>\<close>
    unfolding is_vertex_list_def
    by auto
qed

text \<open>Data structure for representing search tree\<close>
datatype Tree = Node "vertex_list" "Tree fset"

primrec node_vertex_list where
  "node_vertex_list (Node \<nu> ns) = \<nu>"

primrec nodes :: "Tree \<Rightarrow> vertex_list set" where
  "nodes (Node \<nu> ns) = {\<nu>} \<union> (\<Union> (fset (nodes |`| ns)))"

primrec leaves :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list set" where
  "leaves G (Node \<nu> ns) = 
       (if \<T> G \<nu> = {||} then
           {\<nu>}
        else
           (\<Union> (fset (leaves G |`| ns))))"

lemma leaves_are_nodes:
  shows "leaves G T \<subseteq> nodes T"
  by (induction T) auto

lemma leaf_is_node [simp]:
  assumes "\<nu> \<in> leaves G T"
  shows "\<nu> \<in> nodes T"
  using assms
  by (meson leaves_are_nodes subset_eq)

text \<open>Function that creates the search tree from the given graph\<close>
function (domintros) expand_tree :: "colored_graph \<Rightarrow> nat list \<Rightarrow> Tree" where
  "expand_tree G \<nu> = 
     (if \<T> G \<nu> = {||} then 
         Node \<nu> {||} 
      else
         Node \<nu> ((\<lambda> v. expand_tree G (v # \<nu>)) |`| (\<T> G \<nu>)))"
  by pat_completeness auto

lemma expand_tree_dom:
  assumes "is_vertex_list G \<nu>"
  shows "expand_tree_dom (G, \<nu>)"
proof-
  let ?n = "num_vertices G - List.length \<nu>"
  show ?thesis
    using assms
  proof (induct ?n arbitrary: \<nu>)
    case 0
    have "discrete (\<R> G \<nu>)"
    proof-
      have "length (\<R> G \<nu>) = num_vertices G"
        using `is_vertex_list G \<nu>`
        by simp
      then have "length (\<R> G \<nu>) = List.length \<nu>"
        using 0
        unfolding is_vertex_list_def
        by (metis diff_diff_cancel distinct_card minus_nat.diff_0 subset_eq_atLeast0_lessThan_card)
      then show ?thesis
        using 0
        unfolding discrete_def
        by (metis Coloring.colors_def all_colors atLeastLessThan_upt card_atLeastLessThan card_length color_fun.rep_eq length.rep_eq linorder_not_less map_nth minus_nat.diff_0 num_colors_\<R>_geq order.order_iff_strict)
    qed
    show ?case
    proof (rule expand_tree.domintros)
      fix z
      assume "z \<in> fset (\<T> G \<nu>)"
      then show False 
        using \<T>_discrete \<open>discrete (\<R> G \<nu>)\<close> 0 by force
    qed
  next
    case (Suc n)
    show ?case
    proof (rule expand_tree.domintros)
      fix z
      assume "z \<in> fset (\<T> G \<nu>)" "\<not> expand_tree_dom (G, z # \<nu>)"
      have "expand_tree_dom (G, z # \<nu>)"
      proof (rule Suc(1))
        show "is_vertex_list G (z # \<nu>)"
          by (simp add: Suc.prems \<open>z \<in> fset (\<T> G \<nu>)\<close> is_vertex_list_T_extend)
      next
        show "n = num_vertices G - List.length (z # \<nu>)"
          using Suc.hyps(2)
          by force
      qed
      then show False
        using `\<not> expand_tree_dom (G, z # \<nu>)`
        by simp
    qed
  qed
qed

lemmas expand_tree_simps = expand_tree.psimps[OF expand_tree_dom]
lemmas expand_tree_induct = expand_tree.pinduct[OF expand_tree_dom]

definition tree :: "colored_graph \<Rightarrow> Tree" where
  "tree G = expand_tree G []"


lemma nodes_expand_tree_root [simp]:
  assumes "is_vertex_list G \<nu>"
  shows "\<nu> \<in> nodes (expand_tree G \<nu>)"
  by (simp add: expand_tree_simps[OF assms])

lemma empty_node [simp]:
  shows "[] \<in> nodes (tree G)"
  by (simp add: tree_def)

text \<open>Tree contains only vertex lists\<close>
lemma nodes_expand_tree_is_vertex_list:
  assumes "is_vertex_list G \<nu>" "\<nu>' \<in> nodes (expand_tree G \<nu>)"
  shows "is_vertex_list G \<nu>'"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using expand_tree_simps[of G \<nu>] 2
      by simp
  next
    case False
    then show ?thesis
      using expand_tree_simps[of G \<nu>] 2 is_vertex_list_T_extend
      by auto
  qed
qed

lemma nodes_is_vertex_list [simp]:
  assumes "\<nu> \<in> nodes (tree G)"
  shows "is_vertex_list G \<nu>"
  using assms nodes_expand_tree_is_vertex_list[of G "[]" \<nu>] 
  unfolding tree_def is_vertex_list_def
  by simp

lemma leaves_expand_tree_suffix:
  assumes "is_vertex_list G \<nu>" "\<nu>' \<in> leaves G (expand_tree G \<nu>)"
  shows "\<exists> k. k \<le> List.length \<nu>' \<and> drop k \<nu>' = \<nu>"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2 expand_tree_simps[of G \<nu>]
      by auto
  next
    case False
    then obtain n where "n \<in> fset (\<T> G \<nu>)" "\<nu>' \<in> leaves G (expand_tree G (n # \<nu>))"
      using 2 expand_tree_simps[of G \<nu>]
      by auto
    then obtain k where "drop k \<nu>' = n # \<nu>"
      using "2.IH" "2.prems"(1) False is_vertex_list_T_extend by blast
    then show ?thesis
      by (metis Cons_nth_drop_Suc drop_all list.discI list.inject not_le not_less_eq_eq)
  qed
qed

lemma leaves_expand_tree_suffix_not_root:
  assumes "is_vertex_list G \<nu>"  "\<nu>' \<in> leaves G (expand_tree G \<nu>)"  "\<nu>' \<noteq> \<nu>"
  shows "\<exists> k. k > 0 \<and> k \<le> List.length \<nu>' \<and> drop k \<nu>' = \<nu>"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2 expand_tree_simps[of G \<nu>]
      by simp
  next
    case False
    then obtain n where n: "n \<in> fset (\<T> G \<nu>)" "\<nu>' \<in> leaves G (expand_tree G (n # \<nu>))"
      using 2 expand_tree_simps[of G \<nu>]
      by auto
    show ?thesis
    proof (cases "\<nu>' = n # \<nu>")
      case True
      thus ?thesis
        by auto
    next
      case False
      then obtain k where "k > 0" "drop k \<nu>' = n # \<nu>"
        using \<open>\<T> G \<nu> \<noteq> {||}\<close> n
        by (meson "2.IH" "2.prems"(1) is_vertex_list_T_extend)
      then show ?thesis
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) drop_0 leaves_expand_tree_suffix zero_less_iff_neq_zero)
    qed
  qed            
qed

lemma leaves_expand_tree_finite [simp]:
  assumes "is_vertex_list G \<nu>"
  shows "finite (leaves G (expand_tree G \<nu>))"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2 expand_tree_simps[of G \<nu>]
      by simp
  next
    case False
    then show ?thesis
      using expand_tree_simps[of G \<nu>]
      using 2 is_vertex_list_T_extend[of G \<nu>]
      by auto
  qed
qed

lemma leaves_finite [simp]:
  shows "finite (leaves G (tree G))"
  unfolding tree_def
  by simp

lemma leaves_expand_tree_not_empty [simp]:
  assumes "is_vertex_list G \<nu>"
  shows "leaves G (expand_tree G \<nu>) \<noteq> {}"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2
      by (simp add: expand_tree_simps)
  next
    case False
    then show ?thesis
      using expand_tree_simps[of G \<nu>]
      using 2 local.is_vertex_list_T_extend[of G \<nu>]
      by (auto simp add: fmember.rep_eq)
  qed
qed

lemma leaves_not_empty [simp]:
  shows "leaves G (tree G) \<noteq> {}"
  by (simp add: tree_def)

lemma leaves_of_leaf:
  assumes "is_vertex_list G \<nu>0" "\<nu> \<in> leaves G (expand_tree G \<nu>0)" "\<nu>' \<in> leaves G (expand_tree G \<nu>)" 
  shows "\<nu>' = \<nu>"
  using assms
proof (induction G \<nu>0 rule: expand_tree_induct)
  show "is_vertex_list G \<nu>0" 
    by fact
next
  case (2 G \<nu>0)
  show ?case
  proof (cases "\<T> G \<nu>0 = {||}")
    case True
    thus ?thesis
      using 2(2-) expand_tree_simps[of G \<nu>0]
      by simp
  next
    case False
    have "\<nu> \<in> \<Union> (fset (leaves G |`| (\<lambda>v. expand_tree G (v # \<nu>0)) |`| \<T> G \<nu>0))"
      by (metis "2.prems"(1) "2.prems"(2) False expand_tree_simps leaves.simps)
    then obtain A where "\<nu> \<in> A" "A |\<in>| leaves G |`| (\<lambda>v. expand_tree G (v # \<nu>0)) |`| \<T> G \<nu>0"
      by (meson Union_iff notin_fset)
    then obtain z where "z \<in> fset (\<T> G \<nu>0)" "\<nu> \<in> leaves G (expand_tree G (z # \<nu>0))"
      using notin_fset by fastforce
    then show ?thesis
      using "2.IH" "2.prems"(1) "2.prems"(3) False is_vertex_list_T_extend by blast
  qed
qed

lemma leaves_of_node:
  assumes "is_vertex_list G \<nu>0" "\<nu>1 \<in> nodes (expand_tree G \<nu>0)" "\<nu>1' \<in> leaves G (expand_tree G \<nu>1)"
  shows "\<nu>1' \<in> leaves G (expand_tree G \<nu>0)"
  using assms
proof (induction G \<nu>0 rule: expand_tree_induct)
  show "is_vertex_list G \<nu>0"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2
      by (simp add: expand_tree_simps)
  next
    case False
    show ?thesis
    proof (cases "\<nu> = \<nu>1")
      case True
      then show ?thesis
        by (simp add: "2.prems"(3))
    next
      case False
      then obtain z where "z \<in> fset (\<T> G \<nu>)" "\<nu>1 \<in> nodes (expand_tree G (z # \<nu>))" "is_vertex_list G (z # \<nu>)"
        using `\<T> G \<nu> \<noteq> {||}` "2.prems"(2) expand_tree_simps[OF `is_vertex_list G \<nu>`] 
        using "2.prems"(1) is_vertex_list_T_extend 
        by auto
      then have "\<nu>1' \<in> leaves G (expand_tree G (z # \<nu>))"
        using `\<T> G \<nu> \<noteq> {||}` 2
        by auto
      then show ?thesis
        using False expand_tree_simps[OF `is_vertex_list G \<nu>`] `z \<in> fset (\<T> G \<nu>)`
        by auto
    qed
  qed
qed

lemma leaves_expand_tree_iff_discrete_nodes_expand_tree:
  assumes "is_vertex_list G \<nu>" 
  shows "\<nu>' \<in> leaves G (expand_tree G \<nu>) \<longleftrightarrow> 
         \<nu>' \<in> nodes (expand_tree G \<nu>) \<and> discrete (\<R> G \<nu>')"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    thus ?thesis
      using \<T>_non_discrete[of G \<nu>] 2 expand_tree_simps[of G \<nu>]
      by (auto simp add: fcard_fempty gr_implies_not0)
  next
    case False
    have *: "\<forall> z \<in> fset (\<T> G \<nu>). is_vertex_list G (z # \<nu>)"
      by (metis "2.prems" is_vertex_list_T_extend)
    let ?f = "(\<lambda>v. expand_tree G (v # \<nu>))"
    have "\<nu>' \<in> leaves G (Node \<nu> (?f |`| \<T> G \<nu>)) \<longleftrightarrow>
         (\<nu>' \<in> nodes (Node \<nu> (?f |`| \<T> G \<nu>)) \<and>
         discrete (\<R> G \<nu>'))"
      using * 2(2)[OF False] 2 False \<T>_discrete
      by auto
    then show ?thesis
      using False 2
      by (simp add: expand_tree_simps[of G \<nu>])
  qed
qed

lemma leaves_iff_discrete_nodes:
  shows "\<nu>' \<in> leaves G (tree G) \<longleftrightarrow> 
         \<nu>' \<in> nodes (tree G) \<and> discrete (\<R> G \<nu>')"
  by (simp add: leaves_expand_tree_iff_discrete_nodes_expand_tree tree_def)

lemma leaves_discrete [simp]:
  assumes "\<nu>' \<in> leaves G (tree G)"
  shows "discrete (\<R> G \<nu>')"
  using assms leaves_iff_discrete_nodes
  by blast

lemma leaf_in_some_expand_tree:
  assumes "\<nu> \<in> nodes (tree G)" "fset (\<T> G \<nu>) \<noteq> {}"
          "\<nu>' \<in> leaves G (expand_tree G \<nu>)" 
  shows "\<exists> v0 \<in> fset (\<T> G \<nu>). \<nu>' \<in> leaves G (expand_tree G (v0 # \<nu>))"
  using assms leaves.simps[of G \<nu> "(\<lambda>v. expand_tree G (v # \<nu>)) |`| \<T> G \<nu>"] expand_tree_simps[of G \<nu>]
  by (auto split: if_split_asm)

lemma nodes_of_node:
  assumes "is_vertex_list G \<nu>0"  "\<nu>1 \<in> nodes (expand_tree G \<nu>0)" "\<nu>1' \<in> nodes (expand_tree G \<nu>1)"
  shows "\<nu>1' \<in> nodes (expand_tree G \<nu>0)"
  using assms
proof (induction G \<nu>0 rule: expand_tree_induct)
  show "is_vertex_list G \<nu>0"
    by fact
next
  case (2 G \<nu>)
  show ?case
  proof (cases "\<T> G \<nu> = {||}")
    case True
    then show ?thesis
      using 2  expand_tree_simps[of G \<nu>]
      by simp
  next
    case False
    then show ?thesis 
      using expand_tree_simps[of G \<nu>]
      using "2.IH" "2.prems"(1) "2.prems"(2) "2.prems"(3) is_vertex_list_T_extend by force
  qed
qed

lemma nodes_extend:
  assumes "\<nu> \<in> nodes (tree G)" "v \<in> fset (\<T> G \<nu>)"
  shows "(v # \<nu>) \<in> nodes (tree G)"
proof-
  have "(v # \<nu>) \<in> nodes (expand_tree G \<nu>)"
    using assms expand_tree_simps[of G \<nu>] nodes_expand_tree_root nodes_is_vertex_list is_vertex_list_T_extend
    by (force split: if_split_asm)
  then show ?thesis
    using assms(1) nodes_of_node nodes_is_vertex_list is_vertex_list_empty
    unfolding tree_def
    by blast
qed

text \<open>Permutation of a search tree\<close>

primrec perm_tree :: "perm \<Rightarrow> Tree \<Rightarrow> Tree" where
  "perm_tree p (Node \<nu> ns) = 
   Node (perm_fun_list p \<nu>) ((perm_tree p) |`| ns)"

lemma perm_tree_nodes [simp]:
  assumes "\<nu> \<in> nodes T"
  shows "perm_fun_list p \<nu> \<in> nodes (perm_tree p T)"
  using assms
  by (induction T) auto


text \<open>Lemma 1 - induction\<close>
lemma perm_tree_expand_tree [simp]:
  assumes "is_vertex_list G \<nu>" "perm_dom p = num_vertices G"
  shows "expand_tree (perm_graph p G) (perm_fun_list p \<nu>) =
         perm_tree p (expand_tree G \<nu>)"
  using assms
proof (induction G \<nu> rule: expand_tree_induct)
  show "is_vertex_list G \<nu>"
    by fact
next
  case (2 G \<nu>)

  let ?f1 = "\<lambda>v. expand_tree (perm_graph p G) (v # perm_fun_list p \<nu>)"
  let ?f1' = "\<lambda>v. expand_tree (perm_graph p G) (perm_fun_list p (v # \<nu>))"

  have "(?f1 |`| \<T> (perm_graph p G) (perm_fun_list p \<nu>)) = 
        ?f1 |`| perm_fun p |`| \<T> G \<nu>"
    using 2(3-4) \<T>_perm
    by (simp add: perm_fun_fset_def)
  also have "... = ?f1' |`| \<T> G \<nu>"
    by (auto simp add: perm_fun_list_def)
  also have "... = (\<lambda> v. perm_tree p (expand_tree G (v # \<nu>))) |`| (\<T> G \<nu>)"
    using 2
    by (metis (no_types, lifting) bot_fset.rep_eq equals0D fset.map_cong0 is_vertex_list_T_extend)
  also have "... = perm_tree p |`| (\<lambda>v. expand_tree G (v # \<nu>)) |`| \<T> G \<nu>"
    by auto
  finally show ?case
    using 2
    by (auto simp add: expand_tree_simps[of G \<nu>] expand_tree_simps[of "perm_graph p G" "perm_fun_list p \<nu>"])
qed

text \<open>Lemma 1\<close>
lemma perm_tree_tree [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "tree (perm_graph p G) = perm_tree p (tree G)"
  unfolding tree_def
  using assms perm_tree_expand_tree[of G "[]" ]
  by (simp add: perm_fun_list_def)

lemma perm_tree_leaves [simp]:
  assumes "\<forall> \<nu> \<in> nodes T. is_vertex_list G \<nu>" "perm_dom p = num_vertices G" 
  assumes "\<nu> \<in> leaves G T" 
  shows "perm_fun_list p \<nu> \<in> leaves (perm_graph p G) (perm_tree p T)"
  using assms
proof (induction T)
  case (Node \<nu>' ns)
  show ?case
  proof (cases "\<T> G \<nu>' = {||}")
    case True
    then have "\<T> (perm_graph p G) (perm_fun_list p \<nu>') = {||}"
      using \<T>_perm[of G \<nu>' p] Node.prems assms
      by simp
    then show ?thesis
      using True
      using Node.prems
      by auto
  next
    case False
    then have *: "\<T> (perm_graph p G) (perm_fun_list p \<nu>') \<noteq> {||}"
      using \<T>_perm[of G \<nu>' p] Node.prems assms
      by (simp add: perm_fun_fset_def)
    obtain n where "n \<in> fset ns" "\<nu> \<in> leaves G n"
      using False Node.prems
      by auto
    then show ?thesis
      using * False Node(1)[of n] Node.prems      
      by auto
  qed
qed

lemma perm_graph_expand_tree_leaves [simp]:
  assumes "is_vertex_list G \<nu>0" "perm_dom p = num_vertices G"
  assumes "\<nu> \<in> leaves G (expand_tree G \<nu>0)"
  shows "perm_fun_list p \<nu> \<in> leaves (perm_graph p G) (expand_tree (perm_graph p G) (perm_fun_list p \<nu>0))"
  using assms
  by (metis perm_tree_expand_tree perm_tree_leaves nodes_expand_tree_is_vertex_list) 

lemma perm_graph_tree_leaves [simp]:
  assumes "perm_dom p = num_vertices G" 
  assumes "\<nu> \<in> leaves G (tree G)"
  shows "perm_fun_list p \<nu> \<in> leaves (perm_graph p G) (tree (perm_graph p G))"
  using assms
  by simp

text \<open>Corollary 2(b)\<close>
lemma expand_tree_perm_automorphism:
  assumes "is_vertex_list G \<nu>" "is_automorphism G p" 
  shows "expand_tree G (perm_fun_list p \<nu>) = perm_tree p (expand_tree G \<nu>)" 
  using assms is_automorphism_def is_isomorphism_def
  by (metis perm_tree_expand_tree)

text \<open>Special case for the root\<close>
lemma perm_tree_automorphism:
  assumes "is_automorphism G p" 
  shows "perm_tree p (tree G) = tree G"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by (metis perm_tree_tree)

text \<open>Corollary 2(a)\<close>
lemma perm_node_in_tree_automorphism:
  assumes "is_automorphism G p" "\<nu> \<in> nodes (tree G)"
  shows "perm_fun_list p \<nu> \<in> nodes (tree G)"
  using assms
  by (metis perm_tree_automorphism perm_tree_nodes)

lemma perm_node_in_tree_leaves_automorphism:
  assumes "is_automorphism G p" "\<nu> \<in> leaves G (tree G)"
  shows "perm_fun_list p \<nu> \<in> leaves G (tree G)"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by (metis perm_graph_tree_leaves)

lemma perm_node_in_expand_tree_leaves_automorphism:
  assumes "is_vertex_list G \<nu>0" 
          "is_automorphism G p" "\<nu> \<in> leaves G (expand_tree G \<nu>0)" 
  shows "perm_fun_list p \<nu> \<in> leaves G (expand_tree G (perm_fun_list p \<nu>0))"
  using assms is_automorphism_def is_isomorphism_def perm_graph_expand_tree_leaves
  by smt


lemma leaf_perm_perm_perm_edges [simp]:
  assumes "perm_dom p = num_vertices G" 
  assumes "\<nu> \<in> leaves G (tree G)"
  shows "perm_edges (leaf_perm (perm_graph p G) (perm_fun_list p \<nu>)) (edges (perm_graph p G)) =
         perm_edges (leaf_perm G \<nu>) (edges G)"
proof-
  have "\<forall> (x, y) \<in> edges G.
             perm_fun_pair (leaf_perm (perm_graph p G) (perm_fun_list p \<nu>)) (perm_fun p x, perm_fun p y) = 
             perm_fun_pair (leaf_perm G \<nu>) (x, y)"
    using assms
    unfolding perm_fun_pair_def
    using leaf_perm_perm
    by force 
  then show ?thesis
    unfolding perm_edges_def
    by (smt (verit) assms(1) case_prodE edges_perm_graph image_cong image_image perm_edges_def perm_fun_pair)
qed

lemma pointwise_stabilizer:
  assumes "is_vertex_list G \<nu>" 
  assumes "is_automorphism G p"
  shows "is_automorphism (recolor G (\<R> G \<nu>)) p \<longleftrightarrow> 
         (\<forall> v \<in> set \<nu>. perm_fun p v = v)"
proof
  assume *: "is_automorphism (recolor G (\<R> G \<nu>)) p"
  show "\<forall> v \<in> set \<nu>. perm_fun p v = v"
  proof
    fix v
    assume "v \<in> set \<nu>"
    obtain \<pi> where \<pi>: "\<pi> = \<R> G \<nu>" by auto
    have "length \<pi> = num_vertices G"
      using \<pi> assms(1)
      by simp

    have "\<forall> v'. vertex G v' \<and> Coloring.color_fun \<pi> v' = Coloring.color_fun \<pi> v \<longrightarrow> v = v'"
    proof-
      have "{v} \<in> set (cells \<pi>)"
        using \<open>v \<in> set \<nu>\<close> \<R>_cells[of G \<nu> v] assms \<pi>
        by auto
      then obtain c where "{v} = cell \<pi> c"
        unfolding cells_def
        by auto
      then show ?thesis
        unfolding cell_def
        by (metis (no_types, lifting) \<R>_length' \<pi> assms(1) mem_Collect_eq singleton_iff)
    qed

    moreover

    have **: "vertex G v \<and> vertex G (perm_fun p v)"
      using \<open>is_vertex_list G \<nu>\<close> \<open>v \<in> set \<nu>\<close>
      unfolding is_vertex_list_def
      by (meson assms(2) atLeastLessThan_iff is_automorphism_def is_isomorphism_def subsetD vertex_perm_fun)

    moreover

    have "Coloring.color_fun \<pi> v = Coloring.color_fun \<pi> (perm_fun p v)"
    proof-
      have "(color_fun (recolor G \<pi>)) (perm_fun p v) = (color_fun (recolor G \<pi>)) v"
        using automorphism_retains_colors[OF *, of v] ** \<pi> `length \<pi> = num_vertices G`
        by auto
      then show ?thesis
        using ** `length \<pi> = num_vertices G`
        by simp
    qed

    ultimately 

    show "perm_fun p v = v"
      by auto
  qed
next
  obtain \<pi> where \<pi>: "\<pi> = \<R> G \<nu>" by auto
  have "length \<pi> = num_vertices G"
    using \<pi> assms(1)
    by simp

  assume "\<forall> v \<in> set \<nu>. perm_fun p v = v"
  then have *: "perm_fun_list p \<nu> = \<nu>"
    by (simp add: map_idI perm_fun_list_def)
  have "perm_graph p (recolor G \<pi>) = recolor G \<pi>" (is "?pG = ?G")
  proof (rule graph_eqI)
    show "num_vertices ?pG = num_vertices ?G"
      using assms `length \<pi> = num_vertices G`
      unfolding is_automorphism_def is_isomorphism_def
      by auto
  next
    show "edges (perm_graph p (recolor G \<pi>)) = edges (recolor G \<pi>)"
      using assms `length \<pi> = num_vertices G` edges_perm_graph[of p G]
      unfolding is_automorphism_def is_isomorphism_def
      by simp
  next
    show "ColoredGraph.colors (perm_graph p (recolor G \<pi>)) = 
          ColoredGraph.colors (recolor G \<pi>)"
    proof-
      have "perm_coloring p \<pi> = \<pi>"
      proof (rule coloring_eqI)
        show "length (perm_coloring p \<pi>) = length \<pi>"
          using \<open>Coloring.length \<pi> = num_vertices G\<close> assms(2) is_automorphism_def is_isomorphism_def 
          by simp
      next
        show "\<forall>v<Coloring.length (perm_coloring p \<pi>). Coloring.color_fun (perm_coloring p \<pi>) v = Coloring.color_fun \<pi> v"
          using assms \<pi> * \<R>_perm
          unfolding is_automorphism_def is_isomorphism_def
          by metis
      qed
      then show ?thesis
        using \<open>Coloring.length \<pi> = num_vertices G\<close> assms(2) is_automorphism_def is_isomorphism_def 
        by simp
    qed
  qed
  then show "is_automorphism (recolor G (\<R> G \<nu>)) p"
    using assms \<pi>
    unfolding is_automorphism_def is_isomorphism_def
    by simp
qed

end

locale node_invariant = target_cell_selector + 
  fixes \<Phi> :: "colored_graph \<Rightarrow> nat list \<Rightarrow> 'a::linorder"
  assumes \<Phi>_mono: 
    "\<And> G \<nu> \<nu>'.
       \<lbrakk>\<nu> \<in> nodes (tree G); \<nu>' \<in> nodes (tree G);
        List.length \<nu> = List.length \<nu>';
        \<Phi> G \<nu> < \<Phi> G \<nu>' \<rbrakk> \<Longrightarrow>
        (\<forall> \<nu>1 \<in> leaves G (expand_tree G \<nu>). 
         \<forall> \<nu>1' \<in> leaves G (expand_tree G \<nu>'). \<Phi> G \<nu>1 < \<Phi> G \<nu>1')"
  assumes \<Phi>_discrete_weak: 
    "\<And> G \<pi> \<pi>' \<nu> \<nu>'.
       \<lbrakk>is_vertex_list G \<nu>; is_vertex_list G \<nu>';
        \<pi> = \<R> G \<nu>; \<pi>' = \<R> G \<nu>';
        discrete \<pi>; discrete \<pi>' \<rbrakk> \<Longrightarrow>
        \<Phi> G \<nu> = \<Phi> G \<nu>' \<longrightarrow> perm_edges (leaf_perm G \<nu>) (edges G) = 
                            perm_edges (leaf_perm G \<nu>') (edges G)"
  assumes \<Phi>_perm:
    "\<And> G \<nu> p. 
       \<lbrakk>\<nu> \<in> nodes (tree G); perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow>
        \<Phi> (perm_graph p G) (perm_fun_list p \<nu>) = \<Phi> G \<nu>" 
begin

lemma \<Phi>_discrete: 
  assumes 
    "is_vertex_list G \<nu>" "is_vertex_list G \<nu>'"
    "\<pi> = \<R> G \<nu>" "\<pi>' = \<R> G \<nu>'"
    "discrete \<pi>" "discrete \<pi>'"
  shows
    "\<Phi> G \<nu> = \<Phi> G \<nu>' \<longrightarrow> perm_graph (leaf_perm G \<nu>) G = 
                         perm_graph (leaf_perm G \<nu>') G"
proof-
  have "perm_graph (leaf_perm G \<nu>) G = perm_graph (leaf_perm G \<nu>') G \<longleftrightarrow>
        perm_edges (leaf_perm G \<nu>) (edges G) = perm_edges (leaf_perm G \<nu>') (edges G)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (metis assms(1-6) edges_perm_graph leaf_perm_perm_dom)
  next
    assume ?rhs
    show ?lhs
    proof-
      let ?p = "perm_coloring (leaf_perm G \<nu>) (colors G)"
      let ?p' = "perm_coloring (leaf_perm G \<nu>') (colors G)"
      have "?p = ?p'"
      proof (rule coloring_eqI)
        show "length ?p = length ?p'"
          using assms
          by simp
        show "\<forall> v < length ?p. Coloring.color_fun ?p v = Coloring.color_fun ?p' v"
          unfolding leaf_perm_def
          using \<C>_\<alpha>_independent[of "\<R> G \<nu>" "colors G" "\<R> G \<nu>'"]
          unfolding \<C>_def discrete_coloring_perm_def
          by (metis \<R>_finer \<R>_length assms(1-6) discrete_coloring_is_permutation length_colors_num_vertices length_perm_coloring perm_dom_make_perm)
      qed          
      thus ?thesis
        using \<open>?rhs\<close> assms colors_perm_graph edges_perm_graph graph_eqI leaf_perm_perm_dom num_vertices_perm_graph
        by presburger
    qed
  qed
  thus ?thesis
    using \<Phi>_discrete_weak[OF assms]
    by simp
qed

definition equivalent_leaves where 
  "equivalent_leaves G \<nu> \<nu>' \<longleftrightarrow> \<Phi> G \<nu> = \<Phi> G \<nu>'" 

text \<open>Lemma 3 in thesis\<close>

lemma only_automorphism:
  assumes "\<nu> \<in> leaves G (tree G)" "\<nu>' \<in> leaves G (tree G)"
          "perm_fun_list p \<nu> = \<nu>'"
          "is_automorphism G p"
          "\<pi> = leaf_perm G \<nu>"
          "\<pi>' = leaf_perm G \<nu>'"
  shows "p = perm_comp (perm_inv \<pi>') \<pi>"
proof-
  let ?n = "num_vertices G"

  have "is_vertex_list G \<nu>" "is_vertex_list G \<nu>'" 
    using assms
    by simp_all

  have "perm_dom p = ?n"
    using assms(4) is_automorphism_def is_isomorphism_def by auto 

  have "is_perm_fun ?n (Coloring.color_fun (\<R> G \<nu>))" 
    using \<open>\<nu> \<in> leaves G (tree G)\<close> \<open>is_vertex_list G \<nu>\<close>
    using discrete_coloring_is_permutation[of "\<R> G \<nu>"]
    by simp    
  have "is_perm_fun ?n (Coloring.color_fun (\<R> G \<nu>'))"    
    using \<open>\<nu>' \<in> leaves G (tree G)\<close> \<open>is_vertex_list G \<nu>'\<close>
    using discrete_coloring_is_permutation[of "\<R> G \<nu>'"]
    by simp

  have "\<pi>' = perm_comp \<pi> (perm_inv p)"
  proof (rule permEqI)
    show "perm_dom \<pi>' = num_vertices G"
      using \<open>is_vertex_list G \<nu>'\<close> assms(6) assms(2)
      by simp
  next
    show "perm_dom (perm_comp \<pi> (perm_inv p)) = num_vertices G"
      using \<open>perm_dom p = num_vertices G\<close> assms(1) assms(5)
      by auto 
  next
    show "\<forall>v. vertex G v \<longrightarrow> perm_fun \<pi>' v = perm_fun (perm_comp \<pi> (perm_inv p)) v"
    proof safe
      fix v    
      assume "vertex G v"
      have "Coloring.color_fun (\<R> G (perm_fun_list p \<nu>)) v = Coloring.color_fun (\<R> G \<nu>) (perm_fun (perm_inv p) v)"
        using \<open>is_vertex_list G \<nu>\<close> \<open>vertex G v\<close> assms(4) 
        by (smt (verit, ccfv_SIG) \<R>_perm_perm is_automorphism_def is_isomorphism_def perm_fun_perm_inv1 perm_fun_perm_inv_range)
      then show "perm_fun \<pi>' v = perm_fun (perm_comp \<pi> (perm_inv p)) v"
        using assms `is_automorphism G p` `vertex G v`
        unfolding is_automorphism_def is_isomorphism_def
        by simp
    qed
  qed
  then have "perm_comp (perm_inv \<pi>') \<pi> = perm_comp (perm_inv (perm_comp \<pi> (perm_inv p))) \<pi>"
    by simp
  also have "... = perm_comp (perm_comp p (perm_inv \<pi>)) \<pi>"
    by (simp add: \<open>is_vertex_list G \<nu>\<close> \<open>perm_dom p = num_vertices G\<close> assms(1) assms(5))
  also have "... = p"
    by (simp add: \<open>is_vertex_list G \<nu>\<close> \<open>perm_dom p = num_vertices G\<close> assms(1) assms(5) perm_comp_assoc)
  finally
  show ?thesis
    by simp
qed

lemma equivalent_leaves:
  assumes "\<nu> \<in> leaves G (tree G)" "\<nu>' \<in> leaves G (tree G)"
          "perm_fun_list p \<nu> = \<nu>'"
          "is_automorphism G p"
  shows "equivalent_leaves G \<nu> \<nu>'"
proof-
  let ?n = "num_vertices G"

  have "\<nu> \<in> nodes (tree G)"
    using assms(1) by auto

  have "perm_dom p = ?n"
    using assms(4) is_automorphism_def is_isomorphism_def by blast

  have "\<Phi> G \<nu> = \<Phi> (perm_graph p G) (perm_fun_list p \<nu>)"
    using \<open>\<nu> \<in> nodes (tree G)\<close> \<open>perm_dom p = ?n\<close> \<Phi>_perm
    by simp
  also have "... = \<Phi> G (perm_fun_list p \<nu>)"
    using assms(4) is_automorphism_def is_isomorphism_def by auto
  also have "... = \<Phi> G \<nu>'"
    using assms
    by simp
  finally
  show ?thesis
    unfolding equivalent_leaves_def
    by simp
qed

theorem automorphisms:
  assumes "\<nu> \<in> leaves G (tree G)"
  shows "automorphisms G = { let \<pi> = leaf_perm G \<nu>;
                                 \<pi>' = leaf_perm G \<nu>'
                              in perm_comp (perm_inv \<pi>') \<pi> | \<nu>'. 
                                               \<nu>' \<in> leaves G (tree G) \<and>
                                               equivalent_leaves G \<nu> \<nu>' }"
    (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix p
    assume "p \<in> automorphisms G"
    let ?\<nu>' = "perm_fun_list p \<nu>"
    have "?\<nu>' \<in> leaves G (tree G)"
      using \<open>p \<in> automorphisms G\<close> assms automorphisms_def
      by (simp add: perm_node_in_tree_leaves_automorphism)
    have "p = perm_comp (perm_inv (leaf_perm G ?\<nu>')) (leaf_perm G \<nu>)"
         "equivalent_leaves G \<nu> ?\<nu>'"
      using only_automorphism[OF assms(1) \<open>?\<nu>' \<in> leaves G (tree G)\<close>]
      using equivalent_leaves[OF assms(1) \<open>?\<nu>' \<in> leaves G (tree G)\<close>]
      using \<open>p \<in> automorphisms G\<close> automorphisms_def by blast+
    then show "p \<in> ?rhs"
      using \<open>perm_fun_list p \<nu> \<in> leaves G (tree G)\<close> by auto
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix p
    let ?n = "num_vertices G"
    assume "p \<in> ?rhs"
    then obtain \<nu>' \<pi> \<pi>' where 
      "\<nu>' \<in> leaves G (tree G)" "equivalent_leaves G \<nu> \<nu>'"
      "\<pi> = leaf_perm G \<nu>" "\<pi>' = leaf_perm G \<nu>'"
      and "p = perm_comp (perm_inv \<pi>') \<pi>"
      by auto
    then have "is_vertex_list G \<nu>" "is_vertex_list G \<nu>'" 
              "discrete (\<R> G \<nu>)"
              "discrete (\<R> G \<nu>')"
      using assms 
      by simp_all
      
    have "is_isomorphism p G G"
      unfolding is_isomorphism_def
    proof
      show "perm_dom p = ?n"
        using assms \<open>\<nu>' \<in> leaves G (tree G)\<close> \<open>\<pi> = leaf_perm G \<nu>\<close> \<open>\<pi>' = leaf_perm G \<nu>'\<close> \<open>p = perm_comp (perm_inv \<pi>') \<pi>\<close>
        by simp
    next
      show "perm_graph p G = G"
      proof-
        have "perm_graph \<pi> G = perm_graph \<pi>' G"
          using assms  \<open>equivalent_leaves G \<nu> \<nu>'\<close> `\<nu> \<in> leaves G (tree G)` `\<nu>' \<in> leaves G (tree G)`
          using \<Phi>_discrete  `\<pi> = leaf_perm G \<nu>` `\<pi>' = leaf_perm G \<nu>'` `is_vertex_list G \<nu>` `is_vertex_list G \<nu>'`
          by (simp add: equivalent_leaves_def)
        then have "perm_graph (perm_inv \<pi>') (perm_graph \<pi> G) = perm_graph (perm_inv \<pi>') (perm_graph \<pi>' G)"
          by simp
        then have "perm_graph (perm_comp (perm_inv \<pi>') \<pi>) G = perm_graph (perm_comp (perm_inv \<pi>')  \<pi>') G"
           by (simp add: \<open>\<pi> = leaf_perm G \<nu>\<close> \<open>\<pi>' = leaf_perm G \<nu>'\<close> \<open>discrete (\<R> G \<nu>')\<close> \<open>discrete (\<R> G \<nu>)\<close> \<open>is_vertex_list G \<nu>'\<close> \<open>is_vertex_list G \<nu>\<close>)
        then show "perm_graph p G = G"
          by (simp add: \<open>\<pi>' = leaf_perm G \<nu>'\<close> \<open>discrete (\<R> G \<nu>')\<close> \<open>is_vertex_list G \<nu>'\<close> \<open>p = perm_comp (perm_inv \<pi>') \<pi>\<close>)
      qed
    qed
    then show "p \<in> ?lhs"
      by (simp add: automorphisms_def is_automorphism_def)
  qed
qed

definition max_leaves :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list set" where
  "max_leaves G T = max_by_prop (leaves G T) (\<Phi> G)"

definition the_max_leaf :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list" where
  "the_max_leaf G T = rev (Min (rev ` max_leaves G T))"

definition max_leaf :: "colored_graph \<Rightarrow> Tree \<Rightarrow> vertex_list" where
  "max_leaf G T = (SOME \<nu>. \<nu> \<in> leaves G T \<and> (\<forall> \<nu>' \<in> leaves G T. \<Phi> G \<nu> \<ge> \<Phi> G \<nu>'))"

definition canon_form :: "colored_graph \<Rightarrow> colored_graph" where
  "canon_form G = (let \<nu> = max_leaf G (tree G) in perm_graph (leaf_perm G \<nu>) G)"


lemma max_leaves_not_empty [simp]:
  shows "max_leaves G (tree G) \<noteq> {}"
  by (simp add: max_leaves_def)

lemma max_leaves_T_not_empty [simp]:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "max_leaves G T \<noteq> {}"
  using assms max_by_prop_nonempty[of "leaves G T"]
  by (simp add: max_leaves_def)

lemma max_leaves_finite [simp]:
  shows "finite (max_leaves G (tree G))"
  by (simp add: max_leaves_def)

lemma max_leaves_T_finite [simp]:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "finite (max_leaves G T)"
  using assms max_by_prop_finite[of "leaves G T"]
  by (simp add: max_leaves_def)

lemma max_leaves_\<Phi>:
  assumes "\<nu> \<in> max_leaves G (tree G)"
  shows "\<Phi> G \<nu> = Max {\<Phi> G \<nu> | \<nu>. \<nu> \<in> leaves G (tree G)}"
  using assms
  unfolding max_leaves_def max_by_prop_def
  by (simp add: Setcompr_eq_image)

lemma the_max_leaf_in_max_leaves:
  shows "the_max_leaf G (tree G) \<in> max_leaves G (tree G)"
  unfolding the_max_leaf_def
  by (smt (verit, ccfv_SIG) Min_in finite_imageI image_iff image_is_empty max_leaves_finite max_leaves_not_empty rev_rev_ident)

lemma the_max_leaf_is_leaf:
  shows "the_max_leaf G (tree G) \<in> leaves G (tree G)"
  using max_by_prop_subseteq max_leaves_def the_max_leaf_in_max_leaves  
  by force

lemma the_max_leaf_T_in_max_leaves:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "the_max_leaf G T \<in> max_leaves G T"
  using assms
  by (smt (verit, ccfv_SIG) Min_in finite_imageI image_iff image_is_empty max_leaves_T_finite max_leaves_T_not_empty rev_rev_ident the_max_leaf_def)

lemma the_max_leaf_T_in_leaves:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "the_max_leaf G T \<in> leaves G T"
  using assms
  by (metis max_by_prop_iff max_leaves_def the_max_leaf_T_in_max_leaves)

lemma the_max_leaf_is_max:
  assumes "\<nu>' \<in> leaves G (tree G)"
  shows "\<Phi> G (the_max_leaf G (tree G)) \<ge> \<Phi> G \<nu>'"
  using assms
  unfolding the_max_leaf_def max_leaves_def
  by (metis leaves_finite max_by_prop_max_prop max_leaves_def the_max_leaf_def the_max_leaf_in_max_leaves)

lemma ex_max_leaf:
  shows "\<exists> \<nu>. \<nu> \<in> leaves G (tree G) \<and> (\<forall>\<nu>'\<in>leaves G (tree G). \<Phi> G \<nu> \<ge> \<Phi> G \<nu>')" (is "\<exists> \<nu>. ?P \<nu>")
proof-
  have "?P (the_max_leaf G (tree G))"
    using the_max_leaf_is_max the_max_leaf_in_max_leaves max_by_prop_subseteq 
    unfolding max_leaves_def
    by force
  then show ?thesis
    by blast
qed

lemma ex_max_leaf_T:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "\<exists> \<nu>. \<nu> \<in> leaves G T \<and> (\<forall>\<nu>'\<in>leaves G T. \<Phi> G \<nu> \<ge> \<Phi> G \<nu>')" (is "\<exists> \<nu>. ?P \<nu>")
proof-
  have "?P (the_max_leaf G T)"
    by (metis assms(1) assms(2) max_by_prop_max_prop max_leaves_def the_max_leaf_T_in_leaves the_max_leaf_T_in_max_leaves)
  then show ?thesis
    by blast
qed

lemma max_leaf_in_max_leaves:
  shows "max_leaf G (tree G) \<in> max_leaves G (tree G)"
  unfolding max_leaf_def
  using someI_ex[OF ex_max_leaf]
  by (simp add: max_by_prop_iff max_leaves_def)

lemma max_leaf_is_leaf:
  shows "max_leaf G (tree G) \<in> leaves G (tree G)"
  unfolding max_leaf_def 
  using someI_ex[OF ex_max_leaf]
  by blast


lemma max_leaf_T_in_max_leaves:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "max_leaf G T \<in> max_leaves G T"
  unfolding max_leaf_def
  using someI_ex[OF ex_max_leaf_T] assms
  by (simp add: max_by_prop_iff max_leaves_def)

lemma max_leaf_T_is_leaf:
  assumes "finite (leaves G T)" "leaves G T \<noteq> {}"
  shows "max_leaf G T \<in> leaves G T"
  using assms
  by (metis max_by_prop_iff max_leaf_T_in_max_leaves max_leaves_def)

lemma max_leaf_is_max:
  assumes "\<nu>' \<in> leaves G (tree G)"
  shows "\<Phi> G (max_leaf G (tree G)) \<ge> \<Phi> G \<nu>'" 
  using assms
  unfolding max_leaf_def 
  using someI_ex[OF ex_max_leaf]
  by blast

lemma max_leaf_the_some_eq:
  shows "\<Phi> G (the_max_leaf G (tree G)) = \<Phi> G (max_leaf G (tree G))" 
  by (metis leaves_finite leaves_not_empty max_by_prop_iff max_leaf_is_leaf max_leaf_is_max max_leaves_def order_antisym_conv the_max_leaf_in_max_leaves)

lemma the_canon_form:
  shows "canon_form G = (let \<nu> = the_max_leaf G (tree G) in perm_graph (leaf_perm G \<nu>) G)"
  unfolding canon_form_def Let_def
  by (metis leaves_finite leaves_iff_discrete_nodes leaves_not_empty max_by_prop_iff max_leaf_is_leaf max_leaf_the_some_eq max_leaves_def \<Phi>_discrete nodes_is_vertex_list the_max_leaf_in_max_leaves)

lemma canon_formI:
  assumes "\<nu>' \<in> leaves G (tree G)" "\<forall> \<nu> \<in> leaves G (tree G). \<Phi> G \<nu>' \<ge> \<Phi> G \<nu>"
  shows "canon_form G = perm_graph (leaf_perm G \<nu>') G"
  unfolding canon_form_def Let_def max_leaf_def
proof (rule someI2)
  show "\<nu>' \<in> leaves G (tree G) \<and> (\<forall>\<nu>\<in>leaves G (tree G). \<Phi> G \<nu> \<le> \<Phi> G \<nu>')"
    using assms
    by simp
next
  fix \<nu>
  assume "\<nu> \<in> leaves G (tree G) \<and> (\<forall> \<nu>' \<in> leaves G (tree G). \<Phi> G \<nu>' \<le> \<Phi> G \<nu>)"
  then have "equivalent_leaves G \<nu> \<nu>'"
    using assms
    by (simp add: equivalent_leaves_def order_class.order.eq_iff)

  then show "perm_graph (leaf_perm G \<nu>) G = perm_graph (leaf_perm G \<nu>') G"
    using \<open>\<nu> \<in> leaves G (tree G) \<and> (\<forall>\<nu>'\<in>leaves G (tree G). \<Phi> G \<nu>' \<le> \<Phi> G \<nu>)\<close>
    using assms
    using \<Phi>_discrete[of G \<nu> \<nu>' "\<R> G \<nu>" "\<R> G \<nu>'"]
    by (simp add: equivalent_leaves_def)
qed         

lemma perm_leaf_perm:
  assumes "perm_dom p = num_vertices G" "\<nu> \<in> leaves G (tree G)"
  shows "perm_comp (leaf_perm (perm_graph p G) (perm_fun_list p \<nu>)) p =
         leaf_perm G \<nu>" (is "?lhs = ?rhs")
proof (rule permEqI)
  show "\<forall> v. vertex G v \<longrightarrow> perm_fun ?lhs v = perm_fun ?rhs v"
    using assms
    by (simp del: \<R>_perm)
next
  show "perm_dom ?rhs = num_vertices G"
    using assms
    by simp
next
  show "perm_dom ?lhs = num_vertices G "
    using assms
    by (simp del: \<R>_perm)
qed

theorem canon_form:
  shows "is_canon_form canon_form"
  unfolding is_canon_form_def
proof safe
  fix G
  obtain \<nu>' where "\<nu>' \<in> leaves G (tree G)" "\<forall> \<nu> \<in> leaves G (tree G). \<Phi> G \<nu>' \<ge> \<Phi> G \<nu>"
    using ex_max_leaf
    by blast
  then show "isomorphic G (canon_form G)"
    unfolding isomorphic_def is_isomorphism_def
    using canon_formI
    by (rule_tac x="leaf_perm G \<nu>'" in exI) simp
next
  fix G :: colored_graph and p
  assume "perm_dom p = num_vertices G"
  obtain \<nu>' where \<nu>': "\<nu>' \<in> leaves G (tree G)" "\<forall> \<nu> \<in> leaves G (tree G). \<Phi> G \<nu>' \<ge> \<Phi> G \<nu>"
    using ex_max_leaf
    by blast
  let ?pG = "perm_graph p G"
  let ?p\<nu>' = "perm_fun_list p \<nu>'"
  have "?p\<nu>' \<in> leaves (perm_graph p G) (perm_tree p (tree G))"
    using \<nu>'(1) \<open>perm_dom p = num_vertices G\<close>
    by auto
  then have p\<nu>'1: "?p\<nu>' \<in> leaves ?pG (tree ?pG)"
    using \<open>perm_dom p = num_vertices G\<close>
    by simp

  have "\<Phi> ?pG ?p\<nu>' = \<Phi> G \<nu>'"
    using \<Phi>_perm \<open>\<nu>' \<in> leaves G (tree G)\<close> \<open>perm_dom p = num_vertices G\<close> 
    using leaf_is_node
    by blast

  have p\<nu>'2: "\<forall> \<nu> \<in> leaves ?pG (tree ?pG). \<Phi> ?pG ?p\<nu>' \<ge> \<Phi> ?pG \<nu>"
  proof safe
    fix \<nu>
    assume "\<nu> \<in> leaves ?pG (tree ?pG)"
    then have "perm_fun_list (perm_inv p) \<nu> \<in> leaves G (tree G)"
      using \<open>perm_dom p = num_vertices G\<close> 
      by (metis perm_dom_perm_inv num_vertices_perm_graph perm_graph_perm_inv1 perm_graph_tree_leaves)
    then have "\<Phi> G (perm_fun_list (perm_inv p) \<nu>) \<le> \<Phi> G \<nu>'"
      using \<nu>'(2)
      by simp
    moreover
    have "\<Phi> G (perm_fun_list (perm_inv p) \<nu>) = \<Phi> (perm_graph p G) \<nu>"
      using \<open>\<nu> \<in> leaves ?pG (tree ?pG)\<close> \<open>perm_dom p = num_vertices G\<close> 
      using \<Phi>_perm[of \<nu> "perm_graph p G" "perm_inv p"]
      by auto
    ultimately 
    have "\<Phi> (perm_graph p G) \<nu> \<le> \<Phi> G \<nu>'"
      by auto
    thus "\<Phi> ?pG ?p\<nu>' \<ge> \<Phi> ?pG \<nu>"
      using \<open>\<Phi> (perm_graph p G) (perm_fun_list p \<nu>') = \<Phi> G \<nu>'\<close>
      by simp
  qed
  have "canon_form ?pG = perm_graph (leaf_perm ?pG ?p\<nu>') ?pG"
    using canon_formI p\<nu>'1 p\<nu>'2 \<open>perm_dom p = num_vertices G\<close>
    by simp
  also have "... = perm_graph (perm_comp (leaf_perm ?pG ?p\<nu>') p) G"
    using \<open>perm_dom p = num_vertices G\<close> `\<nu>' \<in> leaves G (tree G)`
    by (simp del: \<R>_perm)
  also have "... = perm_graph (leaf_perm G \<nu>') G"
    using \<nu>'(1) \<open>perm_dom p = num_vertices G\<close>
    by (simp add: perm_leaf_perm)
  also have "... = canon_form G"
    using canon_formI[OF \<nu>'(1-2)]
    by auto
  finally show "canon_form (perm_graph p G) = canon_form G"
    .
qed

subsection \<open>Pruning\<close>

primrec prune_node :: "Tree \<Rightarrow> Tree \<Rightarrow> Tree" where                   
  "prune_node (Node \<nu> ns) n = 
   (Node \<nu> ((ffilter (\<lambda> n'. n' \<noteq> n) ((\<lambda> n'. prune_node n' n) |`| ns))))"

definition prune_nodes :: "Tree \<Rightarrow> Tree list \<Rightarrow> Tree" where
  "prune_nodes T ns = foldl prune_node T ns"

lemma prune_nodes_Nil [simp]:
  shows "prune_nodes T [] = T"
  by (simp add: prune_nodes_def)

lemma prune_nodes_snoc [simp]:
  shows "prune_nodes T (ns @ [n]) = prune_node (prune_nodes T ns) n"
  by (simp add: prune_nodes_def)

lemma nodes_prune_node:
  shows "nodes (prune_node T V) \<subseteq> nodes T"
  by (induction T) auto

lemma leaves_prune_node:
  shows "leaves G (prune_node T V) \<subseteq> leaves G T"
  by (induction T) auto  

lemma leaves_prune_nodes:
  shows "leaves G (prune_nodes T Vs) \<subseteq> leaves G T"
proof (induction Vs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next 
  case (snoc V Vs)
  thus ?case
    using leaves_prune_node
    by force
qed


lemma leaves_prune_nodeI:
  assumes "V \<notin> leaves G T'" "V \<in> leaves G T"
  shows "V \<in> leaves G (prune_node T T')"
  using assms
proof (induction T)
  case (Node V' ns')
  show ?case
  proof (cases "\<T> G V' = {||}")
    case True
    then show ?thesis
      using Node.prems
      by simp
  next
    case False
    then show ?thesis
      using Node
      by force
  qed
qed

definition pruneA :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneA G \<nu>1 \<nu>2 \<longleftrightarrow> 
      \<nu>1 \<in> nodes (tree G) \<and> \<nu>2 \<in> nodes (tree G) \<and> List.length \<nu>1 = List.length \<nu>2 \<and>
       \<Phi> G \<nu>1 > \<Phi> G \<nu>2"

definition pruneB :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneB G \<nu>1 \<nu>2 \<longleftrightarrow> 
      \<nu>1 \<in> nodes (tree G) \<and> \<nu>2 \<in> nodes (tree G) \<and> List.length \<nu>1 = List.length \<nu>2 \<and>
       \<Phi> G \<nu>1 \<noteq> \<Phi> G \<nu>2"

definition pruneC :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> vertex_list \<Rightarrow> bool" where
  "pruneC G \<nu>1 \<nu>2 \<longleftrightarrow>
      \<nu>1 \<in> nodes (tree G) \<and> \<nu>2 \<in> nodes (tree G) \<and> rev \<nu>1 < rev \<nu>2 \<and>
     (\<exists> p \<in> automorphisms G. perm_fun_list p \<nu>1 = \<nu>2)"

lemma pruneA_max_leaves:
  assumes "pruneA G \<nu>1 \<nu>2" "\<nu> \<in> max_leaves G (tree G)" 
  shows "\<nu> \<notin> leaves G (expand_tree G \<nu>2)"
proof-
  have *: "\<Phi> G \<nu>1 > \<Phi> G \<nu>2" 
         "List.length \<nu>1 = List.length \<nu>2" 
         "\<nu>1 \<in> nodes (tree G)" "\<nu>2 \<in> nodes (tree G)"
    using \<open>pruneA G \<nu>1 \<nu>2\<close>
    unfolding pruneA_def
    by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    obtain \<nu>1' where "\<nu>1' \<in> leaves G (expand_tree G \<nu>1)"
      using \<open>\<nu>1 \<in> nodes (tree G)\<close> 
      by fastforce

    have "\<Phi> G \<nu>1' > \<Phi> G \<nu>"
     using \<open>\<not> \<nu> \<notin> leaves G (expand_tree G \<nu>2)\<close> 
     using \<Phi>_mono[of \<nu>2 G \<nu>1] \<open>List.length \<nu>1 = List.length \<nu>2\<close>
     using \<open>\<nu>1 \<in> nodes (tree G)\<close> \<open>\<nu>1' \<in> leaves G (expand_tree G \<nu>1)\<close> \<open>\<nu>2 \<in> nodes (tree G)\<close> \<open>\<Phi> G \<nu>2 < \<Phi> G \<nu>1\<close>
     by simp
   then show False
     by (metis (no_types, lifting) "*"(3) \<open>\<nu>1' \<in> leaves G (expand_tree G \<nu>1)\<close> assms(2) is_vertex_list_empty leD max_leaf_is_max max_leaf_the_some_eq max_leaves_\<Phi> target_cell_selector.leaves_of_node target_cell_selector_axioms the_max_leaf_in_max_leaves tree_def)
  qed
qed

lemma pruneA_max_leaf:
  assumes "pruneA G \<nu>1 \<nu>2" 
  shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
  using assms pruneA_max_leaves the_max_leaf_in_max_leaves
  by blast

lemma the_max_leaf_lex_min:
  assumes "\<nu> \<in> max_leaves G (tree G)"
  shows "rev (the_max_leaf G (tree G)) \<le> rev \<nu>"
  using assms
  unfolding the_max_leaf_def
  by simp

lemma pruneC_max_leaf:
  assumes "pruneC G \<nu>1 \<nu>2"
  shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
proof-
  obtain p where 
    *: "rev \<nu>1 < rev \<nu>2"
    "\<nu>1 \<in> nodes (tree G)" "\<nu>2 \<in> nodes (tree G)"
    "p \<in> automorphisms G" "perm_fun_list p \<nu>1 = \<nu>2"
    using \<open>pruneC G \<nu>1 \<nu>2\<close>
    unfolding pruneC_def
    by auto

  then have "List.length \<nu>1 = List.length \<nu>2"
    unfolding perm_fun_list_def
    by auto

  have "is_vertex_list G \<nu>1" "is_vertex_list G \<nu>2"
    using * nodes_is_vertex_list
    by blast+
  then have "perm_fun_list (perm_inv p) \<nu>2 = \<nu>1"
    using *
    unfolding automorphisms_def is_automorphism_def is_isomorphism_def
    using perm_fun_list_perm_inv[of p "num_vertices G" \<nu>1]
    by (simp add: is_vertex_list_def)

  let ?\<nu> = "the_max_leaf G (tree G)"
  have "is_vertex_list G ?\<nu>"
    using the_max_leaf_is_leaf leaf_is_node nodes_is_vertex_list
    by blast
    
  show "?\<nu> \<notin> leaves G (expand_tree G \<nu>2)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    let ?p\<nu>1 = "perm_fun_list p \<nu>1"
    let ?p\<nu> = "perm_fun_list (perm_inv p) ?\<nu>"

    have "expand_tree G ?p\<nu>1 = perm_tree p (expand_tree G \<nu>1)"
      using *
      using \<open>is_vertex_list G \<nu>1\<close> automorphisms_def
      using expand_tree_perm_automorphism
      by blast

    have "?p\<nu> \<in> leaves G (expand_tree G \<nu>1)"
      using *(1) *(4)
      using \<open>\<not>  ?\<nu> \<notin> leaves G (expand_tree G \<nu>2)\<close> \<open>is_vertex_list G \<nu>2\<close> 
      using \<open>perm_fun_list (perm_inv p) \<nu>2 = \<nu>1\<close> 
      using automorphisms_def is_automorphism_perm_inv perm_node_in_expand_tree_leaves_automorphism
      by auto
    then have "?p\<nu> \<in> leaves G (tree G)"
      using "*"(4) automorphisms_def perm_node_in_tree_leaves_automorphism the_max_leaf_is_leaf by force
    then have "?p\<nu> \<in> max_leaves G (tree G)"
      using \<open>is_vertex_list G ?\<nu>\<close>
      using \<Phi>_perm[where p="perm_inv p" and G = G and \<nu> = "?\<nu>"]
      using \<open>p \<in> automorphisms G\<close>
      unfolding automorphisms_def is_automorphism_def is_isomorphism_def
      by (smt (verit, ccfv_threshold) leaves_finite leaves_iff_discrete_nodes max_by_prop_max_prop_gt max_leaves_def mem_Collect_eq order_less_irrefl perm_dom_perm_inv perm_graph_perm_inv1 the_max_leaf_in_max_leaves the_max_leaf_is_leaf)
    then have "rev ?p\<nu> \<ge> rev ?\<nu>"
      using the_max_leaf_lex_min
      by blast

    moreover

    have "\<exists> k. drop k ?p\<nu> = \<nu>1"
      using `?p\<nu> \<in> leaves G (expand_tree G \<nu>1)` `is_vertex_list G \<nu>1`
      using leaves_expand_tree_suffix
      by blast

    moreover

    have "\<exists> k. drop k ?\<nu> = \<nu>2"
      using `\<not> ?\<nu> \<notin> leaves G (expand_tree G \<nu>2)` `is_vertex_list G \<nu>2`
      using leaves_expand_tree_suffix
      by blast
          
    ultimately

    show False
      using \<open>rev \<nu>1 < rev \<nu>2\<close> \<open>List.length \<nu>1 = List.length \<nu>2\<close>
      using list_less_right_append[of "rev \<nu>1" "rev \<nu>2"]
      by (metis append_take_drop_id length_rev linorder_not_less rev_append)
  qed
qed

definition pruneAs :: "colored_graph \<Rightarrow> vertex_list list \<Rightarrow> bool" where
  "pruneAs G \<nu>s \<longleftrightarrow> (\<forall> \<nu>2 \<in> set \<nu>s. \<exists> \<nu>1. pruneA G \<nu>1 \<nu>2)"

definition pruneACs :: "colored_graph \<Rightarrow> vertex_list list \<Rightarrow> bool" where
  "pruneACs G \<nu>s \<longleftrightarrow> (\<forall> \<nu>2 \<in> set \<nu>s. \<exists> \<nu>1. pruneA G \<nu>1 \<nu>2 \<or> pruneC G \<nu>1 \<nu>2)"

lemma pruneAs_remain_max_leaves:
  assumes "pruneAs G \<nu>s" "\<nu> \<in> max_leaves G (tree G)"
  shows "\<nu> \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) \<nu>s))"
  using assms
proof (induction \<nu>s rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: max_by_prop_iff max_leaves_def)
next
  case (snoc \<nu>2 \<nu>s)
  then have "\<nu> \<notin> leaves G (expand_tree G \<nu>2)"
    using pruneA_max_leaves
    by (auto simp add: pruneAs_def)
  then show ?case
    using snoc
    by (auto simp add: leaves_prune_nodeI pruneAs_def)
qed

lemma pruneAs_remain_max_leaf:
  assumes "pruneAs G \<nu>s" 
  shows "the_max_leaf G (tree G) \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) \<nu>s))"
  using assms
  using pruneAs_remain_max_leaves the_max_leaf_in_max_leaves
  by blast

lemma pruneACs_remain_max:
  assumes "pruneACs G \<nu>s"
  shows "the_max_leaf G (tree G) \<in> leaves G (prune_nodes (tree G) (map (expand_tree G) \<nu>s))"
  using assms
proof (induction \<nu>s rule: rev_induct)
  case Nil
  then show ?case
    using the_max_leaf_is_leaf
    by force
next
  case (snoc \<nu>2 \<nu>s)
  then have "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
    using pruneA_max_leaf pruneC_max_leaf
    by (meson in_set_conv_decomp pruneACs_def)
  then show ?case
    using snoc
    by (auto simp add: leaves_prune_nodeI pruneACs_def)
qed

lemma pruneACs_canon_form:
  assumes "pruneACs G \<nu>s"
          "T = prune_nodes (tree G) (map (expand_tree G) \<nu>s)"
  shows "canon_form G = perm_graph (leaf_perm G (max_leaf G T)) G"
proof (rule canon_formI)
  have "the_max_leaf G (tree G) \<in> leaves G T"
    using assms
    using pruneACs_remain_max
    by auto
  then have "max_leaf G T \<in> leaves G T"
    by (metis assms(2) equals0D infinite_super max_leaf_T_is_leaf leaves_prune_nodes leaves_finite)
  then show "max_leaf G T \<in> leaves G (tree G)"
    using assms(2) leaves_prune_nodes 
    by blast
next
  show "\<forall>\<nu>\<in>leaves G (tree G). \<Phi> G \<nu> \<le> \<Phi> G (max_leaf G T)"
    by (smt (verit) assms(1) assms(2) equals0D leaves_finite max_by_prop_max_prop max_leaf_T_in_max_leaves max_leaf_T_is_leaf max_leaf_the_some_eq max_leaves_def leaves_prune_nodes pruneACs_remain_max  order_antisym rev_finite_subset subsetD)
qed

end

section \<open>Refine refinement procedure\<close>

locale refinement_function' =
  fixes \<F> :: "colored_graph \<Rightarrow> coloring"
  assumes \<F>_finer: 
    "\<And> G. finer (\<F> G) (colors G)"
  assumes \<F>_perm [simp]:
    "\<And> p G \<pi>. 
       \<lbrakk>perm_dom p = num_vertices G; length \<pi> = num_vertices G\<rbrakk> \<Longrightarrow> 
          \<F> (recolor (perm_graph p G) (perm_coloring p \<pi>)) = 
          perm_coloring p (\<F> (recolor G \<pi>))"
begin

definition \<R>' :: "colored_graph \<Rightarrow> vertex_list \<Rightarrow> coloring" where
  "\<R>' G \<nu> = fold (\<lambda> v c. \<F> (recolor G (individualize c v))) (rev \<nu>) (\<F> G)"

lemma \<R>'_Nil [simp]:
  shows "\<R>' G [] = \<F> G"
  by (simp add: \<R>'_def)

lemma \<R>'_Cons [simp]:
  shows "\<R>' G (v # \<nu>) = \<F> (recolor G (individualize (\<R>' G \<nu>) v))"
  by (simp add: \<R>'_def)

lemma \<F>_length [simp]:
  shows "length (\<F> G) = num_vertices G"
  using \<F>_finer[of G]
  by (simp add: finer_def)

lemma \<R>'_length [simp]:
  assumes "is_vertex_list G V"
  shows "length (\<R>' G V) = num_vertices G"
  using assms
  by (induction V) (auto simp add: is_vertex_list_def)

lemma \<F>_singleton:
  assumes "{v} \<in> set (cells (colors G))" "vertex G v"
  shows "{v} \<in> set (cells (\<F> G))"
  using assms \<F>_finer finer_singleton
  by auto

lemma \<F>_perm0 [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "\<F> (perm_graph p G) = perm_coloring p (\<F> G)"
  using \<F>_perm[OF assms, of "colors G"]
  by (metis assms colors_recolor edges_recolor graph_eqI length_colors_num_vertices recolor_perm)
end

sublocale refinement_function' \<subseteq> refinement_function "\<R>'"
proof
  fix \<nu> G
  assume "is_vertex_list G \<nu>"
  then show "finer (\<R>' G \<nu>) (colors G)"
  proof (induction \<nu>)
    case Nil
    then show ?case
      using \<R>'_Nil \<F>_finer 
      by presburger
  next
    case (Cons v \<nu>)
    show ?case
    proof (rule finer_trans)
      show "finer (\<R>' G (v # \<nu>)) (\<R>' G \<nu>)"
      proof (rule finer_trans)
        have "v < length (\<R>' G \<nu>)"
          using Cons.prems
          by (auto simp add: is_vertex_list_def)
        then show "finer (individualize (\<R>' G \<nu>) v) (\<R>' G \<nu>)"
          by simp

        show "finer (\<R>' G (v # \<nu>)) (individualize (\<R>' G \<nu>) v)"
          using \<F>_finer[of "recolor G (individualize (\<R>' G \<nu>) v)"] `v < length (\<R>' G \<nu>)` Cons.prems
          by (auto simp add: is_vertex_list_cons)
      qed
    next
      show "finer (\<R>' G \<nu>) (colors G)"
        using Cons
        by (simp add: is_vertex_list_cons)
    qed
  qed
next
  fix v \<nu> G
  assume "is_vertex_list G \<nu>" "v \<in> set \<nu>"
  then show "{v} \<in> set (cells (\<R>' G \<nu>))"
  proof (induction \<nu>)
    case Nil
    then show ?case
      by simp
  next
    case (Cons v' \<nu>)
    have "vertex G v'" "vertex G v"
      using Cons.prems
      by (auto simp add: is_vertex_list_def)
    show ?case
    proof (cases "v = v'")
      case True      
      then show ?thesis
        using \<F>_singleton individualize_singleton
        using \<open>vertex G v'\<close> is_vertex_list_cons Cons.prems(1)
        by auto
    next
      case False
      then show ?thesis
        using Cons \<open>vertex G v\<close>
        using individualize_singleton_preserve
        using \<F>_singleton \<open>vertex G v'\<close> is_vertex_list_cons
        by auto
    qed
  qed
next
  fix \<nu> G p
  assume "is_vertex_list G \<nu>" "perm_dom p = num_vertices G"
  then show "\<R>' (perm_graph p G) (perm_fun_list p \<nu>) = perm_coloring p (\<R>' G \<nu>)"
  proof (induction \<nu> arbitrary: v)
    case Nil
    show ?case
      using Nil.prems(2)
      by auto
  next
    case (Cons v' \<nu>)
    then show ?case
      by (metis \<F>_perm \<R>'_Cons \<R>'_length individualize_length individualize_perm is_vertex_list_cons(1) is_vertex_list_cons(3) perm_fun_list_Cons)
  qed
qed

section \<open>Refine node invariants\<close>

definition parents :: "vertex_list \<Rightarrow> vertex_list list" where
  "parents \<nu> = map (\<lambda> k. drop k \<nu>) (rev [0..<List.length \<nu> + 1])"

lemma parents_Nil [simp]:
  "parents [] = [[]]"
  by (simp add: parents_def)

lemma parents_Cons [simp]: 
  "parents (v # \<nu>) = parents \<nu> @ [v # \<nu>]"
proof-
  have "parents (v # \<nu>) =  map (\<lambda>k. drop k (v # \<nu>)) (rev [0..<List.length (v # \<nu>) + 1])"
    unfolding parents_def
    by simp
  also have "... = map (\<lambda>k. drop k (v # \<nu>)) (rev [1..<List.length (v # \<nu>) + 1]) @ [v # \<nu>]"
    by (simp add: upt_rec)
  also have "... = map (\<lambda>k. drop k \<nu>) (rev [0..<List.length \<nu> + 1]) @ [v # \<nu>]"
  proof-
    have "(rev [1..<List.length (v # \<nu>) + 1]) = map (\<lambda> x. x + 1) (rev [0..<List.length \<nu> + 1])"
      by (metis Suc_eq_plus1 length_Cons map_add_upt rev_map)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by (simp add: parents_def)
qed

lemma hd_parents [simp]:
  shows "hd (parents \<nu>) = []"
  by (induction \<nu>) (auto simp add: parents_def)

lemma parents_append [simp]: 
  "parents (\<nu>1 @ \<nu>2) = 
   parents \<nu>2 @ (map (\<lambda> x. x @ \<nu>2) (tl (parents \<nu>1)))"
proof (induction \<nu>1)
  case Nil
  have "parents \<nu>1 = [] # tl (parents \<nu>1)"
    using hd_parents[of \<nu>1]
    using hd_Cons_tl[of "parents \<nu>1"]
    by (metis Nil_is_append_conv list.distinct(1) map_tailrec_rev.elims parents_Cons parents_Nil)
  then show ?case
    by simp
next
  case (Cons v \<nu>1)
  obtain x \<nu> where "parents \<nu>1 = x # \<nu>"
    by (metis Nil_is_append_conv list.exhaust parents_Cons parents_Nil)
  then show ?case
    using Cons
    by (auto simp add: tl_append)
qed

lemma length_parents [simp]:
  shows "List.length (parents \<nu>) = List.length \<nu> + 1"
  by (simp add: parents_def)

lemma parents_perm [simp]:
  shows "parents (perm_fun_list p \<nu>) = map (perm_fun_list p) (parents \<nu>)"
  by (induction \<nu>) (auto simp add: perm_fun_list_def)

lemma parents_vertex_lists:
  assumes "\<nu>' \<in> set (parents \<nu>)" "is_vertex_list G \<nu>"
  shows "is_vertex_list G \<nu>'"
  using assms
  by (induction \<nu>) (auto simp add: is_vertex_list_def)

locale split =
  fixes split :: "colored_graph \<Rightarrow> color \<Rightarrow> coloring"
  assumes split_length [simp]:
    "\<And> G c. \<lbrakk> c < num_colors G \<rbrakk> \<Longrightarrow>
        length (split G c) = length (colors G)"
  assumes split_finer [simp]: 
    "\<And> G c. \<lbrakk> c < num_colors G \<rbrakk> \<Longrightarrow>
        finer (split G c) (colors G)"
  assumes split_perm [simp]:
   "\<And> G c. \<lbrakk> c < num_colors G; perm_dom p = num_vertices G \<rbrakk> \<Longrightarrow> 
        split (perm_graph p G) c = perm_coloring p (split G c)"
begin

definition split_graph :: "colored_graph \<Rightarrow> color \<Rightarrow> colored_graph" where
  "split_graph G c = recolor G (split G c)"

lemma split_graph_finer [simp]:
  assumes "c < num_colors G"
  shows "finer (colors (split_graph G c)) (colors G)"
  using assms split_finer split_length
  unfolding split_graph_def Let_def
  by simp

lemma num_vertices_split_graph [simp]:
  assumes "c < num_colors G"
  shows "num_vertices (split_graph G c) = num_vertices G"
  using split_length assms
  unfolding split_graph_def Let_def
  by simp

lemma edges_split_graph [simp]:
  assumes "c < num_colors G"
  shows "edges (split_graph G c) = edges G"
  using assms
  by (simp add: split_graph_def)

lemma split_graph_perm [simp]:
  assumes "perm_dom p = num_vertices G" "c < num_colors G"
  shows "split_graph (perm_graph p G) c = perm_graph p (split_graph G c)"
  using assms
  unfolding split_graph_def
  by simp

function \<F>' :: "colored_graph \<Rightarrow> colored_graph" where
 "\<F>' G = (
     let \<pi> = colors G;
         Ws = {j \<in> {0..<num_colors G}. split G j \<prec> \<pi>} 
      in if Ws = {} 
         then G 
         else (
            let i = Min Ws;
                G' = split_graph G i
             in \<F>' G'  
        )
  )"
  by pat_completeness auto
termination
proof (relation "measure (\<lambda> G. num_vertices G -  List.length (cells (colors G)))")
  show "wf (measure (\<lambda>G. ColoredGraph.num_vertices G - List.length (cells (colors G))))"
    by auto
next
  fix G colorsG split_colors c G'
  assume *: "colorsG = colors G"
         "split_colors = {j \<in> {0..<num_colors G}. split G j \<prec> colorsG}"
         "split_colors \<noteq> {}" "c = Min split_colors" "G' = split_graph G c"
  have "num_vertices G' - ColoredGraph.num_colors G' < num_vertices G - ColoredGraph.num_colors G"
  proof-
    have "c < num_colors G"
      using Min_in[of split_colors]
      using "*"(2) "*"(3) "*"(4) by auto
    then have "num_vertices G' = num_vertices G"
      using `G' = split_graph G c` 
      by auto
    moreover
    have "num_colors G \<le> num_vertices G" "num_colors G' \<le> num_vertices G'"
      by (simp_all add: num_colors_ub)
    moreover
    have "num_colors G' > num_colors G"
    proof-
      have "colors G' \<prec> colors G"
        by (metis (no_types, lifting) "*"(1) "*"(2) "*"(3) "*"(4) "*"(5) Min_in atLeastLessThan_iff colors_recolor finer_length finer_strict_def finite_nat_set_iff_bounded length_colors_num_vertices mem_Collect_eq split_graph_def)
      then show ?thesis
        by (simp add: num_colors_finer_strict)
    qed
    ultimately 
    show ?thesis
      by auto
  qed
  then show "(G', G) \<in> measure (\<lambda>G. num_vertices G - List.length (cells (ColoredGraph.colors G)))"
    unfolding measure_def
    by auto
qed

declare \<F>'.simps [simp del]

lemma \<F>'_finer:
shows "finer (colors (\<F>' G)) (colors G)"
proof (induction G rule: \<F>'.induct)
  case (1 G)
  show ?case
  proof (cases "\<forall>j<num_colors G. \<not> split G j \<prec> colors G")
    case True
    thus ?thesis
      using \<F>'.simps[of G]
      by (simp add: Let_def finer_refl)
  next
    case False
    let ?Ws = "{j \<in> {0..<num_colors G}. split G j \<prec> colors G}"
    let ?i = "Min ?Ws"
    have "?Ws \<noteq> {}"
      using False
      by auto
    then have "?i \<in> ?Ws"
      using Min_in[of ?Ws]
      by simp
    then have "?i < num_colors G" "split G ?i \<prec> colors G"
      by auto

    have "finer (colors (\<F>' (split_graph G ?i))) (colors (split_graph G ?i))"
      using False
      using 1(1)[of "colors G" ?Ws ?i "split_graph G ?i"] 
      by (auto simp add: Let_def)
    then show ?thesis
      using split_graph_finer[OF \<open>?i < num_colors G\<close>]
      using False
      using \<F>'.simps[of G] 
      using finer_trans
      using \<open>?Ws \<noteq> {}\<close> 
      by presburger
  qed
qed

lemma \<F>'_length [simp]:
  shows "length (colors (\<F>' G)) = num_vertices G"
  using \<F>'_finer finer_length by fastforce

lemma \<F>'_num_vertices [simp]:
  shows "num_vertices (\<F>' G) = num_vertices G"
proof (induction G rule: \<F>'.induct)
  case (1 G)
  show ?case
  proof (cases "\<forall>j<num_colors G. \<not> split G j \<prec> colors G")
    case True
    then show ?thesis
      using \<F>'.simps[of G]
      by simp
  next
    case False
    then show ?thesis
      using \<F>'.simps[of G]
      using 1
      using \<F>'_length
      by (metis length_colors_num_vertices)
  qed
qed  

lemma \<F>'_edges [simp]:
  shows "edges (\<F>' G) = edges G"
proof (induction G rule: \<F>'.induct)
  case (1 G)
  show ?case
  proof (cases "\<forall>j<num_colors G. \<not> split G j \<prec> colors G")
    case True
    then show ?thesis
      using \<F>'.simps[of G]
      by simp
  next
    case False
    then have "edges (split_graph G (Min {j. j < num_colors G \<and> split G j \<prec> colors G})) = edges G"
      by (metis (mono_tags, lifting) Collect_empty_eq Min_in edges_split_graph finite_nat_set_iff_bounded mem_Collect_eq)
    then have "edges (\<F>' (split_graph G (Min {j. j < num_colors G \<and> split G j \<prec> colors G}))) = edges G"
      using False 1
      by auto
    then show ?thesis
      using \<F>'.simps[of G]
      by (simp add: Let_def split: if_split_asm)
  qed
qed

lemma \<F>'_perm [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "\<F>' (perm_graph p G) = perm_graph p (\<F>' G)"
  using assms
proof (induction G rule: \<F>'.induct)
  case (1 G)

  let ?\<pi> = "colors G"
  let ?k = "num_colors G" 
  let ?Ws = "{j \<in> {0..<?k}. split G j \<prec> ?\<pi>}"
  let ?G' = "perm_graph p G"
  let ?\<pi>' = "colors ?G'"
  let ?k' = "num_colors ?G'" 
  let ?Ws' = "{j \<in> {0..<?k'}. split ?G' j \<prec> ?\<pi>'}"

  have "?k' = ?k"
    using "1.prems"
    by simp_all

  have "?Ws = ?Ws'"
    using "1.prems" `?k' = ?k`
    by (metis atLeastLessThan_iff colors_perm_graph finer_strict_perm_coloring finer_strict_perm_coloring' length_colors_num_vertices split_length split_perm)

  show ?case
  proof (cases "?Ws = {}")
    case True
    then have "\<F>' G = G" "\<F>' ?G' = ?G'" 
      using \<F>'.simps[of G] \<F>'.simps[of ?G'] "1.prems" `?Ws = ?Ws'`
      unfolding Let_def
      by metis+
    then show ?thesis
      using "1.prems"
      by simp
  next
    case False
    then have *: "\<F>' G = \<F>' (split_graph G (Min ?Ws))"
                 "\<F>' ?G' = \<F>' (split_graph ?G' (Min ?Ws'))"
      using `?Ws = ?Ws'` `?k' = ?k`
      using \<F>'.simps[of G] \<F>'.simps[of ?G'] "1.prems" `?Ws = ?Ws'`
      unfolding Let_def
      by metis+
    let ?i = "Min ?Ws"

    have "?i < ?k"
      using False Min_in[of ?Ws]
      by auto

    have  "split_graph ?G' (Min ?Ws') = 
           perm_graph p (split_graph G (Min ?Ws))"
      using "1.prems" * `?i < ?k` `?Ws = ?Ws'`
      by simp
        
    then show ?thesis
      using "1.prems" * False `?i < ?k` 1(1)
      by simp
  qed
qed      

lemma \<F>'_no_split:
  assumes "j < num_colors (\<F>' G)"
  shows "\<not> split (\<F>' G) j \<prec> colors (\<F>' G)"
  using assms
proof (induction G rule: \<F>'.induct)
  case (1 G)
  let ?Ws = "{j \<in> {0..<num_colors G}. split G j \<prec> colors G}"
  show ?case
    using \<F>'.simps[of G]
  proof (cases "?Ws = {}")
    case True
    then show ?thesis
      using 1(2) \<F>'.simps[of G]
      by simp
  next
    case False
    then show ?thesis
      using 1(1)[of "colors G" ?Ws "Min ?Ws" "split_graph G (Min ?Ws)"]
      using \<F>'.simps[of G]
      using "1.prems" by presburger
  qed
qed

lemma \<F>'_fixed_point:
  shows "\<F>' (\<F>' G) = \<F>' G"
  by (smt (verit, best) Collect_empty_eq \<F>'.elims \<F>'_no_split atLeastLessThan_iff)

lemma recolor_\<F>' [simp]:
  "recolor G (colors (\<F>' G)) = \<F>' G"
  by (rule graph_eqI) auto

definition is_split :: "colored_graph \<Rightarrow> coloring \<Rightarrow> bool" where
 "is_split G \<pi> \<longleftrightarrow> (\<forall> j < Coloring.num_colors \<pi>. \<not> split (recolor G \<pi>) j \<prec> \<pi>)"

end

sublocale split \<subseteq> refinement_function' "(\<lambda> G. colors (\<F>' G))"
proof
  fix G
  show "finer (colors (\<F>' G)) (colors G)"
    by (rule \<F>'_finer)
next
  fix p G \<pi>
  assume "perm_dom p = num_vertices G" "length \<pi> = num_vertices G"
  then show "colors (\<F>' (recolor (perm_graph p G) (perm_coloring p \<pi>))) = 
        perm_coloring p (colors (\<F>' (recolor G \<pi>)))"
    by simp
qed

context split
begin

lemma is_split:
  assumes "is_vertex_list G \<nu>"
  shows "is_split G (\<R>' G \<nu>)"
proof (cases \<nu>)
  case Nil
  then show ?thesis
    unfolding is_split_def
    by (metis \<F>'_no_split \<R>'_Nil recolor_\<F>')
next
  case (Cons v \<nu>')
  have "recolor G (ColoredGraph.colors (\<F>' (recolor G (individualize (\<R>' G \<nu>') v)))) = 
          \<F>' (recolor G (individualize (\<R>' G \<nu>') v))"
    by (smt (verit, ccfv_SIG) \<F>_length \<R>_length' \<open>is_vertex_list G \<nu>\<close> individualize_length is_vertex_list_cons(1) is_vertex_list_cons(3) local.Cons num_vertices_recolor recolor_\<F>' recolor_recolor)
  then show ?thesis
    unfolding is_split_def
    using Cons \<F>'_no_split
    by (smt (verit) \<R>'_Cons \<R>_finer \<open>is_vertex_list G \<nu>\<close> dual_order.strict_trans finer_strict_def num_colors_finer_strict)
qed

end


lemma split_by_prop_perm [simp]:
  assumes "\<forall> v < perm_dom p. f (perm_fun p v) = g v"
          "\<forall> x \<in> A. x < perm_dom p"
  shows "split_by_prop (perm_fun_set p A) f = 
        (perm_fun_set p) ` (split_by_prop A g)" (is "?lhs = ?rhs")
proof safe
  have *: "\<forall> x \<in> (perm_fun_set p A). x < perm_dom p"
    using assms(2)
    by (metis imageE perm_comp_perm_inv2 perm_dom_perm_inv perm_fun_perm_inv_range perm_fun_set_def perm_inv_solve)
  fix c
  assume "c \<in> ?lhs"
  then obtain x where "x \<in> perm_fun_set p A" "x < perm_dom p" "c = {x' \<in> perm_fun_set p A. f x' = f x}"
    using *
    unfolding split_by_prop_def
    by auto
  let ?y = "perm_fun (perm_inv p) x"
  have "?y < perm_dom p"
    using `x < perm_dom p`
    by (simp add: perm_fun_perm_inv_range)
  have "?y \<in> A"
    using `x \<in> perm_fun_set p A`
    using assms(2) perm_fun_set_def
    by fastforce
  let ?cy = "{y' \<in> A. g y' = g ?y}"
  have "?cy \<in> split_by_prop A g"
    using `?y \<in> A`
    unfolding split_by_prop_def
    by auto
  moreover have "perm_fun_set p ?cy = c"
  proof safe
    fix x'
    assume "x' \<in> perm_fun_set p ?cy"
    have "f x' = f x"
      using \<open>perm_fun (perm_inv p) x < perm_dom p\<close> \<open>x < perm_dom p\<close>
            \<open>x' \<in> perm_fun_set p ?cy\<close> assms(1) assms(2) perm_fun_set_def 
            by fastforce
    moreover have "x' \<in> perm_fun_set p A"
      using \<open>x' \<in> perm_fun_set p ?cy\<close> perm_fun_set_def by auto
    ultimately show "x' \<in> c"
      using `c = {x' \<in> perm_fun_set p A. f x' = f x}`
      by auto
  next
    fix x'
    assume "x' \<in> c"
    then have "x' \<in> perm_fun_set p A" "f x' = f x"
      using `c = {x' \<in> perm_fun_set p A. f x' = f x}`
      by auto
    let ?y' = "perm_fun (perm_inv p) x'"
    have "perm_fun p ?y' = x'"
      by (simp add: "*" \<open>x' \<in> perm_fun_set p A\<close>)
    moreover have "?y' \<in> ?cy"
      using \<open>f x' = f x\<close> \<open>perm_fun (perm_inv p) x < perm_dom p\<close> \<open>x < perm_dom p\<close> \<open>x' \<in> perm_fun_set p A\<close> assms(1) assms(2) perm_fun_set_def by fastforce
    ultimately show "x' \<in> perm_fun_set p ?cy"
      by (simp add: perm_fun_set_def rev_image_eqI)
  qed
  ultimately show "c \<in> ?rhs"
    by auto
next
  fix c
  assume "c \<in> split_by_prop A g"
  then obtain x where "x \<in> A" "c = {x' \<in> A . g x' = g x}"
    unfolding split_by_prop_def
    by auto
  
  let ?y = "perm_fun p x"
  have "f ?y = g x"
    using \<open>x \<in> A\<close> assms
    by auto
  let ?cy = "{y' \<in> (perm_fun_set p A) . f y' = f ?y}"
  have "?cy \<in> split_by_prop (perm_fun_set p A) f"
    using \<open>x \<in> A\<close> perm_fun_set_def split_by_prop_def
    by fastforce
  moreover
  have "perm_fun_set p c = ?cy"
  proof safe
    fix y'
    assume "y' \<in> perm_fun_set p c"
    show "y' \<in> perm_fun_set p A"
      using \<open>y' \<in> perm_fun_set p c\<close> perm_fun_set_def \<open>c = {x' \<in> A . g x' = g x}\<close>
      by auto
  next
    fix y'
    assume "y' \<in> perm_fun_set p c"
    show "f y' = f (perm_fun p x)"
      using \<open>c = {x' \<in> A. g x' = g x}\<close> \<open>f (perm_fun p x) = g x\<close> \<open>y' \<in> perm_fun_set p c\<close> assms(1) assms(2) perm_fun_set_def
      by auto
  next
    fix y'
    assume "y' \<in> perm_fun_set p A" "f y' = f (perm_fun p x)"
    show "y' \<in> perm_fun_set p c"
      using \<open>c = {x' \<in> A. g x' = g x}\<close> \<open>f y' = f (perm_fun p x)\<close> \<open>x \<in> A\<close> \<open>y' \<in> perm_fun_set p A\<close> assms(1) assms(2) perm_fun_set_def
      by auto
  qed
  ultimately
  show "perm_fun_set p c \<in> split_by_prop (perm_fun_set p A) f"
    by auto
qed


locale split_and_order = 
   fixes order_cells :: "colored_graph \<Rightarrow> vertex set \<Rightarrow> vertex set set \<Rightarrow> vertex set list"
   fixes split_by :: "colored_graph \<Rightarrow> vertex set \<Rightarrow> vertex  \<Rightarrow> 'a"
   assumes order_cells_set [simp]: 
      "\<And> G by_cell cs. finite cs \<Longrightarrow> set (order_cells G by_cell cs) = cs"
   assumes order_cells_distinct [simp]: 
      "\<And> G by_cell cs. finite cs \<Longrightarrow> distinct (order_cells G by_cell cs)"
   assumes order_cells_perm [simp]:
      "\<And> G p by_cell cs. \<lbrakk> 
          perm_dom p = num_vertices G; by_cell \<subseteq> {0..<perm_dom p}; \<Union> cs \<subseteq> {0..<perm_dom p};
          is_split_by_prop cs (split_by G by_cell)
       \<rbrakk> \<Longrightarrow>
         order_cells (perm_graph p G) (perm_fun_set p by_cell) ((perm_fun_set p) ` cs) =
         map (\<lambda> c. perm_fun_set p c) (order_cells G by_cell cs)"
   assumes split_by_perm [simp]:
      "\<And> G p by_cell v. \<lbrakk> perm_dom p = num_vertices G; by_cell \<subseteq> {0..<perm_dom p}; v < perm_dom p\<rbrakk> \<Longrightarrow>
         split_by (perm_graph p G) (perm_fun_set p by_cell) (perm_fun p v) = 
         split_by G by_cell v"
begin

lemma order_cells_length [simp]:
  assumes "finite cs"
  shows "List.length (order_cells G by_cell cs) = card cs"
  using assms
  by (metis distinct_card order_cells_distinct order_cells_set) 

definition split_cell :: "colored_graph \<Rightarrow> vertex set \<Rightarrow> vertex set \<Rightarrow> vertex set list" where
  "split_cell G by_cell splitting_cell = 
     order_cells G by_cell (split_by_prop splitting_cell (\<lambda> v. split_by G by_cell v))"

lemma split_cell_nonempty [simp]:
  assumes "finite splitting_cell"
  shows "{} \<notin> set (split_cell G by_cell splitting_cell)"
  using assms
  unfolding split_cell_def
  by simp

lemma split_cell_set [simp]:
  assumes "finite splitting_cell"
  shows "\<Union> (set (split_cell G by_cell splitting_cell)) = splitting_cell"
  using assms
  unfolding split_cell_def
  by simp

lemma in_concat_nth:
  assumes "i < List.length (concat xs)"
  shows "\<exists> i'. i' < List.length xs \<and> (concat xs) ! i \<in> set (xs ! i')"
proof-
  have "(concat xs) ! i \<in> set (concat xs)"
    using assms
    by (meson in_set_conv_nth) 
  then show ?thesis
    using set_concat using index_of_in_set
    by fastforce 
qed

lemma split_cell_disjoint:
  assumes "finite splitting_cell"
  assumes "i < List.length (split_cell G by_cell splitting_cell)"
          "j < List.length (split_cell G by_cell splitting_cell)" "i \<noteq> j"
  shows "split_cell G by_cell splitting_cell ! i \<inter> split_cell G by_cell splitting_cell ! j = {}"
  using assms
  unfolding split_cell_def
  by (metis nth_eq_iff_index_eq nth_mem order_cells_distinct order_cells_set split_by_prop_disjoint split_by_prop_finite)

lemma split_cell_distinct:
  assumes "finite splitting_cell"
  shows "distinct (split_cell G by_cell splitting_cell)"
  using assms
  unfolding split_cell_def
  by simp

lemma split_cell_subset:
  assumes "finite splitting_cell"
  assumes "new_cell \<in> set (split_cell G by_cell splitting_cell)"
  shows "new_cell \<subseteq> splitting_cell"
  by (metis assms(1) assms(2) mem_simps(9) split_cell_set subset_iff)

lemma split_cells_distinct:
  assumes "cells_ok (num_vertices G) cs" "c < num_colors G"
  shows "distinct (concat (map (split_cell G (cs ! c)) cs))"
proof (rule distinct_concat)
  show "distinct (map (split_cell G (cs ! c)) cs)"
  proof (subst distinct_map, safe)
    show "distinct cs" 
      using `cells_ok (num_vertices G) cs`
      unfolding cells_ok_def
      by (metis distinct_conv_nth inf_idem nth_mem)
    then show "inj_on (split_cell G (cs ! c)) (set cs)"
      using `cells_ok (num_vertices G) cs`
      unfolding inj_on_def
      by (metis cells_ok_finite split_cell_set) 
  qed
next
  fix ys
  assume "ys \<in> set (map (split_cell G (cs ! c)) cs)"
  then show "distinct ys"
    using `cells_ok (num_vertices G) cs`
    by (auto simp add: split_cell_distinct)
next
  fix ys zs
  assume "ys \<in> set (map (split_cell G (cs ! c)) cs)" 
         "zs \<in> set (map (split_cell G (cs ! c)) cs)" 
         "ys \<noteq> zs"
  then obtain c1 c2 where
    *: "c1 \<in> set cs" "c2 \<in> set cs" "c1 \<noteq> c2" "finite c1" "finite c2"
       "ys = split_cell G (cs ! c) c1" "zs = split_cell G (cs ! c) c2"
    using `cells_ok (num_vertices G) cs`
    by auto

  have "c1 \<inter> c2 = {}"
    using `cells_ok (num_vertices G) cs`
    unfolding cells_ok_def
    by (metis `c1 \<in> set cs` `c2 \<in> set cs` `c1 \<noteq> c2` in_set_conv_nth)

  show "set ys \<inter> set zs = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain cc where "cc \<in> set ys" "cc \<in> set zs"
      by auto
    then have "cc \<subseteq> c1" "cc \<subseteq> c2"
      using split_cell_set[of c1 G "cs ! c"]
      using split_cell_set[of c2 G "cs ! c"]
      using *
      by blast+
    then have "cc = {}"
      using `c1 \<inter> c2 = {}`
      by blast
    then show False
      using `cc \<in> set ys` *
      by simp
  qed
qed

lemma split_cells_OK:
  assumes "cells_ok (num_vertices G) cs" "c < num_colors G"
  shows "cells_ok (num_vertices G) (concat (map (split_cell G (cs ! c)) cs))" (is "cells_ok ?n ?cs")
unfolding cells_ok_def
proof safe
  assume "{} \<in> set ?cs"
  then show False
    using assms
    by (auto simp add: split_cell_def)
next
  fix i j v
  assume "i < List.length ?cs" "j < List.length ?cs" "i \<noteq> j" 
         "v \<in> ?cs ! i" "v \<in> ?cs ! j"
  then obtain i' j' where *:
    "i' < List.length cs" "?cs ! i \<in> set (split_cell G (cs ! c) (cs ! i'))"
    "j' < List.length cs" "?cs ! j \<in> set (split_cell G (cs ! c) (cs ! j'))"
    using in_concat_nth
    by (metis (no_types, lifting) length_map nth_map) 
  then have "v \<in> cs ! i'" "v \<in> cs ! j'"
    using `v \<in> ?cs ! i` `v \<in> ?cs ! j` assms
    by (metis UnionI cells_ok_finite nth_mem split_cell_set)+
  show "v \<in> {}"
  proof (cases "i' = j'")
    case True
    then obtain i'' j'' where **:
      "i'' < List.length (split_cell G (cs ! c) (cs ! i'))" 
      "?cs ! i = (split_cell G (cs ! c) (cs ! i')) ! i''"
      "j'' < List.length (split_cell G (cs ! c) (cs ! i'))" 
      "?cs ! j = (split_cell G (cs ! c) (cs ! i')) ! j''"
      using *
      by (metis in_set_conv_nth)
    moreover have "i'' \<noteq> j''"
      using `i \<noteq> j` ** split_cells_distinct[OF assms] `i < List.length ?cs` `j < List.length ?cs`
      using nth_eq_iff_index_eq 
      by blast
    ultimately have "?cs ! i \<inter> ?cs ! j = {}"
      using split_cell_disjoint assms
       by (simp add: "*"(1))
    then have False
      using `v \<in> ?cs ! i` `v \<in> ?cs ! j` 
      by auto      
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using `v \<in> cs ! i'` `v \<in> cs ! j'` `i' < List.length cs` `j' < List.length cs`
            `cells_ok (num_vertices G) cs`
      unfolding cells_ok_def
      by auto
  qed
next
  fix v C
  assume "C \<in> set (concat (map (split_cell G (cs ! c)) cs))" "v \<in> C"
  then have "C \<subseteq> \<Union> (set cs)"
    using `c < num_colors G` split_cell_set[of _ G "cs ! c"] assms
    by (smt (verit, best) index_of_in_set Sup_upper2 Union_upper cells_ok_finite in_concat_nth length_map nth_map nth_mem) 
  then show "v \<in> {0..<num_vertices G}"
    using `v \<in> C` `cells_ok (num_vertices G) cs`
    unfolding cells_ok_def
    by auto
next
  fix v
  assume "v \<in> {0..<num_vertices G}"
  then obtain i where "i < List.length cs" "v \<in> cs ! i"
    using `cells_ok (num_vertices G) cs`
    unfolding cells_ok_def
    by (metis Union_iff in_set_conv_nth)
  then have "v \<in> \<Union> (set (split_cell G (cs ! c) (cs ! i)))"
    using split_cell_set assms
    by auto
  then have "\<exists>x\<in>set (split_cell G (cs ! c) (cs ! i)). v \<in> x"
    by blast
  then have "\<exists>y\<in>set cs. \<exists>x\<in>set (split_cell G (cs ! c) y). v \<in> x"
    using `i < List.length cs`
    by auto
  then show "v \<in> \<Union> (set (concat (map (split_cell G (cs ! c)) cs)))"
    by auto
qed


definition split :: "colored_graph \<Rightarrow> color \<Rightarrow> coloring" where
  "split G c = (
    let cs = cells (colors G);
        new_cs = concat (map (split_cell G (cs ! c)) cs)
     in cells_to_coloring (num_vertices G) new_cs
  )"

lemma split_length_imp [simp]:
  assumes "c < num_colors G"
  shows "length (split G c) = num_vertices G"
  unfolding split_def Let_def
  using split_cells_OK cells_ok
  by (metis assms length_cells_to_coloring length_colors_num_vertices)

lemma split_cell_perm [simp]:
  assumes "\<forall>x\<in>splitting_cell. x < perm_dom p" "perm_dom p = num_vertices G" "by_cell \<subseteq> {0..<perm_dom p}"
  shows "split_cell (perm_graph p G) (perm_fun_set p by_cell) (perm_fun_set p splitting_cell) = 
         map (perm_fun_set p) (split_cell G by_cell splitting_cell)"
proof-
  let ?f = "split_by (perm_graph p G) (perm_fun_set p by_cell)"
  let ?g = "split_by G by_cell"
  let ?pG = "perm_graph p G"
  let ?pC = "split_by_prop (perm_fun_set p splitting_cell) ?f"
  have *:"?pC = perm_fun_set p ` split_by_prop splitting_cell ?g"
  proof (subst split_by_prop_perm)
    show "\<forall>v<perm_dom p. ?f (perm_fun p v) = ?g v"
      using split_by_perm assms
      by auto
  next
    show "\<forall>x\<in>splitting_cell. x < perm_dom p"
    by fact
  qed simp
  then show ?thesis
    using assms order_cells_perm split_by_prop_is_split_by_prop
    unfolding split_cell_def
    by (metis nth_mem perm_dom.rep_eq perm_fun_perm_inv1 perm_fun_perm_inv_range perm_list_nth perm_list_set split_by_prop_set subset_eq)
qed


definition is_split_by :: "colored_graph \<Rightarrow> coloring \<Rightarrow> bool" where
 "is_split_by G \<pi> \<longleftrightarrow> (\<forall>c1 < Coloring.num_colors \<pi>. \<forall> c2 < Coloring.num_colors \<pi>. \<forall> v1 \<in> cell \<pi> c2. \<forall> v2 \<in> cell \<pi> c2. 
                        split_by (recolor G \<pi>) (cell \<pi> c1) v1 = split_by (recolor G \<pi>) (cell \<pi> c1) v2)" 

end


sublocale split_and_order \<subseteq> split split
proof
fix G c
assume "c < num_colors G"
then show "length (split G c) = length (colors G)"
  by simp
next
  fix G c
  assume "c < num_colors G" 
  show "finer (split G c) (colors G)"
  proof (rule cell_subset_finer)
    show "length (split G c) = length (colors G)"
      using `c < num_colors G`
      by simp
  next
    show "\<forall>C'\<in>set (cells (split G c)). \<exists>C\<in>set (cells (colors G)). C' \<subseteq> C"
    proof
      fix C'
      assume "C' \<in> set (cells (split G c))"
      then obtain cc where "cc \<in> set (cells (colors G))" 
         "C' \<in> set (split_cell G (cells (colors G) ! c) cc)"
        unfolding split_def Let_def
        by (smt (verit, ccfv_SIG) More_List.index_of_in_set \<open>c < ColoredGraph.num_colors G\<close> cells_cells_to_coloring cells_ok in_concat_nth length_colors_num_vertices length_map nth_map nth_mem split_cells_OK)
      then show "\<exists>C\<in>set (cells (colors G)). C' \<subseteq> C"
        by (metis Sup_upper cells_ok cells_ok_finite split_cell_set)
    qed
  next
    show "\<forall>p1 p2 c1 c2. c1 < Coloring.num_colors (local.split G c) \<and>
                        p1 < ColoredGraph.num_colors G \<and>
                        c2 < Coloring.num_colors (local.split G c) \<and>
                        p2 < ColoredGraph.num_colors G \<and>
                        cell (split G c) c1 \<subseteq> cell (colors G) p1 \<and> 
                        cell (split G c) c2 \<subseteq> cell (colors G) p2 \<and>
                        c1 \<le> c2 \<longrightarrow> p1 \<le> p2"
    proof safe
      fix p1 p2 c1 c2
      assume "c1 < Coloring.num_colors (split G c)" "c2 < Coloring.num_colors (split G c)"
             "p1 < num_colors G" "p2 < num_colors G"

      let ?lp = "cells (colors G)"
      let ?lc = "cells (split G c)"

      assume *: "cell (split G c) c1 \<subseteq> cell (colors G) p1"
                "cell (split G c) c2 \<subseteq> cell (colors G) p2"
                "c1 \<le> c2"

      have "cell (split G c) c1 = ?lc ! c1"
           "cell (split G c) c2 = ?lc ! c2"
        using \<open>c1 < Coloring.num_colors (split G c)\<close> \<open>c2 < Coloring.num_colors (split G c)\<close> cells_def nth_cells
        by presburger+

      have "cell (colors G) p1 = ?lp ! p1"
           "cell (colors G) p2 = ?lp ! p2"
        using \<open>p1 < num_colors G\<close> \<open>p2 < num_colors G\<close> cells_def nth_cells
        by presburger+

      let ?f = "split_cell G (?lp ! c)"

      let ?lm = "map ?f ?lp"

      have cc: "?lc = concat ?lm"
        by (metis \<open>c < num_colors G\<close> cells_cells_to_coloring cells_ok length_colors_num_vertices local.split_def split_and_order.split_cells_OK split_and_order_axioms)

      then have "distinct ?lc"
        by (metis \<open>c < num_colors G\<close> cells_ok length_colors_num_vertices split_cells_distinct)

      have "p1 < List.length ?lm" "p2 < List.length ?lm"
        using `p1 < num_colors G` `p2 < num_colors G`
        by auto

      let ?x1 = "?lc ! c1"
      have "?x1 \<subseteq> ?lp ! p1"
        using *(1) `cell (colors G) p1 = ?lp ! p1` `cell (split G c) c1 = ?lc ! c1`
        by simp
      then have "?x1 \<in> set (?lm ! p1)"
      proof-
        obtain px1 where "?x1 \<in> set (?lm ! px1)" "px1 < List.length ?lm"
          by (metis \<open>c1 < Coloring.num_colors (local.split G c)\<close> cc in_concat_nth length_cells)
        then have "?x1 \<subseteq> ?lp ! px1"
          using List.nth_map split_cell_subset `px1 < List.length ?lm`
          by auto

        have "cells_ok (length (colors G)) (cells (colors G))"
          using cells_ok by blast
        then have "px1 = p1"
          using `?x1 \<subseteq> ?lp ! px1` `?x1 \<subseteq> ?lp ! p1`
          by (smt (verit, best) \<open>c1 < Coloring.num_colors (split G c)\<close> \<open>cell (split G c) c1 = ?lc ! c1\<close> \<open>p1 < ColoredGraph.num_colors G\<close> \<open>px1 < List.length ?lm\<close> boolean_algebra.conj_zero_right cell_non_empty cells_disjunct inf.absorb_iff2 inf.orderE inf_left_commute length_cells length_map)
        then show "?x1 \<in> set (?lm ! p1)"
          using `?x1 \<in> set (?lm ! px1)`
          by auto
      qed
      then obtain k1 where "k1 < List.length (?lm ! p1)" "?x1 = (?lm ! p1) ! k1"
        by (metis in_set_conv_nth)

      let ?i1 = "concat_prefix_length ?lm p1 + k1"
      have "?i1 < List.length ?lc"
      proof-
        have "?i1 < concat_prefix_length ?lm (p1 + 1)"
          using `k1 < List.length (?lm ! p1)` `p1 < List.length ?lm`
          by (metis add_less_cancel_left concat_prefix_length_Suc)
        then show ?thesis
          using cc concat_prefix_length_ub order_less_le_trans
          by fastforce
      qed
      have "?lc ! ?i1 = ?x1"
        using `p1 < List.length ?lm` `k1 < List.length (?lm ! p1)` `?x1 = (?lm ! p1) ! k1`
        by (metis cc concat_in_nth_list)
      then have "c1 = ?i1"
        using nth_eq_iff_index_eq `distinct ?lc` `?i1 < List.length ?lc` \<open>c1 < Coloring.num_colors (local.split G c)\<close> 
        by (metis length_cells)

      let ?x2 = "?lc ! c2"
      have "?x2 \<subseteq> ?lp ! p2"
        using *(2) `cell (colors G) p2 = ?lp ! p2` `cell (split G c) c2 = ?lc ! c2`
        by simp
      have "?x2 \<in> set (?lm ! p2)"
      proof-
        obtain px2 where "?x2 \<in> set (?lm ! px2)" "px2 < List.length ?lm"
          by (metis \<open>c2 < Coloring.num_colors (local.split G c)\<close> cc in_concat_nth length_cells)
        then have "?x2 \<subseteq> ?lp ! px2"
          using List.nth_map split_cell_subset `px2 < List.length ?lm`
          by auto

        have "cells_ok (length (colors G)) (cells (colors G))"
          using cells_ok by blast
        then have "px2 = p2"
          using `?x2 \<subseteq> ?lp ! px2` `?x2 \<subseteq> ?lp ! p2`
          by (smt (verit, best) \<open>c2 < Coloring.num_colors (split G c)\<close> \<open>cell (split G c) c2 = ?lc ! c2\<close> \<open>p2 < ColoredGraph.num_colors G\<close> \<open>px2 < List.length ?lm\<close> boolean_algebra.conj_zero_right cell_non_empty cells_disjunct inf.absorb_iff2 inf.orderE inf_left_commute length_cells length_map)
        then show "?x2 \<in> set (?lm ! p2)"
          using `?x2 \<in> set (?lm ! px2)`
          by auto
      qed
      then obtain k2 where "k2 < List.length (?lm ! p2)" "?x2 = (?lm ! p2) ! k2"
        by (metis in_set_conv_nth)

      let ?i2 = "concat_prefix_length ?lm p2 + k2"
      have "?i2 < List.length ?lc"
      proof-
        have "?i2 < concat_prefix_length ?lm (p2 + 1)"
          using `k2 < List.length (?lm ! p2)` `p2 < List.length ?lm`
          by (metis add_less_cancel_left concat_prefix_length_Suc)
        then show ?thesis
          using cc concat_prefix_length_ub order_less_le_trans
          by fastforce
      qed
      have "?lc ! ?i2 = ?x2"
        using `p2 < List.length ?lm` `k2 < List.length (?lm ! p2)` `?x2 = (?lm ! p2) ! k2`
        by (metis cc concat_in_nth_list)
      then have "c2 = ?i2"
        using nth_eq_iff_index_eq `distinct ?lc` `?i2 < List.length ?lc` \<open>c2 < Coloring.num_colors (local.split G c)\<close> 
        by (metis length_cells)

      show "p1 \<le> p2"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "p1 > p2"
          by auto
        have "c2 < concat_prefix_length ?lm p2 + List.length (?lm ! p2)"
          using `c2 = ?i2` `k2 < List.length (?lm ! p2)`
          by auto
        also have "... = concat_prefix_length ?lm (p2 + 1)"
          by (metis \<open>p2 < List.length ?lm\<close> concat_prefix_length_Suc)
        also have "... \<le> concat_prefix_length ?lm p1"
          using `p1 > p2`
          by (metis Suc_eq_plus1 leI length_prefix_mono not_less_eq)
        also have "... \<le> c1"
          using `c1 = ?i1`
          by auto
        finally
        show False
          using `c1 \<le> c2`
          by auto
      qed
    qed
  qed
next
  fix p G c
  assume "c < num_colors G" "perm_dom p = num_vertices G"
  show "split (perm_graph p G) c = perm_coloring p (split G c)"
  proof-
    let ?pG = "perm_graph p G"
    let ?n = "num_vertices G"
    let ?csp = "cells (colors ?pG)"
    let ?new_csp = "concat (map (split_cell ?pG (?csp ! c)) ?csp)"
    let ?cs = "cells (colors G)"
    let ?new_cs = "concat (map (split_cell G (?cs ! c)) ?cs)"
    let ?split = "cells_to_coloring (num_vertices G) ?new_cs"
    let ?splitp = "cells_to_coloring (num_vertices G) ?new_csp"
    let ?ps = "perm_fun_set p"

    have ok: "cells_ok (num_vertices G) ?new_cs"
      using \<open>c < num_colors G\<close>
      by (metis cells_ok length_colors_num_vertices split_cells_OK)     

    have *: "?csp =  map (perm_fun_set p) ?cs"
      using cells_perm_graph `perm_dom p = num_vertices G`
      by simp
    have "map (split_cell ?pG (map ?ps ?cs ! c) \<circ> ?ps) ?cs = 
          map (map (perm_fun_set p) \<circ> split_cell G (?cs ! c)) ?cs"
    proof (subst map_eq_conv, safe)
      fix x
      assume "x \<in> set (?cs)"  
      then have "\<forall>x\<in>x. x < perm_dom p"
        using cell_def cells_def `perm_dom p = num_vertices G` 
        by fastforce 
      show "(split_cell ?pG (map ?ps ?cs ! c) \<circ> ?ps) x = 
            (map (perm_fun_set p) \<circ> split_cell G (?cs ! c)) x" (is "?lhs = ?rhs")
      proof-
        have "c < List.length ?cs"
          using `c < num_colors G`
          using `perm_dom p = num_vertices G` length_cells
          by force
        then have "map ?ps ?cs ! c = ?ps (?cs ! c)"
          by auto
        then have "?lhs = split_cell ?pG (?ps (?cs ! c)) (?ps x)"
          by simp
        also have "... = map ?ps (split_cell G (?cs ! c) x)"
          using \<open>\<forall>x\<in>x. x < perm_dom p\<close> split_cell_perm `perm_dom p = num_vertices G` 
          by (metis Sup_upper \<open>c < List.length (cells (colors G))\<close> cells_ok cells_ok_def length_colors_num_vertices nth_mem)
        finally show ?thesis
          by simp
      qed
    qed
    then have new_csp: "?new_csp = map (perm_fun_set p) ?new_cs"
      using * cells_perm_graph[OF `perm_dom p = num_vertices G`]
      by (metis map_concat map_map)
    then have "cells_to_coloring ?n ?new_csp = perm_coloring p (cells_to_coloring ?n ?new_cs)"
      using `perm_dom p = num_vertices G` ok
      by (subst new_csp) (rule cells_to_coloring_perm, auto) 
    then have "?splitp = perm_coloring p ?split"
      using `perm_dom p = num_vertices G`
      by auto
    then show ?thesis
      unfolding split_def Let_def
      using `perm_dom p = num_vertices G`
      by simp
  qed
qed

context split_and_order
begin

lemma is_split_by_split_by:
  assumes "length \<pi> = num_vertices G"
  shows "is_split_by G \<pi> \<longleftrightarrow> is_split G \<pi>"
proof-
  let ?invar = "\<lambda> G \<pi>. (\<forall>j < Coloring.num_colors \<pi>. \<forall> splitting_cell \<in> set (cells \<pi>). 
                       split_by_prop splitting_cell (split_by (recolor G \<pi>) (cell \<pi> j)) = {splitting_cell})" 
  have "?invar G \<pi> \<longleftrightarrow> is_split G \<pi>"
  proof
    assume "?invar G \<pi>"
    show "is_split G \<pi>"
      unfolding is_split_def
    proof safe
      fix j
      assume "j < Coloring.num_colors \<pi>"
      assume "split (recolor G \<pi>) j \<prec> \<pi>"
      moreover
      have "\<forall> splitting_cell \<in> set (cells \<pi>). List.length (split_cell (recolor G \<pi>) (cell \<pi> j) splitting_cell) = 1"
        using `?invar G \<pi>` `j < Coloring.num_colors \<pi>`
        unfolding is_split_by_def split_cell_def
        by auto
      then have *: "sum_list (map (List.length \<circ> split_cell (recolor G \<pi>) (cells \<pi> ! j)) (cells \<pi>)) = List.length (cells \<pi>)"
        using sum_list_const[where L="cells \<pi>" and y=1] \<open>j < Coloring.num_colors \<pi>\<close>
        by simp
      then have "Coloring.num_colors (split (recolor G \<pi>) j) = Coloring.num_colors \<pi>"
        unfolding split_def Let_def
        by (metis List.map.compositionality \<open>j < Coloring.num_colors \<pi>\<close> assms cells_ok colors_recolor length_cells length_concat num_colors_cells_to_coloring num_vertices_recolor split_and_order.split_cells_OK split_and_order_axioms)
      ultimately show False
        using num_colors_finer_strict 
        by force
    qed
  next
    assume "is_split G \<pi>"
    show "?invar G \<pi>"
      unfolding is_split_def
    proof (rule, rule, rule)
      fix j splitting_cell
      assume "j < Coloring.num_colors \<pi>" "splitting_cell \<in> set (cells \<pi>)"
      have "split (recolor G \<pi>) j = \<pi>"
        using `is_split G \<pi>` `j < Coloring.num_colors \<pi>` split_finer[of j "recolor G \<pi>"] assms
        unfolding is_split_def finer_strict_def
        by auto
      let ?s = "\<lambda> splitting_cell. split_cell (recolor G \<pi>) (cell \<pi> j) splitting_cell"
      have "List.length (?s splitting_cell) = 1"
      proof (rule concat_nonempty_singletons)
        show "List.length (concat (map ?s (cells \<pi>))) = 
              List.length (map ?s (cells \<pi>))"
          using `split (recolor G \<pi>) j = \<pi>`
          unfolding split_def Let_def
          by (metis \<open>j < Coloring.num_colors \<pi>\<close> assms cells_ok colors_recolor length_cells length_map nth_cells num_colors_cells_to_coloring num_vertices_recolor split_and_order.split_cells_OK split_and_order_axioms)
      next
        show "\<forall> x \<in> set (map ?s (cells \<pi>)). x \<noteq> []"
        proof safe
          assume "[] \<in> set (map ?s (cells \<pi>))"
          then obtain splitting_cell' where 
            "splitting_cell' \<in> set (cells \<pi>)" "split_by_prop splitting_cell' (split_by (recolor G \<pi>) (cell \<pi> j)) = {}"
            unfolding split_cell_def
            by (smt (verit, ccfv_threshold) cells_ok cells_ok_finite empty_set in_set_conv_nth length_map nth_map order_cells_set split_by_prop_finite)
          then show False
            by (metis UnionE all_not_in_conv cells_non_empty split_by_prop_set)
        qed
      next
        show "?s splitting_cell \<in> set (map ?s (cells \<pi>))"
          using `splitting_cell \<in> set (cells \<pi>)`
          by auto
      qed
      then have "is_singleton (split_by_prop splitting_cell (split_by (recolor G \<pi>) (cell \<pi> j)))"
        by (metis \<open>splitting_cell \<in> set (cells \<pi>)\<close> cells_ok cells_ok_finite is_singleton_altdef order_cells_length split_and_order.split_cell_def split_and_order_axioms split_by_prop_finite)
      then show "split_by_prop splitting_cell (split_by (recolor G \<pi>) (cell \<pi> j)) = {splitting_cell}"
        unfolding split_cell_def
        by (metis ccpo_Sup_singleton is_singleton_the_elem split_by_prop_set)
    qed
  qed
  moreover
  have "?invar G \<pi> \<longleftrightarrow> is_split_by G \<pi>"
  proof
    assume *: "?invar G \<pi>"
    show "is_split_by G \<pi>"
      unfolding is_split_by_def
    proof safe
      fix c1 c2 v1 v2
      assume "c1 < Coloring.num_colors \<pi>" "c2 < Coloring.num_colors \<pi>" "v1 \<in> cell \<pi> c2" "v2 \<in> cell \<pi> c2"
      then show "split_by (recolor G \<pi>) (cell \<pi> c1) v1 = split_by (recolor G \<pi>) (cell \<pi> c1) v2"
        using *[rule_format, of c2 "cell \<pi> c1"]
        by (metis "*" cell_non_empty in_set_conv_nth length_cells nth_cells split_by_prop_singleton)
    qed
  next
    assume "is_split_by G \<pi>"
    show "?invar G \<pi>"
    proof (rule, rule, rule)
      fix j splitting_cell
      assume "j < Coloring.num_colors \<pi>" "splitting_cell \<in> set (cells \<pi>)"
      then show "split_by_prop splitting_cell (split_by (recolor G \<pi>) (cell \<pi> j)) = {splitting_cell}"
        using `is_split_by G \<pi>`
        unfolding is_split_by_def
        by (smt (verit) cells_non_empty distinct_Ex1 distinct_cells length_cells nth_cells split_by_prop_singleton)
    qed
  qed
  ultimately
  show ?thesis
    by blast
qed

lemma is_split_by:
  assumes "is_vertex_list G \<nu>"
  shows "is_split_by G (\<R>' G \<nu>)"
  using assms
  by (simp add: is_split is_split_by_split_by)

end


text\<open>count edges between a node and a set of nodes\<close>
definition node_deg_set :: "colored_graph \<Rightarrow> vertex set \<Rightarrow> vertex \<Rightarrow> nat" where
 "node_deg_set G Vc v = card {(v1, v2) \<in> edges G. v1 = v \<and> v2 \<in> Vc}"

lemma node_deg_set_perm [simp]:
  assumes "perm_dom p = num_vertices G" "by_cell \<subseteq> {0..<perm_dom p}" "v < perm_dom p"
  shows "node_deg_set (perm_graph p G) (perm_fun_set p by_cell) (perm_fun p v) = node_deg_set G by_cell v"
proof-
  have "bij_betw (perm_fun_pair p) {(v1, v2). (v1, v2) \<in> edges G \<and> v1 = v \<and> v2 \<in> by_cell} {(v1, v2). (v1, v2) \<in> edges (perm_graph p G) \<and> v1 = perm_fun p v \<and> v2 \<in> perm_fun_set p by_cell}" (is "bij_betw ?p ?A ?B")
    unfolding bij_betw_def inj_on_def
  proof safe
    fix w w'
    assume "(v, w) \<in> edges G" "(v, w') \<in> edges G" "perm_fun_pair p (v, w) = perm_fun_pair p (v, w')"
    then show "w = w'"
      by (metis \<open>perm_dom p = num_vertices G\<close> edge_vertices(2) perm_fun_inj perm_fun_pair_def prod.sel(2))
  next
    fix w pv pw
    assume "(pv, pw) = perm_fun_pair p (v, w)" "(v, w) \<in> edges G" 
    then show "(pv, pw) \<in> edges (perm_graph p G)"
      using \<open>perm_dom p = num_vertices G\<close> image_iff perm_edges_def 
      by fastforce
  next
    fix w pv pw
    assume "(pv, pw) = perm_fun_pair p (v, w)" "(v, w) \<in> edges G" 
    then show "pv = perm_fun p v"
      by simp
  next
    fix w pv pw
    assume "(pv, pw) = perm_fun_pair p (v, w)" "(v, w) \<in> edges G" "w \<in> by_cell"
    then show "pw \<in> perm_fun_set p by_cell"
      by (simp add: perm_fun_set_def)
  next
    fix pw
    assume *: "(perm_fun p v, pw) \<in> edges (perm_graph p G)" "pw \<in> perm_fun_set p by_cell" 
    then obtain w where "w \<in> by_cell" "pw = perm_fun p w"
      using perm_fun_set_def
      by auto
    have "vertex G w" "vertex G v"
      using `w \<in> by_cell` `by_cell \<subseteq> {0..<perm_dom p}` `perm_dom p = num_vertices G` `v < perm_dom p`
      by auto
    then have "(v, w) \<in> edges G" "perm_fun_pair p (v, w) = (perm_fun p v, pw)" 
      using `perm_dom p = num_vertices G` * \<open>pw = perm_fun p w\<close> edges_perm_graph_perm 
      by auto

    then show "(perm_fun p v, pw) \<in> perm_fun_pair p ` {(v1, v2). (v1, v2) \<in> edges G \<and> v1 = v \<and> v2 \<in> by_cell}"
      using \<open>pw = perm_fun p w\<close> `w \<in> by_cell`
      by (metis (mono_tags, lifting) case_prodI image_eqI mem_Collect_eq) 
  qed
  then show ?thesis
    using bij_betw_same_card
    unfolding node_deg_set_def
    by fastforce
qed

definition set_to_list :: "'a set \<Rightarrow> 'a list"
  where "set_to_list s = (SOME l. distinct l \<and> set l = s)"

lemma set_set_to_list:
  "finite s \<Longrightarrow> set (set_to_list s) = s"
  using finite_distinct_list[of s]
  unfolding set_to_list_def 
  by (smt (verit, best) tfl_some)
   
lemma distinct_set_to_list:
  "finite s \<Longrightarrow> distinct (set_to_list s)"
  using finite_distinct_list[of s]
  unfolding set_to_list_def 
  by (smt (verit, best) tfl_some)

definition order_cells_by_deg where 
  "order_cells_by_deg G by_cell cs =
     sort_key (\<lambda> cl. node_deg_set G by_cell (SOME v. v \<in> cl)) (set_to_list cs)"

lemma order_cells_by_deg_set [simp]:
  assumes "finite cs"
  shows "set (order_cells_by_deg G by_cell cs) = cs"
  using assms
  unfolding order_cells_by_deg_def
  by (simp add: set_set_to_list)

lemma order_cells_by_deg_distinct [simp]:
  assumes "finite cs"
  shows "distinct (order_cells_by_deg G by_cell cs)"
  using assms
  unfolding order_cells_by_deg_def
  by (simp add: distinct_set_to_list)

lemma sorted_by_deg_ordered_cells_by_deg [simp]:
  shows "sorted (map (\<lambda> cl. node_deg_set G by_cell (SOME v. v \<in> cl)) (order_cells_by_deg G by_cell cs))"
  unfolding order_cells_by_deg_def
  by auto

lemma order_cells_by_deg_perm [simp]:
  assumes "perm_dom p = num_vertices G" "by_cell \<subseteq> {0..<perm_dom p}"  "\<Union> cs \<subseteq> {0..<perm_dom p}"
          "\<forall> cl \<in> cs. \<forall> v1 \<in> cl. \<forall> v2 \<in> cl. node_deg_set G by_cell v1 = node_deg_set G by_cell v2"
          "\<forall> cl1 \<in> cs. \<forall> cl2 \<in> cs. \<forall> v1 \<in> cl1. \<forall> v2 \<in> cl2. cl1 \<noteq> cl2 \<longrightarrow> node_deg_set G by_cell v1 \<noteq> node_deg_set G by_cell v2"
          "\<forall> cl \<in> cs. cl \<noteq> {}"
  shows "order_cells_by_deg (perm_graph p G) (perm_fun_set p by_cell) (perm_fun_set p ` cs) =
         map (perm_fun_set p) (order_cells_by_deg G by_cell cs)" (is "?lhs = ?rhs")
proof (rule map_sorted_distinct_set_unique)
  let ?f = "(\<lambda> cl. node_deg_set G by_cell (SOME v. v \<in> cl))"
  let ?fp = "(\<lambda>cl. node_deg_set (perm_graph p G) (perm_fun_set p by_cell) (SOME v. v \<in> cl))"

  have "finite cs"
    using `\<Union> cs \<subseteq> {0..<perm_dom p}`
    by (simp add: finite_UnionD finite_subset)

  {
      fix cl
      assume "cl \<in> cs"
      have "?f cl = ?fp (perm_fun_set p cl)"
      proof-
        let ?s = "(SOME v. v \<in> perm_fun_set p cl)"
        have  "?s \<in> perm_fun_set p cl"
        proof-
          have "perm_fun_set p cl \<noteq> {}"
            using `\<forall> cl \<in> cs. cl \<noteq> {}` `cl \<in> cs`
            unfolding perm_fun_set_def
            by auto
          then show ?thesis
            by (simp add: some_in_eq)
        qed
        then obtain v where "v \<in> cl" and *: "?s = perm_fun p v"
          unfolding perm_fun_set_def
          by auto
        moreover
        have "vertex G (perm_fun p v)" "vertex G v"
          using  `\<Union> cs \<subseteq> {0..<perm_dom p}` `cl \<in> cs` `v \<in> cl` `perm_dom p = num_vertices G`
          by auto
        ultimately
        have "node_deg_set (perm_graph p G) (perm_fun_set p by_cell) ?s = 
              node_deg_set G by_cell v"
          using `perm_dom p = num_vertices G` `by_cell \<subseteq> {0..<perm_dom p}`
          using node_deg_set_perm
          by presburger
        also have "... = node_deg_set G by_cell (SOME v. v \<in> cl)"
        proof-
          have "(SOME v. v \<in> cl) \<in> cl"
            using `\<forall>cl\<in>cs. cl \<noteq> {}` \<open>cl \<in> cs\<close>
            by (simp add: some_in_eq)
          then show ?thesis
            using `v \<in> cl` `cl \<in> cs` `\<forall>cl\<in>cs. \<forall>v1\<in>cl. \<forall>v2\<in>cl. node_deg_set G by_cell v1 = node_deg_set G by_cell v2`
            by blast
        qed
        finally show ?thesis
          by simp
      qed
  }
  note * = this

  show "set ?lhs = set ?rhs"
    using `finite cs`
    by simp

  show "sorted (map ?fp ?lhs)"
    by simp
    
  show "inj_on ?fp (set ?lhs \<union> set ?rhs)"
  proof-
    have "inj_on ?fp (perm_fun_set p ` cs)"
      unfolding inj_on_def
    proof (rule, rule, rule)
      fix x y
      assume *: "x \<in> perm_fun_set p ` cs" "y \<in> perm_fun_set p ` cs" "?fp x = ?fp y"
      have "(SOME v. v \<in> x) \<in> x" "(SOME v. v \<in> y) \<in> y"
        using *(1-2) assms(6) perm_fun_set_def some_in_eq
        by (metis imageE image_is_empty)+
      obtain x' y' where "x' \<in> cs" "x = perm_fun_set p x'" "y' \<in> cs" "y = perm_fun_set p y'"
        using *(1-2)
        by auto
      then obtain v w where "v \<in> x'" "(SOME v. v \<in> x) = perm_fun p v" "w \<in> y'" "(SOME v. v \<in> y) = perm_fun p w"
        using `(SOME v. v \<in> x) \<in> x` `(SOME v. v \<in> y) \<in> y`
        by (auto simp add: perm_fun_set_def)
      then have "node_deg_set G by_cell v = node_deg_set G by_cell w"
        using *(3) assms \<open>x' \<in> cs\<close> \<open>y' \<in> cs\<close> 
        by (metis Union_upper atLeastLessThan_iff node_deg_set_perm subsetD)
      then have "x' = y'"
        using `v \<in> x'` `w \<in> y'` \<open>x' \<in> cs\<close> \<open>y' \<in> cs\<close>
        assms(5-6)
        by auto
      then show "x = y"
        using `x = perm_fun_set p x'` `y = perm_fun_set p y'`
        by simp
    qed
    then show ?thesis
      using `finite cs`
      by auto
  qed

  show "distinct (map ?fp ?lhs)"
  proof (subst distinct_map, safe)
    show "distinct ?lhs"
      using `finite cs`
      by simp
  next
    show "inj_on ?fp (set ?lhs)"
      using `inj_on ?fp (set ?lhs \<union> set ?rhs)`
      using inj_on_subset 
      by blast
  qed

  have **: "map ?fp ?rhs = map ?f (order_cells_by_deg G by_cell cs)"
    using * `finite cs`
    by auto

  show "sorted (map ?fp ?rhs)"
    by (subst **) auto
  
  show "distinct (map ?fp ?rhs)"
  proof (subst **, subst distinct_map, safe)
    show "distinct (order_cells_by_deg G by_cell cs)"
      using `finite cs`
      by auto
  next
    show "inj_on ?f (set (order_cells_by_deg G by_cell cs))"
    proof-
      have "inj_on ?f cs"
        unfolding inj_on_def
      proof (rule, rule, rule)
        fix x y
        assume *: "x \<in> cs" "y \<in> cs" "?f x = ?f y"
        then have "(SOME v. v \<in> x) \<in> x" "(SOME v. v \<in> y) \<in> y"
          using assms `\<forall>cl\<in>cs. cl \<noteq> {}` some_in_eq
          by metis+
        then show "x = y"
          using * assms
          by metis
      qed
      then show ?thesis
        using `finite cs`
        by auto
    qed
  qed
qed

interpretation so: split_and_order order_cells_by_deg node_deg_set
proof
  fix G p by_cell v
  assume "perm_dom p = num_vertices G" "by_cell \<subseteq> {0..<perm_dom p}" "v < perm_dom p"
  then show "node_deg_set (perm_graph p G) (perm_fun_set p by_cell) (perm_fun p v) = node_deg_set G by_cell v "
    by simp
next
  fix G :: colored_graph and by_cell :: "nat set" and cs :: "nat set set"
  assume "finite cs"
  then show "set (order_cells_by_deg G by_cell cs) = cs"
    by simp
next
  fix G :: colored_graph and by_cell :: "nat set" and cs :: "nat set set"
  assume "finite cs"
  then show "distinct (order_cells_by_deg G by_cell cs)"
    by simp
next
  fix G p by_cell cs
  assume *: "perm_dom p = num_vertices G" "by_cell \<subseteq> {0..<perm_dom p}"  "\<Union> cs \<subseteq> {0..<perm_dom p}" "is_split_by_prop cs (node_deg_set G by_cell)"
  then show "order_cells_by_deg (perm_graph p G) (perm_fun_set p by_cell) (perm_fun_set p ` cs) = map (perm_fun_set p) (order_cells_by_deg G by_cell cs)"
    by (smt (verit) is_split_by_prop_def order_cells_by_deg_perm)
qed

locale \<R>\<T> = refinement_function
begin
definition \<T>'_color :: "coloring \<Rightarrow> color option" where
  "\<T>'_color \<pi> = (
      if discrete \<pi> 
      then None 
      else Some (Min {c \<in> set (Coloring.colors \<pi>). card (cell \<pi> c) > 1}))"

definition \<T>' :: "colored_graph \<Rightarrow> nat list \<Rightarrow> nat fset" where
  "\<T>' G \<nu> = (
      case (\<T>'_color (\<R> G \<nu>)) of
        None \<Rightarrow> {||}
      | Some c  \<Rightarrow> Abs_fset (cell (\<R> G \<nu>) c)
  )"

lemma \<T>'_color_in_colors:
  assumes "\<T>'_color \<pi> = Some c"
  shows "c \<in> set (Coloring.colors \<pi>)"
  using assms non_discrete_cells_card_gt1[of \<pi>]
  unfolding \<T>'_color_def
  by (metis (no_types, lifting) Coloring.colors_def Min_in atLeastLessThan_iff atLeastLessThan_upt bounded_nat_set_is_finite ex_in_conv mem_Collect_eq option.inject option.simps(3))

lemma \<T>'_color_cell_gt1:
  assumes "\<T>'_color \<pi> = Some c"
  shows "card (cell \<pi> c) > 1"
  using assms non_discrete_cells_card_gt1[of \<pi>]
  unfolding \<T>'_color_def
  by (metis (no_types, lifting) Coloring.colors_def Min_in atLeastLessThan_iff atLeastLessThan_upt bounded_nat_set_is_finite ex_in_conv mem_Collect_eq option.inject option.simps(3))

lemma \<T>'_is_cell:
  assumes "\<T>'_color (\<R> G \<nu>) = Some c"
  shows "fset (\<T>' G \<nu>) = cell (\<R> G \<nu>) c"
  using assms
  unfolding \<T>'_color_def \<T>'_def
  by (auto split: if_split_asm simp add: Abs_fset_inverse)

lemma \<T>'_discrete:
  assumes "discrete (\<R> G \<nu>)"
  shows "fset (\<T>' G \<nu>) = {}"
  using assms
  unfolding \<T>'_color_def \<T>'_def
  by (auto split: if_split_asm)
end


sublocale \<R>\<T> \<subseteq> target_cell_selector where \<T> = \<T>'
proof
  fix \<nu> G
  assume "is_vertex_list G \<nu>" "discrete (\<R> G \<nu>)" 
  then show "\<T>' G \<nu> = {||}"
    unfolding \<T>'_def \<T>'_color_def
    by (auto split: option.split)
next
  fix \<nu> G
  assume *: "is_vertex_list G \<nu>" "\<not> discrete (\<R> G \<nu>)" 
  show "fset (\<T>' G \<nu>) \<in> set (cells (\<R> G \<nu>)) \<and> 1 < fcard (\<T>' G \<nu>)"
  proof-
    let ?cs = "{c \<in> set (Coloring.colors (\<R> G \<nu>)). 1 < card (cell (\<R> G \<nu>) c)}"
    have "?cs \<noteq> {}"
      using non_discrete_cells_card_gt1[OF `\<not> discrete (\<R> G \<nu>)`] Coloring.colors_def
      by fastforce
    then have "Min ?cs \<in> set (Coloring.colors (\<R> G \<nu>))" "card (cell (\<R> G \<nu>) (Min ?cs)) > 1"
      using Min_in[of ?cs]
      by auto
    then show ?thesis
      using *
      unfolding \<T>'_def \<T>'_color_def
      by (simp add: Abs_fset_inverse fcard_def colors_def cells_def)
  qed
next
  fix G \<nu> p
  assume *: "is_vertex_list G \<nu>" "perm_dom p = num_vertices G"
  have "\<forall> c \<in> set (Coloring.colors (\<R> G \<nu>)). card (perm_fun_set p (cell (\<R> G \<nu>) c)) = card (cell (\<R> G \<nu>) c)"
    using *
    by (metis (no_types, opaque_lifting) Union_upper \<R>_length' cells_def cells_ok cells_ok_def imageI list.set_map perm_fun_set_card) 
  then show "\<T>' (perm_graph p G) (perm_fun_list p \<nu>) = perm_fun_fset p (\<T>' G \<nu>)"
    using * perm_fun_fset_def perm_fun_set_def
    unfolding \<T>'_def \<T>'_color_def
    apply (auto simp add: fmember_def Abs_fset_inverse)
    apply (smt (verit, ccfv_threshold) Collect_cong image_eqI)
    apply (smt (verit, ccfv_SIG) Collect_cong image_eqI)
    done
qed

sublocale refinement_function' \<subseteq> \<R>\<T> \<R>'
  by unfold_locales

locale node_invariant_lex = target_cell_selector + 
  fixes \<Phi>_lex :: "colored_graph \<Rightarrow> vertex list \<Rightarrow> 'a::linorder"
  fixes \<g> :: "nat \<Rightarrow> (vertex \<times> vertex) set \<Rightarrow> 'b::linorder" \<comment> \<open>graph representation\<close>
  assumes \<Phi>_lex_mono: 
    "\<And> G \<nu>1 \<nu>2 \<nu>1' \<nu>2'.
       \<lbrakk>is_vertex_list G (\<nu>1' @ \<nu>1); is_vertex_list G (\<nu>2' @ \<nu>2);
        List.length \<nu>1 = List.length \<nu>2;
        \<Phi>_lex G \<nu>1 < \<Phi>_lex G \<nu>2\<rbrakk> \<Longrightarrow>
        \<Phi>_lex G (\<nu>1' @ \<nu>1) < \<Phi>_lex G (\<nu>2' @ \<nu>2)"
 assumes \<Phi>_lex_extend:
   "\<And> G \<nu> \<nu>'. \<lbrakk>is_vertex_list G (\<nu>' @ \<nu>); \<nu>' \<noteq> [] \<rbrakk> \<Longrightarrow> 
      \<Phi>_lex G \<nu> < \<Phi>_lex G (\<nu>' @ \<nu>)"
  assumes \<Phi>_lex_perm:
    "\<And> G \<nu> p. 
       \<lbrakk>\<nu> \<in> nodes (tree G); perm_dom p = num_vertices G\<rbrakk> \<Longrightarrow>
        \<Phi>_lex (perm_graph p G) (perm_fun_list p \<nu>) = \<Phi>_lex G \<nu>" 
  assumes \<g>_inject:
    "\<And> es1 es2 n. \<lbrakk> n_vertex_edges n es1; n_vertex_edges n es2; 
                    \<g> n es1 = \<g> n es2 \<rbrakk> \<Longrightarrow> es1 = es2"
begin

definition max_invar_leaves :: "colored_graph \<Rightarrow> Tree \<Rightarrow> (vertex_list set)" where
  "max_invar_leaves G T = max_by_prop (leaves G T) (\<Phi>_lex G)"

definition max_leaves' :: "colored_graph \<Rightarrow> Tree \<Rightarrow> (vertex_list set)" where
 "max_leaves' G T = max_by_prop (max_invar_leaves G T) (\<lambda> \<nu>. \<g> (num_vertices G) (perm_edges (leaf_perm G \<nu>) (edges G)))"

lemma max_invar_leaves_not_empty [simp]:
  shows "max_invar_leaves G (tree G) \<noteq> {}"
  using max_by_prop_nonempty[OF leaves_finite leaves_not_empty]
  unfolding max_invar_leaves_def 
  by blast

lemma max_invar_leaves_max_invar:
  assumes "V \<in> max_invar_leaves G (tree G)" "V' \<in> leaves G (tree G)"
  shows "\<Phi>_lex G V \<ge> \<Phi>_lex G V'"
  using assms
  by (metis leaves_finite max_by_prop_max_prop max_invar_leaves_def) 

lemma max_invar_leaves_max_invar_eq:
  assumes "V \<in> max_invar_leaves G (tree G)" "V' \<in> max_invar_leaves G (tree G)"
  shows "\<Phi>_lex G V = \<Phi>_lex G V'"
  using assms
  by (metis leaves_finite max_by_prop_max_prop_eq max_invar_leaves_def) 

lemma max_invar_leaves_max_invar_gt:
  assumes "V \<in> max_invar_leaves G (tree G)" "V' \<in> leaves G (tree G)" "V' \<notin> max_invar_leaves G (tree G)"
  shows "\<Phi>_lex G V > \<Phi>_lex G V'"
  using assms
  unfolding max_invar_leaves_def
  using max_by_prop_max_prop_gt[OF leaves_finite]
  by auto

lemma \<Phi>_lex_extend_nodes:
  assumes "\<nu> \<in> nodes (tree G)" "\<nu>' \<in> leaves G (expand_tree G \<nu>)" "\<nu>' \<noteq> \<nu>"
  shows "\<Phi>_lex G \<nu> < \<Phi>_lex G \<nu>'"
proof-
  obtain \<nu>'' where "\<nu>' = \<nu>'' @ \<nu>" "\<nu>'' \<noteq> []"
    using leaves_expand_tree_suffix_not_root
    by (metis append_Nil append_take_drop_id assms(1) assms(2) assms(3) nodes_is_vertex_list)
  then show "\<Phi>_lex G \<nu> < \<Phi>_lex G \<nu>'"
    using \<Phi>_lex_extend
    using assms(1) assms(2) leaf_is_node nodes_expand_tree_is_vertex_list nodes_is_vertex_list 
    by blast
qed

definition \<Phi>' where 
  "\<Phi>' G \<nu> = (if \<not> discrete (\<R> G \<nu>) 
             then (\<Phi>_lex G \<nu>, None)
             else (\<Phi>_lex G \<nu>, Some (\<g> (num_vertices G) (perm_edges (leaf_perm G \<nu>) (edges G)))))"

lemma \<Phi>_extend:
  assumes "\<nu> \<in> nodes (tree G)" "\<nu>' \<in> leaves G (expand_tree G \<nu>)" "\<nu>' \<noteq> \<nu>"
  shows "\<Phi>' G \<nu> < \<Phi>' G \<nu>'"
  using assms \<Phi>_lex_extend_nodes
  unfolding \<Phi>'_def
  by auto

end

sublocale node_invariant_lex \<subseteq> node_invariant
   where \<Phi> = \<Phi>' 
proof
  fix G V V'
  let ?fV = "\<Phi>_lex G V"
  let ?fV' = "\<Phi>_lex G V'"
  let ?hV = "\<g> (num_vertices G) (perm_edges (leaf_perm G V) (edges G))"
  let ?hV' = "\<g> (num_vertices G) (perm_edges (leaf_perm G V') (edges G))"
  let ?lV = "discrete (\<R> G V)"
  let ?lV' = "discrete (\<R> G V')"

  assume assms: "V \<in> nodes (tree G)" "V' \<in> nodes (tree G)" 
         "List.length V = List.length V'"
         "\<Phi>' G V < \<Phi>' G V'"
  then have *:"?fV < ?fV' \<or> 
               (?fV = ?fV' \<and> ?lV \<and> 
               (\<not> ?lV' \<or> (?lV' \<and> ?hV < ?hV')))"
    unfolding \<Phi>'_def Let_def
    by (auto split: if_split_asm simp add: less_eq_option_def less_option_def)

  show "\<forall> V1\<in>leaves G (expand_tree G V).
             \<forall>V1'\<in>leaves G (expand_tree G V'). \<Phi>' G V1 < \<Phi>' G V1'"
  proof safe
    fix V1 V1'
    assume l: "V1 \<in> leaves G (expand_tree G V)" "V1' \<in> leaves G (expand_tree G V')"
    then obtain k k' where 
      k: "k \<le> List.length V1" "drop k V1 = V" 
         "k' \<le> List.length V1'" "drop k' V1' = V'" "V1' \<noteq> V' \<longrightarrow> k' > 0"
      using leaves_expand_tree_suffix leaves_expand_tree_suffix_not_root
      by (metis assms(1) assms(2) nodes_is_vertex_list)

    then obtain V2 V2' where **: "V1 = V2 @ V" "V1' = V2' @ V'" "V1' \<noteq> V' \<longrightarrow> V2' \<noteq> []"
      by (metis append_Nil append_take_drop_id)

    have dd: "discrete (\<R> G V1)" "discrete (\<R> G V1')"
      using \<open>V \<in> nodes (tree G)\<close> \<open>V' \<in> nodes (tree G)\<close> l leaves_expand_tree_iff_discrete_nodes_expand_tree nodes_is_vertex_list
      by blast+

    have "is_vertex_list G V1" "is_vertex_list G V1'"
     using assms l leaf_is_node nodes_expand_tree_is_vertex_list nodes_is_vertex_list 
     by blast+

    show "\<Phi>' G V1 < \<Phi>' G V1'"
    proof (cases "?fV < ?fV'")
      case True
      then show ?thesis
        using \<Phi>_lex_mono assms l(1-2) **(1-2)
        using \<open>is_vertex_list G V1'\<close> \<open>is_vertex_list G V1\<close>
        unfolding \<Phi>'_def Let_def
        by auto
    next
      case False
      then have "?fV = ?fV'" "?lV" "\<not> ?lV' \<or> (?lV' \<and> ?hV < ?hV')"
        using *
        by auto
      have "V1 = V"
        using \<open>V \<in> nodes (tree G)\<close> \<open>discrete (\<R> G V)\<close> l(1)
        by (metis is_vertex_list_empty leaves_iff_discrete_nodes leaves_of_leaf tree_def)
      show ?thesis
      proof (cases "\<not> ?lV'")
        case False
        then have "V1' = V'"
          using \<open>V' \<in> nodes (tree G)\<close> l(2)
          by (metis is_vertex_list_empty leaves_iff_discrete_nodes leaves_of_leaf tree_def)
        then show ?thesis
          using \<open>V1 = V\<close>  \<open>\<Phi>' G V < \<Phi>' G V'\<close>
          by simp
      next
        case True
        then have "snd (\<Phi>' G V') = None"
          unfolding \<Phi>'_def
          by auto

        have "V1' \<noteq> V'"
          using True dd(2) by blast
        then have "V2' \<noteq> []"
          using "**"(3) by auto
        moreover
        have "is_vertex_list G V1'"
          using nodes_is_vertex_list
          using assms(2) l(2) leaf_is_node nodes_expand_tree_is_vertex_list
          by blast
        ultimately have "\<Phi>' G V1 < \<Phi>' G V1'"
          using `V1' = V2' @ V'` \<open>V1 = V\<close> \<open>?fV = ?fV'\<close> dd \<Phi>_lex_extend
          by (auto simp add: \<Phi>'_def)
        then show ?thesis
          unfolding \<Phi>'_def Let_def
          by auto
      qed
    qed
  qed
next
  fix G \<pi> \<pi>' V V'
  assume "is_vertex_list G V" "is_vertex_list G V'" "\<pi> = \<R> G V" "\<pi>' = \<R> G V'" "discrete \<pi>" "discrete \<pi>'" 
  then show "\<Phi>' G V = \<Phi>' G V' \<longrightarrow> perm_edges (leaf_perm G V) (edges G) = perm_edges (leaf_perm G V') (edges G)"
    using \<g>_inject
    unfolding \<Phi>'_def
    by (smt (verit, ccfv_SIG) Pair_inject case_prodI2 edge_vertices(1) edge_vertices(2) edges_perm_graph leaf_perm_perm_dom num_vertices_perm_graph option.inject)
next
  fix G V p
  assume "V \<in> nodes (tree G)" "perm_dom p = num_vertices G" 
  then show "\<Phi>' (perm_graph p G) (perm_fun_list p V) = \<Phi>' G V"
    using \<Phi>_lex_perm leaves_iff_discrete_nodes leaf_perm_perm_perm_edges
    unfolding \<Phi>'_def
    by auto
qed

context node_invariant_lex
begin
lemma max_leaves':
  shows "max_leaves G (tree G) = max_leaves' G (tree G)"
  proof-
    have "max_leaves' G (tree G) = max_by_prop (leaves G (tree G)) (\<lambda>x. (\<Phi>_lex G x, \<g> (num_vertices G) (perm_edges (leaf_perm G x) (edges G))))"
      unfolding max_leaves'_def max_invar_leaves_def
      by (subst max_by_prop_pair, auto)
    also have "... = max_leaves G (tree G)"
      unfolding max_leaves_def \<Phi>'_def
      by (rule max_by_prop_cong, auto simp add: less_option_def less_eq_option_def)
    finally show ?thesis by simp
  qed
end

locale node_invariant_fun = target_cell_selector + 
  fixes invar :: "colored_graph \<Rightarrow> coloring \<Rightarrow> bool" \<comment> \<open>invariant that each node coloring satisfies\<close>
  fixes \<f> :: "colored_graph \<Rightarrow> coloring \<Rightarrow> 'a" \<comment> \<open>function calculated in each node\<close>
  fixes \<f>_hash :: "'a \<Rightarrow> nat" \<comment> \<open>hash function\<close> \<comment> \<open>hash applied to function values in each node\<close>
  fixes \<g> :: "nat \<Rightarrow> (vertex \<times> vertex) set \<Rightarrow> 'b::linorder" \<comment> \<open>graph (edge set) representation\<close>
  assumes invar [simp]:
    "\<And> G \<nu>. is_vertex_list G \<nu> \<Longrightarrow> invar G (\<R> G \<nu>)"
  assumes \<f>_perm [simp]:
    "\<And> G \<pi>. \<lbrakk>perm_dom p = num_vertices G; perm_dom p = length \<pi>; invar G \<pi> \<rbrakk> \<Longrightarrow>  
                \<f> (perm_graph p G) (perm_coloring p \<pi>) = \<f> G \<pi>"
  assumes \<g>_inject': "\<And> es1 es2 n. \<lbrakk> n_vertex_edges n es1; n_vertex_edges n es2; 
                                    \<g> n es1 = \<g> n es2 \<rbrakk> \<Longrightarrow> es1 = es2"
begin

abbreviation \<f>h where
   "\<f>h G \<nu> \<equiv> \<f>_hash (\<f> G (\<R> G \<nu>))"

definition \<Phi>_lex' :: "colored_graph \<Rightarrow> vertex list \<Rightarrow> nat list" where
  "\<Phi>_lex' G \<nu> = map (\<lambda> \<nu>'. \<f>h G \<nu>') (parents \<nu>)"

lemma \<Phi>_lex'_gt: 
  assumes "is_vertex_list G \<nu>1" "is_vertex_list G \<nu>1" "\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2"
           "\<f>h G (v1 # \<nu>1) > \<f>h G (v2 # \<nu>2)"
    shows "\<Phi>_lex' G (v1 # \<nu>1) > \<Phi>_lex' G (v2 # \<nu>2)"
    using assms list_less_append[of "[\<f>h G (v2 # \<nu>2)]" "[\<f>h G (v1 # \<nu>1)]" "\<Phi>_lex' G \<nu>1"]
    unfolding \<Phi>_lex'_def
    by auto
end

sublocale node_invariant_fun \<subseteq> node_invariant_lex where \<Phi>_lex = \<Phi>_lex'
proof
  fix G \<nu> \<nu>'
  assume *: "is_vertex_list G (\<nu>' @ \<nu>)" "\<nu>' \<noteq> []"

  have "tl (parents \<nu>') \<noteq> []"
    using `\<nu>' \<noteq> []`
    by (metis Nil_is_append_conv Nil_tl hd_parents last_ConsL last_snoc list.sel(1) list_encode.cases parents_Cons)
  then show "\<Phi>_lex' G \<nu> < \<Phi>_lex' G (\<nu>' @ \<nu>)"
    using * list_less_append[of "[]" _ ]
    unfolding \<Phi>_lex'_def
    by (smt (verit, del_insts) Nil_is_map_conv append_Nil2 less_list_code(1) linorder_less_linear map_append parents_append) 
next
  fix es1 es2 n
  assume "n_vertex_edges n es1" "n_vertex_edges n es2" "\<g> n es1 = \<g> n es2"
  then show "es1 = es2" 
    using \<g>_inject'
    by auto
next
  fix G \<nu>1 \<nu>2 \<nu>1' \<nu>2'
  assume  "is_vertex_list G (\<nu>1' @ \<nu>1)" "is_vertex_list G (\<nu>2' @ \<nu>2)" "List.length \<nu>1 = List.length \<nu>2"
          "\<Phi>_lex' G \<nu>1 < \<Phi>_lex' G \<nu>2"
  then show "\<Phi>_lex' G (\<nu>1' @ \<nu>1) < \<Phi>_lex' G (\<nu>2' @ \<nu>2)"
    unfolding \<Phi>_lex'_def
    by (simp add: list_less_right_append)
next
  fix G \<nu> p
  assume "\<nu> \<in> nodes (tree G)" "perm_dom p = num_vertices G" 
  then show "\<Phi>_lex' (perm_graph p G) (perm_fun_list p \<nu>) = \<Phi>_lex' G \<nu>"
    using nodes_is_vertex_list parents_vertex_lists
    unfolding \<Phi>_lex'_def
    by auto
qed

locale McKayPiperno = split_and_order +
  fixes \<f> :: "colored_graph \<Rightarrow> coloring \<Rightarrow> 'c"
  fixes \<f>_hash :: "'c \<Rightarrow> nat" \<comment> \<open>hash function\<close>
  fixes \<g> :: "nat \<Rightarrow> (vertex \<times> vertex) set \<Rightarrow> 'b::linorder" \<comment> \<open>binary representation for graph\<close>
  assumes \<f>_perm' [simp]:
    "\<And> G \<pi>. \<lbrakk>perm_dom p = num_vertices G; perm_dom p = length \<pi>; is_split_by G \<pi> \<rbrakk> \<Longrightarrow>  
                \<f> (perm_graph p G) (perm_coloring p \<pi>) = \<f> G \<pi>"
  assumes \<g>_inject'': "\<And> es1 es2 n. \<lbrakk> n_vertex_edges n es1; n_vertex_edges n es2; 
                                     \<g> n es1 = \<g> n es2 \<rbrakk> \<Longrightarrow> es1 = es2"

sublocale McKayPiperno \<subseteq> node_invariant_fun \<R>' \<T>' is_split_by \<f> \<f>_hash
proof
  fix G \<nu>
  assume "is_vertex_list G \<nu>"
  then show "is_split_by G (\<R>' G \<nu>)"
    using is_split_by
    by blast
next
  fix es1 es2 n
  assume "n_vertex_edges n es1" "n_vertex_edges n es2"
         "\<g> n es1 = \<g> n es2" 
  then show "es1 = es2"
    using \<g>_inject''
    by simp
next
  fix p G \<pi>
  assume "perm_dom p = num_vertices G" "perm_dom p = length \<pi>" "is_split_by G \<pi>"
  then show "\<f> (perm_graph p G) (perm_coloring p \<pi>) = \<f> G \<pi>"
    using \<f>_perm'
    by simp
qed    

definition equitable :: "colored_graph \<Rightarrow> coloring \<Rightarrow> bool" where
  "equitable G \<pi> \<longleftrightarrow>
    (\<forall> c1 c2 v1 v2. c1 < Coloring.num_colors \<pi> \<longrightarrow>
                    c2 < Coloring.num_colors \<pi> \<longrightarrow>
                    v1 \<in> cell \<pi> c1 \<longrightarrow>
                    v2 \<in> cell \<pi> c1 \<longrightarrow>
                    (node_deg_set G (cell \<pi> c2) v1 = node_deg_set G (cell \<pi> c2) v2))"

lemma equitable_perm [simp]:
  assumes "perm_dom p = num_vertices G"
  assumes "perm_dom p = Coloring.length \<pi>"
  shows "equitable (perm_graph p G) (perm_coloring p \<pi>) \<longleftrightarrow> equitable G \<pi>"
proof
  assume "equitable (perm_graph p G) (perm_coloring p \<pi>)"
  have "\<And> c1 c2 v1 v2. \<lbrakk>
                         c1 < Coloring.num_colors \<pi>;
                         c2 < Coloring.num_colors \<pi>;
                         v1 \<in> cell \<pi> c1;
                         v2 \<in> cell \<pi> c1 \<rbrakk> \<Longrightarrow>
                         (node_deg_set G (cell \<pi> c2) v1 = 
                          node_deg_set G (cell \<pi> c2) v2)"
  proof-
    fix c1 c2 v1 v2
    assume "c1 < Coloring.num_colors \<pi>" "c2 < Coloring.num_colors \<pi>"
    assume "v1 \<in> cell \<pi> c1" "v2 \<in> cell \<pi> c1"

    have "c1 < Coloring.num_colors (perm_coloring p \<pi>)" "c2 < Coloring.num_colors (perm_coloring p \<pi>)"
      using assms(2) num_colors_perm_coloring `c1 < Coloring.num_colors \<pi>` `c2 < Coloring.num_colors \<pi>`
      by auto

    moreover obtain w1 where "w1 \<in> cell (perm_coloring p \<pi>) c1" "w1 = perm_fun p v1"
      by (simp add: \<open>v1 \<in> cell \<pi> c1\<close> assms(2) perm_fun_set_def)
    moreover obtain w2 where "w2 \<in> cell (perm_coloring p \<pi>) c1" "w2 = perm_fun p v2"
      by (simp add: \<open>v2 \<in> cell \<pi> c1\<close> assms(2) perm_fun_set_def)

    ultimately have "node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) w1 = 
                     node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) w2"
      using `equitable (perm_graph p G) (perm_coloring p \<pi>)` equitable_def
      by blast

    moreover have "cell \<pi> c2 \<subseteq> {0..<perm_dom p}"
      using assms(2) cell_def by auto
    moreover have "v1 < perm_dom p" "v2 < perm_dom p"
      using \<open>v1 \<in> cell \<pi> c1\<close> \<open>v2 \<in> cell \<pi> c1\<close> assms(2) cell_def by auto

    ultimately show "node_deg_set G (cell \<pi> c2) v1 = node_deg_set G (cell \<pi> c2) v2"
      using assms node_deg_set_perm `w1 = perm_fun p v1` `w2 = perm_fun p v2`
      by auto
  qed
  then show "equitable G \<pi>"
    using equitable_def by blast
next
  assume "equitable G \<pi>"
  have "(\<And> c1 c2 v1 v2. \<lbrakk>
                    c1 < Coloring.num_colors (perm_coloring p \<pi>);
                    c2 < Coloring.num_colors (perm_coloring p \<pi>);
                    v1 \<in> cell (perm_coloring p \<pi>) c1;
                    v2 \<in> cell (perm_coloring p \<pi>) c1 \<rbrakk> \<Longrightarrow>
                    (node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) v1 =
                     node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) v2))"
  
  proof-
    fix c1 c2 v1 v2
    assume "c1 < Coloring.num_colors (perm_coloring p \<pi>)"
    assume "c2 < Coloring.num_colors (perm_coloring p \<pi>)"
    assume "v1 \<in> cell (perm_coloring p \<pi>) c1"
    assume "v2 \<in> cell (perm_coloring p \<pi>) c1"

    have "c1 < Coloring.num_colors \<pi>" "c2 < Coloring.num_colors \<pi>"
      using `c1 < Coloring.num_colors (perm_coloring p \<pi>)`
      using `c2 < Coloring.num_colors (perm_coloring p \<pi>)`
      using num_colors_perm_coloring assms(2)
      by auto

    moreover obtain w1 where "w1 \<in> cell \<pi> c1" "perm_fun p w1 = v1"
      using \<open>v1 \<in> cell (perm_coloring p \<pi>) c1\<close> assms(2) perm_fun_set_def by auto
    moreover obtain w2 where "w2 \<in> cell \<pi> c1" "perm_fun p w2 = v2"
      using \<open>v2 \<in> cell (perm_coloring p \<pi>) c1\<close> assms(2) perm_fun_set_def by auto

    ultimately have "node_deg_set G (cell \<pi> c2) w1 = node_deg_set G (cell \<pi> c2) w2"
      using `equitable G \<pi>` equitable_def by blast

    moreover have "cell \<pi> c2 \<subseteq> {0..<perm_dom p}"
      using assms(2) cell_def by auto
    moreover have "w1 < perm_dom p" "w2 < perm_dom p"
      using `w1 \<in> cell \<pi> c1` `w2 \<in> cell \<pi> c1` assms(2) cell_def by auto

    ultimately show "node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) v1 =
                     node_deg_set (perm_graph p G) (cell (perm_coloring p \<pi>) c2) v2"
      using assms node_deg_set_perm `perm_fun p w1 = v1` `perm_fun p w2 = v2`
      by auto
  qed
  then show "equitable (perm_graph p G) (perm_coloring p \<pi>)"
    using equitable_def by blast
qed

type_synonym quotient_graph = "(nat list \<times> (vertex \<Rightarrow> vertex \<Rightarrow> nat))"

definition quotient_graph :: "colored_graph \<Rightarrow> coloring \<Rightarrow> quotient_graph" where
  "quotient_graph G \<pi> = (
    let n = Coloring.num_colors \<pi>;
        verts = map card (cells \<pi>);
        edgew = \<lambda> i j. if i < n \<and> j < n 
                       then node_deg_set (recolor G \<pi>) (cell \<pi> i) (SOME v . v \<in> cell \<pi> j) 
                       else 0
     in (verts, edgew)
  )"

lemma quotient_graph_perm: 
  assumes "equitable (recolor G \<pi>) \<pi>"
  assumes gdom: "perm_dom p = num_vertices G"
  assumes pidom: "perm_dom p = Coloring.length \<pi>"
  shows "quotient_graph (perm_graph p G) (perm_coloring p \<pi>) = quotient_graph G \<pi>"
proof
  let ?n = "perm_dom p"
  let ?cn = "Coloring.num_colors \<pi>"

  have "\<forall>c \<in> {0..<?cn}. card (cell (perm_coloring p \<pi>) c) = card (cell \<pi> c)"
  proof
    fix c
    assume c_in_dom: "c \<in> {0..<?cn}"
    let ?lhs = "cell (perm_coloring p \<pi>) c"
    let ?rhs = "cell \<pi> c"
    have "?rhs \<subseteq> {0..<?n}"
      using cell_def c_in_dom pidom by auto
    moreover have "?lhs = perm_fun_set p ?rhs"
      using cell_perm_coloring c_in_dom pidom by auto
    ultimately show "card ?lhs = card ?rhs"
      using c_in_dom pidom perm_fun_set_card by auto
  qed

  then have "map (card \<circ> cell (perm_coloring p \<pi>)) [0..<?cn] =
             map (card \<circ> cell \<pi>) [0..<?cn]"
    by auto
  then show "fst (quotient_graph (perm_graph p G) (perm_coloring p \<pi>)) =
             fst (quotient_graph G \<pi>)" 
    using pidom
    unfolding quotient_graph_def Let_def cells_def Coloring.colors_def
    by auto
  next
    show "snd (quotient_graph (perm_graph p G) (perm_coloring p \<pi>)) =
          snd (quotient_graph G \<pi>)"
    proof-
      have peq: "equitable (recolor (perm_graph p G) (perm_coloring p \<pi>)) (perm_coloring p \<pi>)"
        using `equitable (recolor G \<pi>) \<pi>`
        using equitable_perm gdom pidom 
        by auto
      {
      fix i j
      assume idom: "i \<in> {0..<Coloring.num_colors \<pi>}"
      assume jdom: "j \<in> {0..<Coloring.num_colors \<pi>}"
      let ?ci  = "cell \<pi> i"
      let ?cj  = "cell \<pi> j"
      let ?ci' = "cell (perm_coloring p \<pi>) i"
      let ?cj' = "cell (perm_coloring p \<pi>) j"
      let ?rG  = "recolor G \<pi>"
      let ?rG' = "recolor (perm_graph p G) (perm_coloring p \<pi>)"
      have "node_deg_set ?rG' ?ci' (SOME v. v \<in> ?cj') = node_deg_set ?rG ?ci (SOME v. v \<in> ?cj)"
      proof-
        have cjp: "?cj' = perm_fun_set p ?cj" 
          using pidom
          by auto
        obtain v where "v \<in> ?cj" "(SOME v. v \<in> ?cj) = v"
          using cell_non_empty jdom some_in_eq 
          by fastforce
        then have *: "perm_fun p v \<in> ?cj'" 
          using cjp perm_fun_set_def 
          by auto

        have cidom: "?ci \<subseteq> {0..<perm_dom p}" using cell_def pidom by auto
        have cjdom: "?cj \<subseteq> {0..<perm_dom p}" using cell_def pidom by auto
        have vsup:  "v < perm_dom p" using cjdom \<open>v \<in> ?cj\<close> by auto
        have "node_deg_set ?rG ?ci v = node_deg_set ?rG' ?ci' (perm_fun p v)"
          using gdom pidom cidom cjdom vsup
          by auto
        also have "... =  node_deg_set ?rG' ?ci' (SOME v. v \<in> ?cj')"
        proof-
          have "i < Coloring.num_colors (perm_coloring p \<pi>)" "j < Coloring.num_colors (perm_coloring p \<pi>)"
            using idom jdom pidom
            by auto
          moreover have "(SOME v. v \<in> cell (perm_coloring p \<pi>) j) \<in> cell (perm_coloring p \<pi>) j" "(perm_fun p v) \<in> cell (perm_coloring p \<pi>) j"
            using * some_in_eq
            by auto
          ultimately show ?thesis
            using peq
            unfolding equitable_def
            by blast
        qed
        finally show ?thesis
          using `(SOME v. v \<in> ?cj) = v`
          by simp
      qed
    }
    note ** = this
    show ?thesis
      using pidom ** 
      unfolding quotient_graph_def Let_def
      by auto ((rule ext)+, auto split: if_split) 
  qed
qed


definition hash32 :: "32 word \<Rightarrow> 32 word" where
  "hash32 value = (
     let value1 = value + 1;
         value2 = xor value1 (drop_bit 17 value1);
         value3 = value2 * 3982152891;
         value4 = xor value3 (drop_bit 11 value3);
         value5 = value4 * 2890668881;
         value6 = xor value5 (drop_bit 15 value5);
         value7 = value6 * 830770091;
         value8 = xor value7 (drop_bit 14 value7)
      in value8
  )"

definition sequential32 :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word" where
  "sequential32 prev_hash value = hash32 (xor prev_hash value)"

fun hash_triple :: "32 word \<times> 32 word \<times> 32 word \<Rightarrow> 32 word" where
 "hash_triple (x, y, z) = 
    (let h1 = sequential32 0 x;
         h2 = sequential32 h1 y;
         h3 = sequential32 h2 z
      in h3)"

definition multiset32add :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word" where
  "multiset32add prev_hash value = prev_hash + hash32 value + 1"

fun quotient_graph_hash :: "quotient_graph \<Rightarrow> nat" where
  "quotient_graph_hash (vertices, edge_weights_fun) = (
     let n = List.length vertices;
         add_node = \<lambda> v invariant. multiset32add invariant (word_of_nat v);
         add_edges = \<lambda> i invariant. fold (\<lambda> j invariant. multiset32add invariant (hash_triple (word_of_nat i, word_of_nat j, word_of_nat (edge_weights_fun i j)))) [0..<n] invariant 
      in unat (fold (\<lambda> (i, v) invariant. add_edges i (add_node v invariant)) (zip [0..<n] vertices) 0)
  )"

definition adjacency_matrix :: "nat \<Rightarrow> (vertex \<times> vertex) set \<Rightarrow> bool list list" where
  "adjacency_matrix n es = map (\<lambda> i. (map (\<lambda> j. (i, j) \<in> es ) [0..<n])) [0..<n]"

lemma adjacency_matrix_nth:
  assumes "n_vertex_edges n es" 
  shows "(v1, v2) \<in> es \<longleftrightarrow> v1 < n \<and> v2 < n \<and> (adjacency_matrix n es) ! v1 ! v2"
  using assms
  unfolding adjacency_matrix_def
  by auto
  
lemma adjacency_matrix_inj: 
  assumes "n_vertex_edges n es1" "n_vertex_edges n es2"
          "adjacency_matrix n es1 = adjacency_matrix n es2"
  shows "es1 = es2"
  using assms adjacency_matrix_nth[OF assms(1)] adjacency_matrix_nth[OF assms(2)]
  by auto

interpretation mcp: McKayPiperno order_cells_by_deg node_deg_set quotient_graph quotient_graph_hash adjacency_matrix
proof
  fix p G \<pi>
  assume *: "perm_dom p = num_vertices G" "perm_dom p = length \<pi>" "so.is_split_by G \<pi>"
  then have "equitable (recolor G \<pi>) \<pi>"
    unfolding so.is_split_by_def equitable_def
    by metis
  then show "quotient_graph (perm_graph p G) (perm_coloring p \<pi>) = quotient_graph G \<pi>"
    using quotient_graph_perm *
    by simp
next
  fix es1 es2 n
  assume "n_vertex_edges n es1" "n_vertex_edges n es2" "adjacency_matrix n es1 = adjacency_matrix n es2"
  then show "es1 = es2"
    by (simp add: adjacency_matrix_inj)
qed

end