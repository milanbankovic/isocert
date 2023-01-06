theory Coloring
  imports Main Permutation
begin

lemma MaxAtLeastLessThan [simp]:
  fixes k :: nat
  assumes "k > 0"
  shows "Max {0..<k} = k - 1"
proof (subst Max_eq_iff)
  show "finite {0..<k}" 
    using finite_atLeastLessThan
    by auto
next
  show "{0..<k} \<noteq> {}" using assms by simp
next
  show "k - 1 \<in> {0..<k} \<and> (\<forall>a\<in>{0..<k}. a \<le> k - 1)"
    using assms
    by auto
qed


text\<open>colors are represented by natural numbers\<close>
type_synonym color = nat

typedef coloring = "{cs :: color list. (\<exists> k. set cs = {0..<k})}"
    morphisms color_list coloring
by (rule_tac x="[0]" in exI, auto)

setup_lifting type_definition_coloring

lift_definition length :: "coloring \<Rightarrow> nat" is List.length
done

lift_definition max_color :: "coloring \<Rightarrow> color" is "\<lambda> cs. Max (set cs)"
done

definition num_colors :: "coloring \<Rightarrow> nat" where
  "num_colors \<pi> = (if color_list \<pi> = [] then 0 else max_color \<pi> + 1)"

definition colors :: "coloring \<Rightarrow> color list" where
    "colors \<pi> = [0..<num_colors \<pi>]"

lemma distinct_colors:
  shows "distinct (colors \<pi>)"
  by (simp add: colors_def) 

lemma ex_color:
  assumes "c < num_colors \<pi>"
  shows "c \<in> set (colors \<pi>)"
using assms
unfolding colors_def num_colors_def
by auto

lift_definition color_fun :: "coloring => (nat => color)" is "\<lambda> cs v. cs ! v"
done

lemma color_fun_in_colors:
  assumes "v < length \<pi>"
  shows "color_fun \<pi> v \<in> set (colors \<pi>)"
  using assms
  unfolding colors_def num_colors_def
  by transfer (smt (verit, ccfv_SIG) MaxAtLeastLessThan One_nat_def Suc_pred add.commute empty_iff list.set(1) not_gr_zero nth_mem plus_1_eq_Suc set_upt upt_0)

lemma ex_color_color_fun:
  assumes "c \<in> set (colors \<pi>)"
  shows "\<exists> v < length \<pi>. color_fun \<pi> v = c"
  using assms
  unfolding colors_def num_colors_def
  by transfer (metis (mono_tags, opaque_lifting) MaxAtLeastLessThan Suc_eq_plus1 Suc_pred' add_lessD1 atLeastLessThan_iff atLeastLessThan_upt comm_monoid_add_class.add_0 in_set_conv_nth length_greater_0_conv not_less0) 

lemma all_colors:
  shows "set (colors \<pi>) = set (map (color_fun \<pi>) [0..<length \<pi>])"
  unfolding colors_def num_colors_def
  by transfer (smt (verit, del_insts) MaxAtLeastLessThan Suc_eq_plus1_left Suc_pred' add.commute atLeastLessThan_iff atLeastLessThan_upt gr_zeroI length_greater_0_conv length_pos_if_in_set map_nth nth_mem)

lemma all_colors_list:
  shows "colors \<pi> = remdups (sort (map (color_fun \<pi>) [0..<length \<pi>]))"
  by (metis all_colors colors_def remdups_upt set_sort sort_upt sorted_list_of_set_sort_remdups sorted_remdups sorted_sort sorted_sort_id)

lemma color_fun_all_colors [simp]: 
  shows "\<exists>k. color_fun \<pi> ` {0..<length \<pi>} = {0..<k}"
  by transfer  (metis list.set_map map_nth set_upt)


lemma coloring_eqI:
  assumes "length \<pi> = length \<pi>'" "\<forall> v < length \<pi>. color_fun \<pi> v = color_fun \<pi>' v"
  shows "\<pi> = \<pi>'"
proof-
  have "color_list \<pi> = color_list \<pi>'"
    by (metis assms(1) assms(2) color_fun.rep_eq length.rep_eq nth_equalityI) 
  then show ?thesis
    by (simp add: color_list_inject) 
qed

definition color_fun_to_coloring :: "nat \<Rightarrow> (nat \<Rightarrow> color) \<Rightarrow> coloring" where
  "color_fun_to_coloring n \<pi> = coloring (map \<pi> [0..<n])"


lemma color_fun_to_coloring [simp]:
  assumes "\<exists>k. \<pi> ` {0..<n} = {0..<k}" "v < n" 
  shows "color_fun (color_fun_to_coloring n \<pi>) v = \<pi> v"
  using assms
  unfolding color_fun_to_coloring_def
  by (subst color_fun.abs_eq) (simp_all add: eq_onp_def)

lemma color_fun_to_coloring_length [simp]:
  assumes "\<exists> k. \<pi> ` {0..<n} = {0..<k}"
  shows "length (color_fun_to_coloring n \<pi>) = n"
  using assms
  unfolding color_fun_to_coloring_def
  by transfer (simp add: coloring_inverse length.rep_eq)

lemma color_fun_to_coloring_eq_conv: 
  assumes "\<forall> v < n. \<pi>1 v = \<pi>2 v" 
  shows "color_fun_to_coloring n \<pi>1 = color_fun_to_coloring n \<pi>2"
  unfolding color_fun_to_coloring_def
  by (smt (verit, best) assms ex_nat_less_eq linorder_not_less map_eq_conv set_upt)

text\<open>------------------------------------------------------\<close>
subsection\<open>Cells\<close>
text\<open>------------------------------------------------------\<close>

text \<open>Cell of a coloring is the set of all vertices colored by the given color\<close>
definition cell :: "coloring \<Rightarrow> color \<Rightarrow> nat set" where
  "cell \<pi> c = {v. v < length \<pi> \<and> color_fun \<pi> v = c}"

text \<open>The list of all cells of a given coloring\<close>
definition cells :: "coloring \<Rightarrow> (nat set) list" where
  "cells \<pi> = map (\<lambda> c. cell \<pi> c) (colors \<pi>)" 

lemma cell_finite [simp]:
  shows "finite (cell \<pi> c)"
  unfolding cell_def
  by auto

lemma length_cells [simp]:
  shows "List.length (cells \<pi>) = num_colors \<pi>"
  by (simp add: cells_def colors_def num_colors_def) 

lemma nth_cells [simp]:
  assumes "c < num_colors \<pi>"
  shows "cells \<pi> ! c = cell \<pi> c"
  using assms
  unfolding colors_def num_colors_def cells_def
  by auto

lemma cells_disjunct:
  assumes "i < num_colors \<pi>" "j < num_colors \<pi>" "i \<noteq> j"
  shows "cells \<pi> ! i \<inter> cells \<pi> ! j = {}"
  using assms
  by (auto simp add: cell_def)

lemma cells_non_empty:
  assumes "c \<in> set (cells \<pi>)"
  shows "c \<noteq> {}"
  using assms ex_color_color_fun
  unfolding cells_def cell_def
  by auto

lemma cell_non_empty:
  assumes "c < num_colors \<pi>"
  shows "cell \<pi> c \<noteq> {}"
  by (metis assms cells_non_empty length_cells nth_cells nth_mem) 

definition cells_ok where
  "cells_ok n cs \<longleftrightarrow> 
    (\<forall> i j. i < List.length cs \<and> j < List.length cs \<and> i \<noteq> j  \<longrightarrow> cs ! i \<inter> cs ! j = {}) \<and>
    (\<forall> c \<in> set cs. c \<noteq> {}) \<and> 
    (\<Union> (set cs) = {0..<n})"

lemma cells_ok:
  shows "cells_ok (length \<pi>) (cells \<pi>)"
  unfolding cells_ok_def
proof safe
  fix i j x
  assume "i < List.length (cells \<pi>)" "j < List.length (cells \<pi>)" "i \<noteq> j"
         "x \<in> (cells \<pi>) ! i" "x \<in> (cells \<pi>) ! j"
  then show "x \<in> {}"
    using cells_disjunct
    by auto
next
  assume "{} \<in> set (cells \<pi>)"
  then show False
    using cells_non_empty by blast
next
  fix v Cell
  assume "v \<in> Cell" "Cell \<in> set (cells \<pi>)"
  then show "v \<in> {0..<length \<pi>}"
     unfolding cells_def all_colors cell_def
     by auto
next
  fix v
  assume "v \<in> {0..<length \<pi>}"
  then have "v \<in> cell \<pi> (color_fun \<pi> v)"
    unfolding cell_def
    by simp
  then show "v \<in> \<Union> (set (cells \<pi>))"
    using `v \<in> {0..<length \<pi>}`
    by (simp add: cells_def cell_def color_fun_in_colors)
qed

lemma cells_ok_finite [simp]:
  fixes n :: nat
  assumes "cells_ok n cs" "x \<in> set cs"
  shows "finite x"
  using assms
  unfolding cells_ok_def
  by (metis List.finite_set Union_upper finite_subset set_upt)

lemma distinct_cells:
  shows "distinct (cells \<pi>)"
  using cells_ok[of \<pi>]
  unfolding cells_ok_def
  by (metis distinct_conv_nth in_set_conv_nth le_iff_inf order.refl)

text\<open>------------------------------------------------------\<close>
subsection \<open>Cells to coloring\<close>
text\<open>------------------------------------------------------\<close>

text\<open>determine coloring fun or the coloring given by its cells\<close>

text\<open>function given by a set of ordered pairs\<close>
definition tabulate :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "tabulate A x = (THE y. (x, y) \<in> A)"

lemma tabulate:
  assumes "\<exists>! y. (x, y) \<in> A" "(x, y) \<in> A"
  shows "tabulate A x = y"
  using assms
  by (metis tabulate_def the_equality)

lemma tabulate_codomain:
  assumes "\<exists>! y. (x, y) \<in> A"
  shows "(x, tabulate A x) \<in> A"
  using assms
  by (metis tabulate)

lemma tabulate_value:
  assumes "y = tabulate A x" "\<exists>! y. (x, y) \<in> A"
  shows "(x, y) \<in> A"
  using assms
  by (metis tabulate)

abbreviation cells_to_color_fun_pairs :: "nat set list \<Rightarrow> (nat \<times> color) set" where
  "cells_to_color_fun_pairs cs \<equiv> 
    (\<Union> (set (map2 (\<lambda>cl c. (\<lambda>v. (v, c)) ` cl) cs [0..<List.length cs])))"

definition cells_to_color_fun :: "nat set list \<Rightarrow> nat \<Rightarrow> color" where
  "cells_to_color_fun cs = tabulate (cells_to_color_fun_pairs cs)"

lemma ex1_cells_to_color_fun_pairs:
  assumes "cells_ok n cs"
  shows "\<forall> v < n. \<exists>! c. (v, c) \<in> cells_to_color_fun_pairs cs"
proof (rule allI, rule impI)
  fix v
  assume "v < n"
  then obtain c where "c < List.length cs" "v \<in> cs ! c"
    using assms
    unfolding cells_ok_def
    by (metis Union_iff atLeastLessThan_iff in_set_conv_nth zero_le)
  then have *: "(cs ! c, c) \<in> set (zip cs [0..<List.length cs])"
               "(v, c) \<in> (\<lambda>v. (v, c)) ` (cs ! c)"
     by (auto simp add: set_zip)

  let ?A = "cells_to_color_fun_pairs cs"
  show "\<exists>! c. (v, c) \<in> ?A"
  proof
    show "(v, c) \<in> ?A"
      using *
      by auto
  next
    fix c'
    assume "(v, c') \<in> ?A"
    then have "c' < List.length cs" "v \<in> cs ! c'"
      by (auto simp add: set_zip)
    then show "c' = c"
      using * `c < List.length cs` assms
      unfolding cells_ok_def
      by auto
  qed
qed

lemma cells_to_color_fun: 
  assumes "cells_ok n cs" "c < List.length cs" "v \<in> cs ! c"
  shows "cells_to_color_fun cs v = c"
  unfolding cells_to_color_fun_def
proof (rule tabulate)
  let ?A = "cells_to_color_fun_pairs cs"

  have "(cs ! c, c) \<in> set (zip cs [0..<List.length cs])"
    by (metis add_cancel_right_left assms(2) in_set_zip length_map map_nth nth_upt prod.sel(1) prod.sel(2))     
  then show "(v, c) \<in> ?A"
    using `v \<in> cs ! c`
    by auto

  have "v < n"
    using `cells_ok n cs` `c < List.length cs` `v \<in> cs ! c`
    unfolding cells_ok_def
    by auto
  then show "\<exists>!c. (v, c) \<in> ?A"
    using ex1_cells_to_color_fun_pairs[OF assms(1), rule_format, of v]
    by simp
qed

lemma cells_to_color_fun': 
  assumes "cells_ok n cs" 
          "c < List.length cs" "v < n" "cells_to_color_fun cs v = c"
  shows "v \<in> cs ! c"
proof-
  have "(v, c) \<in> cells_to_color_fun_pairs cs"
    using assms
    using tabulate_value[of c "cells_to_color_fun_pairs cs" v]  ex1_cells_to_color_fun_pairs
    unfolding cells_to_color_fun_def
    by presburger
  then show ?thesis
    by (auto simp add: set_zip)
qed
  
lemma cells_to_color_fun_image:
  assumes "cells_ok n cs"
  shows "cells_to_color_fun cs ` {0..<n} = {0..<List.length cs}"
proof safe
  fix v
  assume "v \<in> {0..<n}"
  then obtain c where "c < List.length cs" "cells_to_color_fun cs v = c"
    using assms cells_to_color_fun
    unfolding cells_ok_def
    by (smt (verit, ccfv_SIG) Union_iff in_set_conv_nth) 
  then show "cells_to_color_fun cs v \<in> {0..<List.length cs}"
    by simp
next
  fix c
  assume "c \<in> {0..<List.length cs}"
  then obtain v where "v \<in> {0..<n}" "v \<in> cs ! c"
    using assms
    unfolding cells_ok_def
    by (metis Union_iff atLeastLessThan_iff equals0I nth_mem)
  then show "c \<in> cells_to_color_fun cs ` {0..<n}"
    using \<open>c \<in> {0..<List.length cs}\<close> assms cells_to_color_fun by fastforce
qed

definition cells_to_coloring where
  "cells_to_coloring n cs = color_fun_to_coloring n (cells_to_color_fun cs)"

lemma color_list_cells_to_coloring [simp]:
  assumes "cells_ok n cs"
  shows "color_list (cells_to_coloring n cs) = map (cells_to_color_fun cs) [0..<n]"
  unfolding cells_to_coloring_def color_fun_to_coloring_def
proof (rule coloring_inverse)
  show "map (cells_to_color_fun cs) [0..<n] \<in> {cs. \<exists>k. set cs = {0..<k}}"
    using assms cells_to_color_fun_image by auto  
qed

lemma length_cells_to_coloring [simp]:
  assumes "cells_ok n cs"
  shows "length (cells_to_coloring n cs) = n"
  using assms
  by (simp add: length.rep_eq)

lemma max_color_cells_to_coloring [simp]:
  assumes "cells_ok n cs" "cs \<noteq> []"
  shows "max_color (cells_to_coloring n cs) = List.length cs - 1"
  by (simp add: assms(1) assms(2) cells_to_color_fun_image max_color.rep_eq)


lemma colors_cells_to_coloring [simp]:
  assumes "cells_ok n cs"
  shows "colors (cells_to_coloring n cs) = [0..<List.length cs]"
  using assms
  unfolding colors_def num_colors_def
  by (smt (verit, ccfv_threshold) MaxAtLeastLessThan One_nat_def Suc_pred add.commute cells_to_color_fun_image color_list_cells_to_coloring last_in_set length_pos_if_in_set list.set_map list.size(3) max_color.rep_eq plus_1_eq_Suc set_upt upt_0)


lemma num_colors_cells_to_coloring [simp]:
  assumes "cells_ok n cs"
  shows "num_colors (cells_to_coloring n cs) = List.length cs"
  by (metis assms colors_cells_to_coloring colors_def length_upt minus_nat.diff_0)

lemma cell_cells_to_coloring:
  assumes "cells_ok n cs" "c < List.length cs"
  shows "cell (cells_to_coloring n cs) c = cs ! c"
proof safe
  fix v
  let ?cl = "cells_to_coloring n cs"
  assume "v \<in> cell ?cl c"
  then have "v < length ?cl" "color_fun ?cl v = c"
    unfolding cell_def
    by auto
  then show "v \<in> cs ! c"
    using assms(1) cells_to_color_fun'[OF assms, of v]
    by (simp add:color_fun.rep_eq) 
next
  fix v
  assume "v \<in> cs ! c"
  then have "v \<in> \<Union> (set cs)"
    using assms(2) nth_mem
    by auto
  then have "v < n"
    using assms
    unfolding cells_ok_def
    by simp
  then show "v \<in> cell (cells_to_coloring n cs) c"
    using assms
    unfolding cell_def
    using \<open>v \<in> cs ! c\<close> cells_to_color_fun color_fun.rep_eq by force 
qed

lemma cells_cells_to_coloring:
  assumes "cells_ok n cs"
  shows "cells (cells_to_coloring n cs) = cs"
  using assms
  unfolding cells_def
  by (metis cell_cells_to_coloring cells_def colors_cells_to_coloring length_cells length_map map_nth nth_cells nth_equalityI)
  
  
text\<open>------------------------------------------------------\<close>
subsection\<open>Finer colorings\<close>
text\<open>------------------------------------------------------\<close>

text \<open>Check if the color \<pi>' refines the coloring \<pi> - each cells of \<pi>' is a subset of a cell of \<pi>\<close>
definition finer :: "coloring \<Rightarrow> coloring \<Rightarrow> bool" (infixl "\<preceq>" 100) where
  "finer \<pi>' \<pi> \<longleftrightarrow> length \<pi>' = length \<pi> \<and> 
  (\<forall> v1 < length \<pi>. \<forall> v2 < length \<pi>. 
      color_fun \<pi> v1 < color_fun \<pi> v2 \<longrightarrow> color_fun \<pi>' v1 < color_fun \<pi>' v2)"

definition finer_strict :: "coloring \<Rightarrow> coloring \<Rightarrow> bool"  (infixl "\<prec>" 100) where
  "finer_strict \<pi> \<pi>' \<longleftrightarrow> \<pi> \<preceq> \<pi>' \<and> \<pi> \<noteq> \<pi>'" 

lemma finer_length:
  assumes "finer \<pi>' \<pi>"
  shows "length \<pi>' = length \<pi>"
  using assms
  by (simp add: finer_def)

lemma finer_refl:
  shows "finer \<pi> \<pi>"
  unfolding finer_def
  by auto

lemma finer_trans:
  assumes "finer \<pi>1 \<pi>2" "finer \<pi>2 \<pi>3"
  shows "finer \<pi>1 \<pi>3"
  using assms
  using finer_def 
  by auto


lemma finer_same_color:
  assumes "\<pi>' \<preceq> \<pi>" "v1 < length \<pi>" "v2 < length \<pi>" "color_fun \<pi>' v1 = color_fun \<pi>' v2" 
  shows "color_fun \<pi> v1 = color_fun \<pi> v2"
  using assms
  unfolding finer_def
  by (metis less_imp_not_eq less_linear)
  
  
lemma finer_cell_subset:
  assumes "finer \<pi>' \<pi>"
  shows "\<forall> C' \<in> set (cells \<pi>'). \<exists> C \<in> set (cells \<pi>). C' \<subseteq> C"
proof safe
  fix C'
  assume "C' \<in> set (cells \<pi>')"
  then obtain c' where "c' < num_colors \<pi>'" "C' = cell \<pi>' c'"
    by (metis index_of_in_set length_cells nth_cells)
  then obtain v where "v \<in> cell \<pi>' c'"
    using cell_non_empty by auto
  then have "v < length \<pi>'" "color_fun \<pi>' v = c'"
    unfolding cell_def
    by auto
  have "length \<pi>' = length \<pi>"
    using assms finer_length 
    by simp
  let ?C = "cell \<pi> (color_fun \<pi> v)"
  have "color_fun \<pi> v \<in> set (colors \<pi>)"
    using `v < length \<pi>'` `length \<pi>' = length \<pi>`
    using color_fun_in_colors
    by simp
  then have "?C \<in> set (cells \<pi>)"
    unfolding cells_def
    by simp
  moreover
  have "C' \<subseteq> ?C"
  proof
    fix v'
    assume "v' \<in> C'"
    then have "v' < length \<pi>'" "color_fun \<pi>' v' = color_fun \<pi>' v"
      using \<open>C' \<in> set (cells \<pi>')\<close>  \<open>C' = cell \<pi>' c'\<close> \<open>v \<in> cell \<pi>' c'\<close> \<open>v' \<in> C'\<close> 
      by (auto simp add: cell_def)
    then have "color_fun \<pi> v' = color_fun \<pi> v"
      using \<open>v < length \<pi>'\<close> \<open>finer \<pi>' \<pi>\<close> finer_same_color 
      by (metis finer_def) 
    then show "v' \<in> ?C"
      using \<open>v' < length \<pi>'\<close> \<open>length \<pi>' = length \<pi>\<close>
      unfolding cell_def
      by simp
  qed
  ultimately
  show "\<exists> C \<in> set (cells \<pi>). C' \<subseteq> C"
    by blast
qed

lemma finer_cell_subset1:
  assumes "finer \<pi>' \<pi>"
  shows "\<forall> C' \<in> set (cells \<pi>'). \<exists>! C \<in> set (cells \<pi>). C' \<subseteq> C"
proof
  fix C'
  assume "C' \<in> set (cells \<pi>')"
  {
    fix C1 C2
    assume "C1 \<in> set (cells \<pi>)" "C2 \<in> set (cells \<pi>)" "C' \<subseteq> C1" "C' \<subseteq> C2"
    then have "C1 = C2"
      by (smt (verit, best) Int_empty_right Int_left_commute \<open>C' \<in> set (cells \<pi>')\<close> cell_non_empty cells_disjunct index_of_in_set inf.absorb_iff2 le_iff_inf length_cells nth_cells)
  }
  then show "\<exists>! C \<in> set (cells \<pi>). C' \<subseteq> C"
    using finer_cell_subset[OF assms]
    by (meson \<open>C' \<in> set (cells \<pi>')\<close>)
qed

lemma finer_cell_subset':
  assumes "finer \<pi>' \<pi>"
  shows "\<forall> C \<in> set (cells \<pi>). \<exists> Cs \<subseteq> set (cells \<pi>'). Cs \<noteq> {} \<and> C = \<Union> Cs"
proof safe
  fix C
  assume "C \<in> set (cells \<pi>)"
  then obtain c where "c < num_colors \<pi>" "C = cell \<pi> c"
    by (metis index_of_in_set length_cells nth_cells)
  let ?Cs = "(\<lambda> v. cell \<pi>' (color_fun \<pi>' v)) ` C"
  have "?Cs \<subseteq> set (cells \<pi>')"
  proof safe
    fix v
    assume "v \<in> C"
    then show "cell \<pi>' (color_fun \<pi>' v) \<in> set (cells \<pi>')"
      unfolding cells_def
      using \<open>C = cell \<pi> c\<close> assms cell_def color_fun_in_colors finer_length by auto
  qed
  moreover
  have "?Cs \<noteq> {}"
    using \<open>C \<in> set (cells \<pi>)\<close> cells_non_empty by blast
  moreover
  have "C = \<Union> ?Cs"
  proof safe
    fix v
    assume "v \<in> C" 
    have "v \<in> cell \<pi>' (color_fun \<pi>' v)"
      using finer_length[OF assms] `v \<in> C` `C = cell \<pi> c`
      unfolding cell_def
      by auto
    then show "v \<in> \<Union> ?Cs"
      using `v \<in> C`
      by auto
  next
    fix v v'
    assume "v \<in> C" "v' \<in> cell \<pi>' (color_fun \<pi>' v)"
    then show "v' \<in> C"
      using finer_same_color[OF assms, of v v'] `C = cell \<pi> c` `c < num_colors \<pi>` finer_length[OF assms]
      unfolding cell_def
      by auto
  qed
  ultimately
  show "\<exists> Cs \<subseteq> set (cells \<pi>'). Cs \<noteq> {} \<and> C = \<Union> Cs"
    by blast
qed

lemma cell_subset_finer:
  assumes "length \<pi>' = length \<pi>"
          "\<forall> C' \<in> set (cells \<pi>'). \<exists> C \<in> set (cells \<pi>). C' \<subseteq> C"
          "\<forall> p1 p2 c1 c2. c1 < num_colors \<pi>' \<and> p1 < num_colors \<pi> \<and>
                          c2 < num_colors \<pi>' \<and> p2 < num_colors \<pi> \<and>
                          cell \<pi>' c1 \<subseteq> cell \<pi> p1 \<and>
                          cell \<pi>' c2 \<subseteq> cell \<pi> p2 \<and> c1 \<le> c2 \<longrightarrow> p1 \<le> p2"
  shows "finer \<pi>' \<pi>"
unfolding finer_def
proof safe
  show "length \<pi>' = length \<pi>"
    by fact
next
  fix v1 v2
  assume "v1 < length \<pi>" "v2 < length \<pi>" "color_fun \<pi> v1 < color_fun \<pi> v2"
  show "color_fun \<pi>' v1 < color_fun \<pi>' v2"
  proof-
    let ?p1 = "color_fun \<pi> v1" 
    let ?p2 = "color_fun \<pi> v2"
    let ?c1 = "color_fun \<pi>' v1"
    let ?c2 = "color_fun \<pi>' v2" 
    let ?C1' = "cell \<pi>' ?c1"
    let ?C2' = "cell \<pi>' ?c2"
    have "?C1' \<in> set (cells \<pi>')"
      by (simp add: \<open>v1 < length \<pi>\<close> assms(1) cells_def color_fun_in_colors)
    then obtain C1 where "?C1' \<subseteq> C1" "C1 \<in> set (cells \<pi>)"
      using assms(2) by fastforce     
    have "?C2' \<in> set (cells \<pi>')"
      by (simp add: \<open>v2 < length \<pi>\<close> assms(1) cells_def color_fun_in_colors)
    then obtain C2 where "?C2' \<subseteq> C2" "C2 \<in> set (cells \<pi>)"
      using assms(2) by fastforce
    have "v1 \<in> C1"
      using \<open>cell \<pi>' (color_fun \<pi>' v1) \<subseteq> C1\<close> \<open>v1 < length \<pi>\<close> assms(1) cell_def
       by auto
    then have "C1 = cell \<pi> ?p1"
      using `C1 \<in> set (cells \<pi>)`
      unfolding cells_def cell_def
      by auto
    moreover 
    have "v2 \<in> C2"
      using \<open>cell \<pi>' (color_fun \<pi>' v2) \<subseteq> C2\<close> \<open>v2 < length \<pi>\<close> assms(1) cell_def
       by auto    
    then have "C2 = cell \<pi> ?p2"
      using `C2 \<in> set (cells \<pi>)`
      unfolding cells_def cell_def
      by auto
    moreover 
    have "?c1 < num_colors \<pi>'"
      using \<open>v1 < length \<pi>\<close> assms(1) 
      by (metis atLeast0LessThan atLeastLessThan_upt color_fun_in_colors colors_def lessThan_iff)
    moreover 
    have "?c2 < num_colors \<pi>'"
      using \<open>v2 < length \<pi>\<close> assms(1) 
      by (metis atLeast0LessThan atLeastLessThan_upt color_fun_in_colors colors_def lessThan_iff)   
    moreover 
    have "?p1 < num_colors \<pi>" "?p2 < num_colors \<pi>"
      using \<open>v1 < length \<pi>\<close> \<open>v2 < Coloring.length \<pi>\<close> color_fun_in_colors colors_def
      by auto
    ultimately show "?c1 < ?c2"
      using `?C1' \<subseteq> C1` `?C2' \<subseteq> C2` 
      using `color_fun \<pi> v1 < color_fun \<pi> v2`
      using assms(3)
      by (meson leD linorder_le_less_linear)
  qed
qed

lemma finer_color_fun_non_decreasing:
  assumes "\<pi>' \<preceq> \<pi>" "v < length \<pi>"
  shows "color_fun \<pi>' v \<ge> color_fun \<pi> v"
  using assms
proof (induction "color_fun \<pi> v" arbitrary: v rule: nat_less_induct)
  case 1
  show ?case
  proof (cases "color_fun \<pi> v = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "color_fun \<pi> v - 1 \<in> set (colors \<pi>)"
      using "1.prems"(2) color_fun_in_colors colors_def less_imp_diff_less by auto
    then obtain v' where "v' < length \<pi>" "color_fun \<pi> v' = color_fun \<pi> v - 1"
      using ex_color_color_fun[of "color_fun \<pi> v - 1" \<pi>] False
      by blast
    then have "color_fun \<pi>' v' \<ge> color_fun \<pi> v'"
      using 1 False
      by (metis bot_nat_0.not_eq_extremum diff_less zero_less_one)
    moreover
    have "color_fun \<pi>' v' < color_fun \<pi>' v"
      using `color_fun \<pi> v' = color_fun \<pi> v - 1` False
      using assms `v < length \<pi>` `v' < length \<pi>` 
      unfolding finer_def
      by simp
    ultimately show ?thesis
      using `color_fun \<pi> v' = color_fun \<pi> v - 1` False
      by linarith
  qed
qed

lemma finer_singleton:
  assumes "{v} \<in> set (cells \<pi>1)" "v < length \<pi>1" "finer \<pi>2 \<pi>1"
  shows "{v} \<in> set (cells \<pi>2)"
proof-
  have "length \<pi>1 = length \<pi>2"
    using `finer \<pi>2 \<pi>1`
    unfolding finer_def
    by simp

  obtain c where c: "c \<in> set (colors \<pi>1)" "color_fun \<pi>1 v = c" "cell \<pi>1 c = {v}"
    using assms
    by (smt (verit) cell_def color_fun_in_colors in_set_conv_nth length_cells mem_Collect_eq nth_cells singletonI)
  let ?c = "color_fun \<pi>2 v"
  have "cell \<pi>2 ?c = {v}"
  proof-
    have "\<forall> v' < length \<pi>1. v' \<noteq> v \<longrightarrow> color_fun \<pi>2 v' \<noteq> ?c"
    proof safe
      fix v'
      assume "v' < length \<pi>1" "color_fun \<pi>2 v' = color_fun \<pi>2 v" "v' \<noteq> v"
      then have "color_fun \<pi>1 v' = color_fun \<pi>1 v"
        using assms(2-3) finer_same_color by blast
      then have "v' \<in> cell \<pi>1 c"
        by (simp add: \<open>v' < length \<pi>1\<close> c(2) cell_def)
      then show False
        using assms c \<open>v' \<noteq> v\<close>
        by blast
    qed
    then show ?thesis
      using c(3) `length \<pi>1 = length \<pi>2`
      unfolding cell_def
      by auto
  qed
  then show ?thesis
    using `v < length \<pi>1` `length \<pi>1 = length \<pi>2` color_fun_in_colors 
    unfolding cells_def
    by auto
qed

lemma cells_inj:
  assumes "length \<pi> = length \<pi>'" "cells \<pi> = cells \<pi>'"
  shows "\<pi> = \<pi>'"
proof (rule coloring_eqI)
  show "length \<pi> = length \<pi>'"
    by fact
next
  show "\<forall>v<Coloring.length \<pi>. color_fun \<pi> v = color_fun \<pi>' v"
  proof safe
    fix v
    assume "v < length \<pi>"
    have "cell \<pi> (color_fun \<pi> v) = cell \<pi>' (color_fun \<pi> v)"
      using assms
      unfolding cells_def
      by (metis \<open>v < Coloring.length \<pi>\<close> assms(2) color_fun_in_colors colors_def length_cells map_eq_conv)
    then show "color_fun \<pi> v = color_fun \<pi>' v"
      using assms(1) cells_ok[of \<pi>']
      by (metis (mono_tags, lifting) \<open>v < Coloring.length \<pi>\<close> cell_def mem_Collect_eq)
  qed
qed

lemma finer_cells_order:
  assumes "\<pi>' \<preceq> \<pi>" "c < num_colors \<pi>" "c' < num_colors \<pi>'" "cell \<pi>' c' = cell \<pi> c"
  shows "c \<le> c'"
proof-
 obtain v where "v < length \<pi>" "color_fun \<pi> v = c"
   using \<open>c < num_colors \<pi>\<close> ex_color ex_color_color_fun by blast
  then have "color_fun \<pi>' v = c'"
    using \<open>cell \<pi>' c' = cell \<pi> c\<close>
    unfolding cell_def
    by auto
  show ?thesis
    using finer_color_fun_non_decreasing[OF assms(1)]
    using \<open>color_fun \<pi> v = c\<close> \<open>color_fun \<pi>' v = c'\<close> \<open>v < Coloring.length \<pi>\<close>
    by blast
qed

lemma finer_cell_set_eq:
  assumes "\<pi>' \<preceq> \<pi>" "set (cells \<pi>) = set (cells \<pi>')"
  shows "cells \<pi> = cells \<pi>'"
proof-
  have "num_colors \<pi> = num_colors \<pi>'"
    by (metis assms(2) distinct_card distinct_cells length_cells)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain c where "c < num_colors \<pi>" "cell \<pi> c \<noteq> cell \<pi>' c"
      by (metis \<open>num_colors \<pi> = num_colors \<pi>'\<close> length_cells nth_cells nth_equalityI)
    then obtain c' where "c' < num_colors \<pi>" "cell \<pi> c = cell \<pi>' c'"
      by (metis \<open>num_colors \<pi> = num_colors \<pi>'\<close> assms(2) in_set_conv_nth length_cells nth_cells)
    have "c < c'"
      by (metis \<open>c < num_colors \<pi>\<close> \<open>c' < num_colors \<pi>\<close> \<open>cell \<pi> c = cell \<pi>' c'\<close> \<open>cell \<pi> c \<noteq> cell \<pi>' c\<close> \<open>num_colors \<pi> = num_colors \<pi>'\<close> assms(1) finer_cells_order order_le_neq_trans)

    have *: "\<forall> cc. c < cc \<and> cc < num_colors \<pi> \<longrightarrow> (\<exists> cc'. c' < cc' \<and> cc' < num_colors \<pi>' \<and> cell \<pi> cc = cell \<pi>' cc')"
    proof safe
      fix cc
      assume "c < cc" "cc < num_colors \<pi>"
      then obtain cc' where "cc' < num_colors \<pi>'" "cell \<pi> cc = cell \<pi>' cc'"
        by (metis assms(2) in_set_conv_nth length_cells nth_cells)
      obtain v where "v < length \<pi>" "color_fun \<pi> v = c" "color_fun \<pi>' v = c'" 
        by (metis (mono_tags, lifting) \<open>c' < num_colors \<pi>\<close> \<open>cell \<pi> c = cell \<pi>' c'\<close> \<open>num_colors \<pi> = num_colors \<pi>'\<close> atLeast0LessThan cell_def colors_def ex_color_color_fun lessThan_iff mem_Collect_eq set_upt)
      obtain v' where "v' < length \<pi>" "color_fun \<pi> v' = cc" "color_fun \<pi>' v' = cc'"
        by (smt (verit, ccfv_threshold) \<open>cc' < num_colors \<pi>'\<close> \<open>cell \<pi> cc = cell \<pi>' cc'\<close> atLeast0LessThan cell_def colors_def ex_color_color_fun lessThan_iff mem_Collect_eq set_upt)
      have "c' < cc'"
        using \<open>\<pi>' \<preceq> \<pi>\<close> \<open>c < cc\<close>
        unfolding finer_def
        using \<open>color_fun \<pi> v = c\<close> \<open>color_fun \<pi> v' = cc\<close> \<open>color_fun \<pi>' v = c'\<close> \<open>color_fun \<pi>' v' = cc'\<close> \<open>v < Coloring.length \<pi>\<close> \<open>v' < Coloring.length \<pi>\<close>
        by blast
      then show "\<exists>cc'>c'. cc' < num_colors \<pi>' \<and> cell \<pi> cc = cell \<pi>' cc'"
        using \<open>cc' < num_colors \<pi>'\<close> \<open>cell \<pi> cc = cell \<pi>' cc'\<close> by blast
    qed

    let ?f = "\<lambda> cc. SOME cc'. c' < cc' \<and> cc' < num_colors \<pi>' \<and> cell \<pi> cc = cell \<pi>' cc'"

    have **: "\<forall> cc. c < cc \<and> cc < num_colors \<pi> \<longrightarrow> c' < ?f cc \<and> ?f cc < num_colors \<pi>' \<and> cell \<pi> cc = cell \<pi>' (?f cc)"
      using *
      by (smt tfl_some)

    have "card {c+1..<num_colors \<pi>} \<le> card {c'+1..<num_colors \<pi>'}"
    proof (rule card_inj_on_le)
      show "inj_on ?f {c + 1..<num_colors \<pi>}"
        unfolding inj_on_def
      proof safe
        fix x y
        assume "x \<in> {c + 1..<num_colors \<pi>}" "y \<in> {c + 1..<num_colors \<pi>}" "?f x = ?f y"
        then have "c < x" "x < num_colors \<pi>" "c < y" "y < num_colors \<pi>"
          by auto
        then have "cell \<pi> x = cell \<pi>' (?f x)" "cell \<pi> y = cell \<pi>' (?f y)"
          using **
          by blast+
        then have "cell \<pi> x = cell \<pi> y"
          using `?f x = ?f y`
          by simp
        then show "x = y"
          by (metis \<open>x < num_colors \<pi>\<close> \<open>y < num_colors \<pi>\<close> distinct_cells length_cells nth_cells nth_eq_iff_index_eq)
      qed
    next
      show "?f ` {c + 1..<num_colors \<pi>} \<subseteq> {c' + 1..<num_colors \<pi>'}"
      proof safe
        fix cc
        assume "cc \<in> {c + 1..<num_colors \<pi>}"
        then have "cc > c" "cc < num_colors \<pi>"
          by auto
        then show "?f cc \<in> {c' + 1..<num_colors \<pi>'}"
          using **
          by fastforce
      qed
    next
      show "finite {c' + 1..<num_colors \<pi>'}"
        by simp
    qed
    then show False
      using `c < c'` `c < num_colors \<pi>` `c' < num_colors \<pi>` `num_colors \<pi> = num_colors \<pi>'`
      using card_atLeastLessThan[of "c+1" "num_colors \<pi>"]
      using card_atLeastLessThan[of "c'+1" "num_colors \<pi>'"]
      by auto
  qed
qed

lemma num_colors_finer_strict:
  assumes "\<pi>' \<prec> \<pi>"
  shows "num_colors \<pi>' > num_colors \<pi>"
proof-
  have "cells \<pi> \<noteq> cells \<pi>'"
    using assms cells_inj[of \<pi> \<pi>']
    using finer_length finer_strict_def
    by fastforce
  let ?f = "\<lambda> C. SOME C'. C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C"

  have *: "\<forall> C \<in> set (cells \<pi>). ?f C \<in> set (cells \<pi>') \<and> ?f C \<subseteq> C"
  proof
    fix C
    assume "C \<in> set (cells \<pi>)"
    then obtain Cs where "C = \<Union> Cs" "Cs\<subseteq>set (cells \<pi>')" "Cs \<noteq> {}"
      using finer_cell_subset'[of \<pi>' \<pi>] assms
      unfolding finer_strict_def
      by meson
    then have "\<exists> C' \<in> set (cells \<pi>'). C' \<subseteq> C"
      by auto
    then show "?f C \<in> set (cells \<pi>') \<and> ?f C \<subseteq> C"
      by (metis (no_types, lifting) verit_sko_ex')
  qed

  have "inj_on ?f (set (cells \<pi>))"
    unfolding inj_on_def
  proof (rule ballI, rule ballI, rule impI)
    fix C1 C2
    assume **: "C1 \<in> set (cells \<pi>)" "C2 \<in> set (cells \<pi>)"
               "?f C1 = ?f C2"
    let ?C' = "(SOME C'. C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C1)"
    have "?C' \<in> set (cells \<pi>')" "?C' \<subseteq> C1" "?C' \<subseteq> C2"
      using * **
      by auto
    then show "C1 = C2"
      using cells_ok[of \<pi>] cells_ok[of \<pi>']
      unfolding cells_ok_def
      by (metis (no_types, lifting) "**"(1) "**"(2) Int_subset_iff index_of_in_set subset_empty)
  qed

  have "?f ` set (cells \<pi>) \<subset> set (cells \<pi>')"
  proof
    show "?f ` set (cells \<pi>) \<subseteq> set (cells \<pi>')"
    proof safe
      fix C
      assume "C \<in> set (cells \<pi>)"
      then obtain Cs where "C = \<Union> Cs" "Cs\<subseteq>set (cells \<pi>')" "Cs \<noteq> {}"
        using finer_cell_subset'[of \<pi>' \<pi>] assms
        unfolding finer_strict_def
        by meson
      then have "\<exists> C' \<in> set (cells \<pi>'). C' \<subseteq> C"
        by auto
      then show "?f C \<in> set (cells \<pi>')"
        by (smt (verit, ccfv_SIG) tfl_some)
    qed
  next
    show "?f ` set (cells \<pi>) \<noteq> set (cells \<pi>')"
    proof (rule ccontr)
      assume contr: "\<not> ?thesis"
      then have "card (set (cells \<pi>)) = card (set (cells \<pi>'))"
        using \<open>inj_on ?f (set (cells \<pi>))\<close> card_image
        by fastforce

      have ex1: "\<forall> C \<in> set (cells \<pi>). \<exists>! C' \<in> set (cells \<pi>'). C' \<subseteq> C"
      proof (rule, rule)
        fix C
        assume "C \<in> set (cells \<pi>)"
        then show "?f C \<in> set (cells \<pi>') \<and> ?f C \<subseteq> C"
          using "*" by blast
      next
        fix C C'
        assume "C \<in> set (cells \<pi>)" "C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C"
        let ?g = "\<lambda> C'. THE C. C \<in> set (cells \<pi>) \<and> C \<supseteq> C'"
        have gex1: "\<forall> C' \<in> set (cells \<pi>'). \<exists>! C \<in> set (cells \<pi>). C \<supseteq> C'"
          by (meson assms finer_cell_subset1 finer_strict_def)
        have "inj_on ?g (set (cells \<pi>'))"
        proof-
          have "?g ` (set (cells \<pi>')) = set (cells \<pi>)"
          proof safe
            fix C' 
            assume "C' \<in> set (cells \<pi>')"
            then show "?g C' \<in> set (cells \<pi>)"
              using gex1 the_eq_trivial
              by (smt (verit, ccfv_threshold) the_equality)
          next
            fix C
            assume "C \<in> set (cells \<pi>)"
            then have "?g (?f C) = C"
              by (smt (verit, ccfv_threshold) "*" gex1 someI_ex the_equality)
            then show "C \<in> ?g ` set (cells \<pi>')"
              using \<open>C \<in> set (cells \<pi>)\<close> contr by blast
          qed
            
          then show ?thesis
            using `card (set (cells \<pi>)) = card (set (cells \<pi>'))`
            by (simp add: eq_card_imp_inj_on)
        qed
        moreover
        have "?g C' = ?g (?f C)"
        proof-
          have "?g (?f C) = C"
            by (smt (verit, del_insts) \<open>C \<in> set (cells \<pi>)\<close> \<open>C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C\<close> gex1 someI_ex the_equality)
          moreover
          have "?g C' = C"
            by (simp add: \<open>C \<in> set (cells \<pi>)\<close> \<open>C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C\<close> gex1 the1_equality)
          ultimately
          show ?thesis
            by simp
        qed
        ultimately show "C' = ?f C"
          using `C \<in> set (cells \<pi>)` * `C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C`
          unfolding inj_on_def
          by blast
        qed
      have "\<forall> C \<in> set (cells \<pi>). ?f C = C"
      proof
        fix C
        assume "C \<in> set (cells \<pi>)"
        then obtain Cs where "Cs \<subseteq> set (cells \<pi>')" "\<Union>Cs = C"
          by (metis assms finer_cell_subset' finer_strict_def)
        then have "\<forall> C' \<in> Cs. C' \<in> set (cells \<pi>') \<and> C' \<subseteq> C"
          by auto
        then have "\<exists>! C'. C' \<in> Cs"
          using `C \<in> set (cells \<pi>)` ex1
          by (metis Sup_bot_conv(1) \<open>\<Union> Cs = C\<close> cells_non_empty)
        then have "Cs = {C}"
          by (metis \<open>\<Union> Cs = C\<close> cSup_singleton empty_iff is_singletonI' is_singleton_the_elem)
        then have "C \<in> set (cells \<pi>')"
          using \<open>Cs \<subseteq> set (cells \<pi>')\<close>
          by auto
        moreover
        have "?f C \<in> set (cells \<pi>')"  "?f C \<subseteq> C"
          using * \<open>C \<in> set (cells \<pi>)\<close>
          by auto
        ultimately
        show "?f C = C"
          using ex1
          using \<open>C \<in> set (cells \<pi>)\<close>
          by blast
      qed
      then have "set (cells \<pi>) = set (cells \<pi>')"
        using contr by force
      then show False
        using `cells \<pi> \<noteq> cells \<pi>'`
        using assms finer_cell_set_eq finer_strict_def by blast
    qed
  qed
  then have "card (?f ` set (cells \<pi>)) < card (set (cells \<pi>'))"
    by (meson List.finite_set psubset_card_mono)
  moreover 
  have "card (?f ` set (cells \<pi>)) = card (set (cells \<pi>))"
  proof (rule card_image)
    show "inj_on ?f (set (cells \<pi>))"
      by fact
  qed
  ultimately
  have "card (set (cells \<pi>)) < card (set (cells \<pi>'))"
    by simp
  then have "List.length (cells \<pi>') > List.length (cells \<pi>)"
    using distinct_card[of "cells \<pi>"] distinct_card[of "cells \<pi>'"]
    by (simp add: distinct_cells)
  then show ?thesis
    by auto             
qed

text \<open>A coloring is discrete if each vertex is colored by a different color {0..<n}\<close>
definition discrete :: "coloring \<Rightarrow> bool" where
  "discrete \<pi> \<longleftrightarrow> set (colors \<pi>) = {0..<length \<pi>}"

lemma discrete_coloring_is_permutation [simp]:
  assumes "discrete \<pi>"
  shows "is_perm_fun (length \<pi>) (color_fun \<pi>)"
  using assms finite_surj_inj[of "{0..<length \<pi>}" "color_fun \<pi>"] all_colors
  unfolding discrete_def is_perm_fun_def
  unfolding bij_betw_def
  by auto

lemma discrete_singleton:
  assumes "discrete \<pi>" "v < length \<pi>"
  shows "cell \<pi> (color_fun \<pi> v) = {v}"
proof-
  have f: "inj_on (color_fun \<pi>) {0..<length \<pi>}" "color_fun \<pi> ` {0..<length \<pi>} = {0..<length \<pi>}"
    using \<open>discrete \<pi>\<close>
    by (meson bij_betw_def discrete_coloring_is_permutation is_perm_fun_def)+
  then show ?thesis
    using \<open>v < length \<pi>\<close>
    unfolding cell_def inj_on_def
    by auto
qed

    
    
lemma discrete_cells_card1:
  assumes "discrete \<pi>" "C \<in> set (cells \<pi>)"
  shows "card C = 1"
proof-
  obtain c where "c \<in> set (colors \<pi>)" "C = cell \<pi> c"
    by (metis assms(2) ex_color index_of_in_set length_cells nth_cells)
  then obtain v where "C = {v}"
    by (metis assms(1) discrete_singleton ex_color_color_fun)
  thus ?thesis
    by simp
qed

lemma non_discrete_cells_card_gt1:
  assumes "\<not> discrete \<pi>"
  shows "\<exists> c \<in> set (colors \<pi>). card (cell \<pi> c) > 1"
proof (rule ccontr)
  assume "\<not> ?thesis"
  moreover
  have "\<forall> c \<in> set (colors \<pi>). card (cell \<pi> c) \<ge> 1"
    by (metis atLeast0LessThan atLeastLessThan_upt card_0_eq cell_finite cell_non_empty colors_def lessThan_iff less_one linorder_le_less_linear)
  ultimately
  have *: "\<forall> c \<in> set (colors \<pi>). card (cell \<pi> c) = 1"
    by force
  have "card ({0..<length \<pi>}) = card (set (colors \<pi>))"
  proof (rule bij_betw_same_card)
    show "bij_betw (color_fun \<pi>) {0..<length \<pi>} (set (colors \<pi>))"
      unfolding bij_betw_def 
    proof 
      show "inj_on (color_fun \<pi>) {0..<Coloring.length \<pi>}"
        unfolding inj_on_def
      proof safe
        fix v1 v2
        assume "v1 \<in> {0..<length \<pi>}" "v2 \<in> {0..<length \<pi>}" "color_fun \<pi> v1 = color_fun \<pi> v2"
        then have "v1 \<in> cell \<pi> (color_fun \<pi> v1)" "v2 \<in> cell \<pi> (color_fun \<pi> v1)"
          unfolding cell_def
          by auto
        moreover have "card (cell \<pi> (color_fun \<pi> v1)) = 1"
          using * \<open>v1 \<in> {0..<length \<pi>}\<close> color_fun_in_colors
          by force
        ultimately show "v1 = v2"
          using card_le_Suc0_iff_eq[of "cell \<pi> (color_fun \<pi> v1)"]
          by auto
      qed
    next
      show "color_fun \<pi> ` {0..<Coloring.length \<pi>} = set (colors \<pi>)"
      proof safe
        fix v
        assume "v \<in> {0..<length \<pi>}"
        then show "color_fun \<pi> v \<in> set (colors \<pi>)"
          using color_fun_in_colors
          by force
      next
        fix c
        assume "c \<in> set (colors \<pi>)"
        then obtain v where "v \<in> cell \<pi> c"
          using *
          by fastforce
        then show "c \<in> color_fun \<pi> ` {0..<Coloring.length \<pi>}"
          unfolding cell_def
          by auto
      qed
    qed
  qed
  then have "length \<pi> = num_colors \<pi>"
    by (simp add: colors_def)
  then have "discrete \<pi>"
    unfolding discrete_def colors_def
    by auto
  then show False
    using assms
    by auto
  qed

definition discrete_coloring_perm :: "coloring \<Rightarrow> perm" where
  "discrete_coloring_perm \<alpha> = make_perm (length \<alpha>) (color_fun \<alpha>)"

lemma perm_dom_discrete_coloring_perm [simp]:
  assumes "discrete \<alpha>"
  shows "perm_dom (discrete_coloring_perm \<alpha>) = length \<alpha>"
  using assms
  unfolding discrete_coloring_perm_def
  by simp

lemma perm_fun_discrete_coloring_perm [simp]:
  assumes "discrete \<alpha>" "v < length \<alpha>"
  shows "perm_fun (discrete_coloring_perm \<alpha>) v = color_fun \<alpha> v"
  using assms
  unfolding discrete_coloring_perm_def
  by simp


text\<open>------------------------------------------------------\<close>
subsection\<open>Permute coloring\<close>
text\<open>------------------------------------------------------\<close>

text\<open>The effect of vertices perm on colors\<close>

definition perm_coloring :: "perm \<Rightarrow> coloring \<Rightarrow> coloring" where
  "perm_coloring p \<pi> = coloring (perm_reorder p (color_list \<pi>))"

lemma length_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "length (perm_coloring p \<pi>) = length \<pi>"
  using assms
  by (smt (verit) color_list eq_onp_same_args length.abs_eq length.rep_eq length_perm_reorder mem_Collect_eq perm_coloring_def set_perm_reorder)

lemma color_fun_perm_coloring:
  assumes "perm_dom p = length \<pi>"
  shows "color_fun (perm_coloring p \<pi>) = (!) (perm_reorder p (color_list \<pi>))"
  using assms
  by (smt (verit) color_fun.abs_eq color_list eq_onp_same_args length.rep_eq list.set_map map_nth mem_Collect_eq perm_coloring_def perm_dom_perm_inv perm_list_set perm_reorder set_upt)
  
lemma color_fun_perm_coloring_app:
  assumes "perm_dom p  = length \<pi>" 
  assumes "v < length \<pi>" 
  shows "color_fun (perm_coloring p \<pi>) v = ((color_fun \<pi>) \<circ> (perm_fun (perm_inv p))) v"
  using assms color_fun.rep_eq color_fun_perm_coloring length.rep_eq
  by auto

lemma perm_coloring_perm_fun [simp]:
  assumes "perm_dom p = length \<pi>" "v < length \<pi>"
  shows "color_fun (perm_coloring p \<pi>) (perm_fun p v) = color_fun \<pi> v"
  by (metis assms(1) assms(2) color_fun_perm_coloring_app comp_apply perm_dom_perm_inv perm_fun_perm_inv2 perm_fun_perm_inv_range perm_inv_inv)  

lemma max_color_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "max_color (perm_coloring p \<pi>) = max_color \<pi>"
  using assms
  by (metis color_fun.rep_eq color_fun_perm_coloring length.rep_eq length_perm_coloring length_perm_reorder list.set_map map_nth max_color.rep_eq perm_dom_perm_inv perm_list_set perm_reorder set_upt)

lemma num_colors_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "num_colors (perm_coloring p \<pi>) = num_colors \<pi>"
  using assms
  unfolding num_colors_def
  using length.rep_eq length_perm_coloring 
  by fastforce

lemma colors_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "colors (perm_coloring p \<pi>) = colors \<pi>"
  using assms num_colors_def num_colors_perm_coloring
  unfolding colors_def
  by simp

lemma perm_coloring_perm_id [simp]:
  shows "perm_coloring (perm_id (length \<pi>)) \<pi> = \<pi>"
  by (simp add: color_list_inverse length.rep_eq perm_coloring_def) 

lemma perm_coloring_perm_comp:
  assumes "perm_dom p1 = length \<pi>" "perm_dom p2 = length \<pi>"
  shows "perm_coloring (perm_comp p1 p2) \<pi>  = 
         perm_coloring p1 (perm_coloring p2 \<pi>)"
  using assms
  unfolding perm_coloring_def
  by (smt (verit, del_insts) color_list coloring_inverse length.rep_eq mem_Collect_eq perm_reorder_comp set_perm_reorder)

lemma perm_coloring_perm_inv_comp1 [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "perm_coloring (perm_inv p) (perm_coloring p \<pi>) = \<pi>"
  using assms
  by (metis perm_coloring_perm_comp perm_coloring_perm_id perm_comp_perm_inv1 perm_dom_perm_inv)

lemma perm_coloring_perm_inv_comp2 [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "perm_coloring p (perm_coloring (perm_inv p) \<pi>) = \<pi>"
  using assms
  by (metis perm_coloring_perm_inv_comp1 perm_dom_perm_inv perm_inv_inv)

lemma perm_coloring_inj:
  assumes "length \<pi> = perm_dom p" "length \<pi>' = perm_dom p" 
          "perm_coloring p \<pi> = perm_coloring p \<pi>'"
  shows "\<pi> = \<pi>'"
  using assms
  by (metis perm_coloring_perm_inv_comp1) 

lemma cell_perm_coloring [simp]: 
  assumes "perm_dom p = length \<pi>"
  shows "cell (perm_coloring p \<pi>) c = perm_fun_set p (cell \<pi> c)" (is "?lhs = ?rhs")
proof safe
  fix x
  assume "x \<in> ?lhs"
  then show "x \<in> ?rhs"
    using assms color_fun_perm_coloring_app
    unfolding cell_def
    by (smt (verit) comp_apply image_iff length_perm_coloring mem_Collect_eq perm_fun_perm_inv1 perm_fun_perm_inv_range perm_fun_set_def)
next
  fix x
  assume "x \<in> ?rhs"
  then show "x \<in> ?lhs"
    by (smt (verit, ccfv_SIG) assms cell_def image_iff length_perm_coloring mem_Collect_eq perm_coloring_perm_fun perm_comp_perm_inv2 perm_dom_perm_inv perm_fun_perm_inv_range perm_fun_set_def perm_inv_solve)
qed

lemma cells_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "cells (perm_coloring p \<pi>) = map (perm_fun_set p) (cells \<pi>)"
  using assms colors_perm_coloring
  unfolding cells_def
  by simp

lemma discrete_perm_coloring [simp]:
  assumes "perm_dom p = length \<pi>"
  shows "discrete (perm_coloring p \<pi>) \<longleftrightarrow> discrete \<pi>"
  using assms
  unfolding discrete_def
  by auto

lemma perm_coloring_finer:
  assumes "\<pi> \<preceq> \<pi>0" "perm_coloring \<sigma> \<pi> = \<pi>" "perm_dom \<sigma> = length \<pi>" "perm_dom \<sigma> = length \<pi>0"
  shows "perm_coloring \<sigma> \<pi>0 = \<pi>0"
proof (rule coloring_eqI)
  show "\<forall>v<length (perm_coloring \<sigma> \<pi>0). Coloring.color_fun (perm_coloring \<sigma> \<pi>0) v = Coloring.color_fun \<pi>0 v"
  proof safe
    fix v
    assume "v < length (perm_coloring \<sigma> \<pi>0)"
    then have "Coloring.color_fun \<pi> (perm_fun \<sigma> v) = Coloring.color_fun \<pi> v"
      using assms
      by (metis length_perm_coloring perm_coloring_perm_fun)
    then show "Coloring.color_fun (perm_coloring \<sigma> \<pi>0) v = Coloring.color_fun \<pi>0 v"
      using assms \<open>v < Coloring.length (perm_coloring \<sigma> \<pi>0)\<close>
      by (smt (verit) color_fun_perm_coloring_app comp_def finer_same_color length_perm_coloring perm_fun_perm_inv_range)
  qed
next
  show "Coloring.length (perm_coloring \<sigma> \<pi>0) = Coloring.length \<pi>0"
    using assms
    using length_perm_coloring
    by blast
qed

lemma color_fun_to_coloring_perm [simp]:
  assumes "perm_dom p = n" "\<exists> k. \<pi> ` {0..<n} = {0..<k}"
  shows "color_fun_to_coloring n (\<pi> \<circ> perm_fun (perm_inv p)) = 
         perm_coloring p (color_fun_to_coloring n \<pi>)" (is "?lhs = ?rhs")
proof (rule coloring_eqI)
  have *: "\<exists> k. (\<pi> \<circ> perm_fun (perm_inv p)) ` {0..<n} = {0..<k}"
    using assms
    by (metis image_comp list.set_map perm_dom_perm_inv perm_fun_list_def perm_inv_perm_list perm_list_set set_upt) 
    
  then show "length ?lhs = length ?rhs"
    using assms
    by simp
    
  show "\<forall> v < length ?lhs. color_fun ?lhs v = color_fun ?rhs v"
    using assms *
    by (simp add: color_fun_perm_coloring_app perm_fun_perm_inv_range) 
qed

lemma color_fun_to_coloring_perm':
  assumes "perm_dom p = n" "\<exists> k. \<pi> ` {0..<n} = {0..<k}"
          "\<forall> w < n. \<pi>' (perm_fun p w) = \<pi> w"
  shows "color_fun_to_coloring n \<pi>' = 
         perm_coloring p (color_fun_to_coloring n \<pi>)" (is "?lhs = ?rhs")
proof (rule coloring_eqI)
  obtain k where k: "\<pi> ` {0..<n} = {0..<k}"
    using assms
    by auto
  moreover
  have "\<forall> w < n. \<pi>' w = \<pi> (perm_fun (perm_inv p) w)"
    using assms
    by (metis perm_fun_perm_inv1 perm_fun_perm_inv_range) 
  moreover
  have "\<forall> w < n. perm_fun (perm_inv p) w < n"
    using assms(1)
    by (simp add: perm_fun_perm_inv_range)
  ultimately
  have "\<forall> w < n. \<pi>' w < k"
    by auto
  moreover
  have "\<forall> c < k. \<exists> w < n. \<pi>' w = c"
  proof safe
    fix c
    assume "c < k"
    then obtain w where "w < n" "\<pi> w = c"
      using k
      by (metis (mono_tags, opaque_lifting) atLeastLessThan_iff image_iff le0) 
    then have "\<pi>' (perm_fun p w) = c"
      using assms(3) by blast
    then show "\<exists>w<n. \<pi>' w = c"
      using `w < n` assms(1)
      by (metis perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_inv)
  qed
  ultimately have *: "\<pi>' ` {0..<n} = {0..<k}"
    by auto
  then have *: "\<exists> k. \<pi>' ` {0..<n} = {0..<k}"
    by auto

  show "length ?lhs = length ?rhs"
    using assms *
    by auto

  show "\<forall> v < length ?lhs. color_fun ?lhs v = color_fun ?rhs v"
    using assms * \<open>\<forall>w<n. \<pi>' w = \<pi> (perm_fun (perm_inv p) w)\<close> 
    by (simp add: color_fun_perm_coloring_app perm_fun_perm_inv_range)
qed

lemma tabulate_eq:
  assumes "(x1, y) \<in> f1" "(x2, y) \<in> f2" "\<exists>! y. (x1, y) \<in> f1" "\<exists>! y. (x2, y) \<in> f2"
  shows "tabulate f1 x1 = tabulate f2 x2"
  using assms
  by (metis tabulate_value) 

lemma cells_to_color_fun_perm_perm [simp]:
  assumes "cells_ok n cs" "perm_dom p = n" "w < n"
  shows "cells_to_color_fun (map (perm_fun_set p) cs) (perm_fun p w) = cells_to_color_fun cs w"
  unfolding cells_to_color_fun_def
proof (rule tabulate_eq)
  let ?c = "THE c. (w, c) \<in> cells_to_color_fun_pairs cs"
  show "(w, ?c) \<in> cells_to_color_fun_pairs cs"
    using ex1_cells_to_color_fun_pairs[OF assms(1)] assms(3)
    by (smt (verit, ccfv_threshold) the_equality)
  show "\<exists>!y. (w, y) \<in> cells_to_color_fun_pairs cs"
    using ex1_cells_to_color_fun_pairs[OF assms(1)] assms(3)
    by simp

  have "cells_ok n (map (perm_fun_set p) cs)" (is "cells_ok n ?cs")
    unfolding cells_ok_def
  proof safe
    fix c
    assume "{} \<in> set ?cs"
    then show False
      using assms
      by (metis cells_cells_to_coloring cells_non_empty cells_perm_coloring length_cells_to_coloring)
  next
    fix v C
    assume "v \<in> C" "C \<in> set ?cs"
    then obtain C' where "v \<in> perm_fun_set p C'" "C' \<in> set cs"
      by auto
    then obtain v' where "v = perm_fun p v'" "v' \<in> \<Union> (set cs)"
      by (auto simp add: perm_fun_set_def)
    then show "v \<in> {0..<n}"
      using assms
      unfolding cells_ok_def
      by (metis atLeastLessThan_iff in_set_conv_nth perm_dom.rep_eq perm_list_nth perm_list_set) 
  next
    fix v
    assume "v \<in> {0..<n}"
    then have "perm_fun (perm_inv p) v \<in> {0..<n}"
      using assms(2)
      by (simp add: atLeast0LessThan perm_fun_perm_inv_range)
    then obtain i where "i < List.length cs" "perm_fun (perm_inv p) v \<in> cs ! i"
      using `cells_ok n cs`
      unfolding cells_ok_def
      by (metis Union_iff index_of_in_set) 
    then show "v \<in> \<Union> (set ?cs)"
      using assms(2)
      by (smt (verit, ccfv_SIG) UnionI \<open>v \<in> {0..<n}\<close> image_eqI in_set_conv_nth length_map nth_map nth_mem perm_comp_perm_inv2 perm_dom.rep_eq perm_dom_perm_inv perm_fun_perm_inv1 perm_fun_set_def perm_inv_solve perm_list_nth perm_list_set) 
  next
    fix i j x
    assume *: "i < List.length ?cs" "j < List.length ?cs" "i \<noteq> j"
              "x \<in> map (perm_fun_set p) cs ! i" "x \<in> map (perm_fun_set p) cs ! j"
    then have "\<forall> x \<in> cs ! i. x < n" "\<forall> x \<in> cs ! j. x < n"
      using `cells_ok n cs`
      unfolding cells_ok_def
      by auto
    then have "perm_fun (perm_inv p) x \<in> cs ! i" "perm_fun (perm_inv p) x \<in> cs ! j"
      using assms(1) perm_fun_inj[OF assms(2)] *
      unfolding perm_fun_set_def 
      by (smt (verit) assms(2) image_iff length_map nth_map perm_dom_perm_inv perm_fun_perm_inv1 perm_inv_inv)+
    then show "x \<in> {}"
      using assms *
      unfolding cells_ok_def
      by auto
  qed

  have "perm_fun p w < n"
    using assms(2) assms(3)
    by (metis perm_comp_perm_inv2 perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_solve)
  show "\<exists>!y. (perm_fun p w, y) \<in> cells_to_color_fun_pairs (map (perm_fun_set p) cs)"
    using \<open>cells_ok n (map (perm_fun_set p) cs)\<close> \<open>perm_fun p w < n\<close> ex1_cells_to_color_fun_pairs 
    by presburger 


  show "(perm_fun p w, ?c) \<in> cells_to_color_fun_pairs (map (perm_fun_set p) cs)"
  proof-
    have "?c < List.length cs"
      using `(w, ?c) \<in> cells_to_color_fun_pairs cs`
      by (auto simp add: set_zip)
    then have "w \<in> cs ! ?c"
      using assms(1) assms(3) \<open>(w, THE c. (w, c) \<in> cells_to_color_fun_pairs cs) \<in> cells_to_color_fun_pairs cs\<close> \<open>\<exists>!y. (w, y) \<in> cells_to_color_fun_pairs cs\<close> 
      by (metis cells_to_color_fun' cells_to_color_fun_def tabulate_value)
    then have "perm_fun p w \<in> (map (perm_fun_set p) cs) ! ?c"
      using `?c < List.length cs`
      unfolding perm_fun_set_def
      by simp
    then show ?thesis
      using `?c < List.length cs`
      using \<open>\<exists>!y. (perm_fun p w, y) \<in> cells_to_color_fun_pairs (map (perm_fun_set p) cs)\<close> \<open>cells_ok n (map (perm_fun_set p) cs)\<close> 
      by (metis cells_to_color_fun cells_to_color_fun_def length_map tabulate_value) 
  qed
qed

lemma cells_to_coloring_perm: 
  assumes "cells_ok n cs" "perm_dom p = n"
  shows "cells_to_coloring n (map (perm_fun_set p) cs) = 
         perm_coloring p (cells_to_coloring n cs)"
  using assms
  unfolding cells_to_coloring_def
  by (subst color_fun_to_coloring_perm') (auto simp add: cells_to_color_fun_image)

lemma finer_perm_coloring [simp]:
  assumes "\<pi> \<preceq> \<pi>'" "length \<pi> = length \<pi>'" "length \<pi> = perm_dom p"
  shows "perm_coloring p \<pi> \<preceq> perm_coloring p \<pi>'"
  using assms
  using color_fun.rep_eq color_fun_perm_coloring finer_def length.rep_eq length_perm_coloring perm_fun_perm_inv_range
  by fastforce

lemma finer_strict_perm_coloring: 
  assumes "length \<pi> = length \<pi>'" "length \<pi> = perm_dom p"
          "\<pi> \<prec> \<pi>'" 
  shows "perm_coloring p \<pi> \<prec> perm_coloring p \<pi>'"
proof-
  have "perm_coloring p \<pi> \<noteq> perm_coloring p \<pi>'"
    using assms
    by (metis finer_strict_def perm_coloring_inj)
  then show ?thesis
    using assms
    unfolding finer_strict_def
    by auto
qed

lemma finer_strict_perm_coloring': 
  assumes  "length \<pi> = length \<pi>'" "length \<pi> = perm_dom p"
           "perm_coloring p \<pi> \<prec> perm_coloring p \<pi>'"
  shows "\<pi> \<prec> \<pi>'"
  using assms finer_strict_perm_coloring[of "perm_coloring p \<pi>" "perm_coloring p \<pi>'" "perm_inv p"]
  by auto


subsection\<open>Permute coloring based on its discrete refinement\<close>
definition \<C> :: "coloring \<Rightarrow> coloring \<Rightarrow> coloring" where
  "\<C> \<pi> \<alpha> \<equiv> perm_coloring (discrete_coloring_perm \<alpha>) \<pi>" 

lemma length_\<C>:
  assumes "length \<alpha> = length \<pi>" "discrete \<alpha>"
  shows "length (\<C> \<pi> \<alpha>) = length \<pi>"
  using assms length_perm_coloring perm_dom_discrete_coloring_perm
  unfolding \<C>_def
  by force

lemma color_fun_\<C>:
  assumes "length \<alpha> = length \<pi>" "discrete \<alpha>" "v < length \<pi>"
  shows "color_fun (\<C> \<pi> \<alpha>) v = (color_fun \<pi> \<circ> inv_n (length \<alpha>) (color_fun \<alpha>)) v"
proof-
  have "color_fun (\<C> \<pi> \<alpha>) v = (color_fun \<pi> \<circ> perm_fun (perm_inv (make_perm (length \<alpha>) (color_fun \<alpha>)))) v"
    using assms
    using color_fun_perm_coloring_app[of "make_perm (length \<alpha>) (color_fun \<alpha>)" \<pi> v]
    unfolding \<C>_def discrete_coloring_perm_def
    by (metis discrete_coloring_is_permutation perm_dom_make_perm)
  then show ?thesis
    by (smt (verit, best) assms(1) assms(2) assms(3) comp_apply discrete_coloring_is_permutation finer_length inv_n_def inv_perm_fun_def inv_perm_fun_perm_fun make_perm_inv_perm_fun perm_fun_make_perm)
qed
    
lemma color_fun_\<C>':
  assumes "length \<alpha> = length \<pi>" "discrete \<alpha>" "v < length \<pi>"
  shows "color_fun (\<C> \<pi> \<alpha>) (color_fun \<alpha> v) = color_fun \<pi> v"
  using assms
  by (metis \<C>_def discrete_coloring_is_permutation discrete_coloring_perm_def perm_coloring_perm_fun perm_dom_make_perm perm_fun_discrete_coloring_perm)

lift_definition id_coloring :: "nat => coloring" is "\<lambda> n. [0..<n]"
  by auto

lemma length_id_coloring [simp]:
  shows "length (id_coloring n) = n"
  by transfer auto

lemma color_fun_id_coloring_app [simp]:
  assumes "v < n"
  shows "color_fun (id_coloring n) v = v"
  using assms
  by transfer auto

lemma \<C>_id_finer:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>"
  shows "finer (id_coloring (length \<alpha>)) (\<C> \<pi> \<alpha>)"
  unfolding finer_def
proof safe
  show "length (id_coloring (length \<alpha>)) = length (\<C> \<pi> \<alpha>)"
    by (simp add: \<C>_def assms(1) assms(2) discrete_coloring_perm_def finer_length)  
next
  fix v w
  assume lt: "v < length (\<C> \<pi> \<alpha>)" "w < length (\<C> \<pi> \<alpha>)"
  assume "color_fun (\<C> \<pi> \<alpha>) v < color_fun (\<C> \<pi> \<alpha>) w"
  then have "v < w"
    by (smt (verit, ccfv_threshold) \<C>_def assms(1) assms(2) color_fun_perm_coloring_app comp_apply discrete_coloring_is_permutation discrete_coloring_perm_def finer_def length_\<C> lt(1) lt(2) perm_dom_make_perm perm_fun_perm_inv_range perm_inv_make_perm1)
  then show "color_fun (id_coloring (length \<alpha>)) v < color_fun (id_coloring (length \<alpha>)) w"
    using assms(1) assms(2) finer_def length_\<C> lt(2) by auto
qed

lemma \<C>_mono:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>" 
  assumes "v < length \<pi>" "w < length \<pi>" "v \<le> w"
  shows "color_fun (\<C> \<pi> \<alpha>) v \<le> color_fun (\<C> \<pi> \<alpha>) w"
  using assms
  by (smt (verit, ccfv_SIG) \<C>_def color_fun_perm_coloring_app comp_apply discrete_coloring_is_permutation discrete_coloring_perm_def finer_def le_antisym linorder_cases order.order_iff_strict perm_dom_make_perm perm_fun_perm_inv_range perm_inv_make_perm1)

lemma \<C>_colors [simp]:
  assumes "length \<pi> = length \<alpha>" "discrete \<alpha>"
  shows "colors (\<C> \<pi> \<alpha>) = colors \<pi>"
  using assms
  unfolding \<C>_def
  by simp

lemma \<C>_0:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>" "length \<pi> > 0"
  shows "color_fun (\<C> \<pi> \<alpha>) 0 = 0"
  using assms
proof-
  let ?c = "color_fun (\<C> \<pi> \<alpha>)"
  have "0 \<in> set (colors \<pi>)"
    using `length \<pi> > 0`
    by (metis color_fun_in_colors colors_def empty_iff ex_color gr_zeroI list.set(1) upt_eq_Nil_conv) 
  then have "0 \<in> set (colors (\<C> \<pi> \<alpha>))"
    using assms
    by (simp add: finer_def)
  then obtain v where "v < length (\<C> \<pi> \<alpha>)" "?c v = 0"
    using ex_color_color_fun by blast 
  then show ?thesis
    using \<C>_mono[OF assms(1-2)]
    by (metis (full_types) assms(1) assms(2) finer_length leI le_zero_eq length_\<C> less_nat_zero_code)
qed

lemma \<C>_consecutive_colors:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>"
  assumes "v + 1 < length \<pi>" 
  shows "color_fun (\<C> \<pi> \<alpha>) (v + 1) = (color_fun (\<C> \<pi> \<alpha>) v) \<or> 
         color_fun (\<C> \<pi> \<alpha>) (v + 1) = (color_fun (\<C> \<pi> \<alpha>) v) + 1"
proof-
  let ?\<alpha> = "discrete_coloring_perm \<alpha>"
  let ?c = "color_fun (perm_coloring ?\<alpha> \<pi>)"
  have "?c (v + 1) \<ge> ?c v"
    using \<C>_mono[OF assms(1-2)] assms(3)
    unfolding \<C>_def
    by auto
  moreover
  have "?c (v + 1) \<le> ?c v + 1"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "?c (v + 1) > ?c v + 1"
      by simp

    have "\<exists> w. w < length \<pi> \<and> ?c w = ?c v + 1"
    proof-
      have "?c (v + 1) \<in> set (colors \<pi>)"
        using \<open>v + 1 < length \<pi>\<close>
        by (metis assms(1) assms(2) color_fun_in_colors colors_perm_coloring finer_length length_perm_coloring perm_dom_discrete_coloring_perm)
      then have "?c v + 1 \<in> set (colors \<pi>)"
        using \<open>?c v + 1 < ?c (v + 1)\<close>
        by (simp add: colors_def)
      then show ?thesis
        by (smt (verit, del_insts) assms(1) assms(2) colors_perm_coloring ex_color_color_fun finer_length length_perm_coloring perm_dom_discrete_coloring_perm)
    qed
    then obtain w where "w < length \<pi>" "?c w = ?c v + 1"
      by auto
    have "?c v < ?c w" "?c w < ?c (v + 1)"
      using \<open>?c w = ?c v + 1\<close>
      using \<open>?c v + 1 < ?c (v + 1)\<close> 
      by auto
    then have "v < w \<and> w < v + 1"
      by (metis \<C>_def \<C>_mono \<open>w < length \<pi>\<close> add.commute assms(1) assms(2) assms(3) linorder_not_less trans_le_add2)
    then show False
      by auto
  qed
  ultimately
  show ?thesis
    using \<C>_def by fastforce
qed

lemma \<C>_cell:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>"
  shows "cell (\<C> \<pi> \<alpha>) c = color_fun \<alpha> ` cell \<pi> c"
proof-
  have "is_perm_fun (length \<alpha>) (color_fun \<alpha>)"
    by (simp add: assms(2))

  let ?c = "color_fun (\<C> \<pi> \<alpha>)"
  have "cell (\<C> \<pi> \<alpha>) c = {v. v < length (\<C> \<pi> \<alpha>) \<and> ?c v = c}"
    unfolding cell_def
    by simp
  also have "... = {v. v < length \<alpha> \<and> ?c v = c}"
    using assms(1) assms(2) finer_length length_\<C> by presburger
  also have "... = {color_fun \<alpha> t | t. color_fun \<alpha> t < length \<alpha> \<and> ?c (color_fun \<alpha> t) = c}"
    using `is_perm_fun (length \<alpha>) (color_fun \<alpha>)`
    by (metis perm_inv_make_perm1)
  also have "... = {color_fun \<alpha> t | t. t < length \<alpha> \<and> ?c (color_fun \<alpha> t) = c}"
    using `is_perm_fun (length \<alpha>) (color_fun \<alpha>)`
    unfolding is_perm_fun_def bij_betw_def
    by (metis (no_types, lifting) \<open>is_perm_fun (length \<alpha>) (color_fun \<alpha>)\<close> assms(2) atLeastLessThan_iff bot_nat_0.extremum discrete_coloring_perm_def image_eqI perm_dom_discrete_coloring_perm perm_fun_perm_inv_range perm_inv_make_perm1)
  also have "... = {color_fun \<alpha> t | t. t < length \<alpha> \<and> color_fun \<pi> t = c}"
    by (metis assms(1) assms(2) color_fun_\<C>' finer_length)
  also have "... = color_fun \<alpha> ` (cell \<pi> c)"
    unfolding cell_def
    using assms(1) finer_length by auto 
  finally
  show ?thesis
    .
qed

lemma \<C>_card_cell:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>"
  shows "card (cell (\<C> \<pi> \<alpha>) c) = card (cell \<pi> c)"
proof (rule bij_betw_same_card[symmetric])
  show "bij_betw (color_fun \<alpha>) (cell \<pi> c) (cell (\<C> \<pi> \<alpha>) c)"
    by (smt (verit) \<C>_cell assms(1) assms(2) bij_betwI' cell_def discrete_coloring_is_permutation discrete_coloring_perm_def finer_length image_iff mem_Collect_eq perm_dom_discrete_coloring_perm perm_dom_perm_inv perm_fun_perm_inv1 perm_fun_perm_inv_range perm_inv_make_perm1)
qed

lemma \<C>_\<alpha>_independent':
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>" 
  assumes "finer \<beta> \<pi>" "discrete \<beta>" 
  assumes "\<forall> w \<le> v. color_fun (\<C> \<pi> \<alpha>) w = color_fun (\<C> \<pi> \<beta>) w" "v + 1 < length \<pi>"
  assumes "color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v + 1"
  shows "color_fun (\<C> \<pi> \<beta>) (v + 1) = color_fun (\<C> \<pi> \<beta>) v + 1"
proof (rule ccontr)
  let ?\<alpha> = "color_fun (\<C> \<pi> \<alpha>)"
  let ?\<beta> = "color_fun (\<C> \<pi> \<beta>)"

  assume "\<not> ?thesis"
  then have "?\<beta> (v + 1) = ?\<beta> v"
    using \<C>_consecutive_colors assms
    by blast

  let ?cell = "\<lambda> n C c. {v. v < n \<and> color_fun C v = c}"

  have "card (cell (\<C> \<pi> \<beta>) (?\<alpha> v)) > card (?cell (v + 1) (\<C> \<pi> \<beta>) (?\<alpha> v))"
  proof-
    have "?cell (v + 1) (\<C> \<pi> \<beta>) (?\<alpha> v) \<union> {v + 1} \<subseteq> cell (\<C> \<pi> \<beta>) (?\<alpha> v)"
      using \<open>?\<beta> (v + 1) = ?\<beta> v\<close>
      using assms(3-6)
      using finer_length length_\<C>
      unfolding cell_def
      by auto 
      
    moreover
    have "finite (cell (\<C> \<pi> \<beta>) (?\<alpha> v))"
      unfolding cell_def
      by auto
    ultimately
    have "card (?cell (v + 1) (\<C> \<pi> \<beta>) (?\<alpha> v) \<union> {v + 1}) \<le> card (cell (\<C> \<pi> \<beta>) (?\<alpha> v))"
      by (meson card_mono)
    thus ?thesis
      unfolding cell_def
      by auto
  qed

  moreover

  have "\<forall> y. v < y \<and> y < length \<pi> \<longrightarrow> ?\<alpha> v < ?\<alpha> y"
    using assms
    by (metis \<C>_mono discrete)

  then have "card (cell (\<C> \<pi> \<alpha>) (?\<alpha> v)) = card (?cell (v + 1) (\<C> \<pi> \<alpha>) (?\<alpha> v))"
    unfolding cell_def
    by (metis (no_types, lifting) assms(1) assms(2) assms(6) finer_length leD leI length_\<C> less_add_one less_or_eq_imp_le order_less_le_trans)

  moreover

  have "card (cell (\<C> \<pi> \<alpha>) (?\<alpha> v)) = card (cell (\<C> \<pi> \<beta>) (?\<alpha> v))"
    using assms
    by (simp add: \<C>_card_cell)

  moreover

  have "?cell (v + 1) (\<C> \<pi> \<alpha>) (?\<alpha> v) = ?cell (v + 1) (\<C> \<pi> \<beta>) (?\<alpha> v)"
    using \<open>\<forall> w \<le> v. color_fun (\<C> \<pi> \<alpha>) w = color_fun  (\<C> \<pi> \<beta>) w\<close>
    unfolding cell_def
    by auto
  then have "card (?cell (v + 1) (\<C> \<pi> \<alpha>) (?\<alpha> v)) = card (?cell (v + 1) (\<C> \<pi> \<beta>) (?\<alpha> v))"
    by simp

  ultimately

  show False
    by simp
qed

lemma \<C>_\<alpha>_independent:
  assumes "finer \<alpha> \<pi>" "discrete \<alpha>" 
  assumes "finer \<beta> \<pi>" "discrete \<beta>" 
  assumes "v < length \<pi>"
  shows "color_fun (\<C> \<pi> \<alpha>) v = color_fun (\<C> \<pi> \<beta>) v"
  using \<open>v < length \<pi>\<close>
proof (induction v rule: less_induct)
  case (less v')
  show ?case
  proof (cases "v' = 0")
    case True
    then have "Min {c. c < length \<pi>} = 0"
      by (metis \<open>v' < length \<pi>\<close> empty_Collect_eq eq_Min_iff finite_Collect_less_nat mem_Collect_eq zero_le)
    then show ?thesis
      using assms \<C>_0 True
      by simp
  next
    case False
    then obtain v where "v' = v + 1"
      by (metis add.commute add.left_neutral canonically_ordered_monoid_add_class.lessE less_one linorder_neqE_nat)
    have ih: "\<forall> w \<le> v. color_fun (\<C> \<pi> \<alpha>) w = color_fun (\<C> \<pi> \<beta>) w"
      using less.IH
      using \<open>v' = v + 1\<close> less.prems by force
    show ?thesis
    proof (cases "color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v + 1")
      case True
      then have "color_fun (\<C> \<pi> \<beta>) (v + 1) = color_fun (\<C> \<pi> \<beta>) v + 1"
        using \<C>_\<alpha>_independent'[OF assms(1-4) ih]
        using \<open>v' = v + 1\<close> less.prems by blast
      thus ?thesis
        using True \<open>v' = v + 1\<close>
        using less.IH less.prems by auto
    next
      case False
      then have "color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v"
        using \<C>_consecutive_colors \<open>v' = v + 1\<close> assms(1) assms(2) assms(3) less.prems
         by blast
      have "color_fun (\<C> \<pi> \<beta>) (v + 1) = color_fun (\<C> \<pi> \<beta>) v"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "color_fun (\<C> \<pi> \<beta>) (v + 1) = color_fun (\<C> \<pi> \<beta>) v + 1"
          using \<C>_consecutive_colors \<open>v' = v + 1\<close> assms(1) assms(3) assms(4) less.prems
           by blast
        then have "color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v + 1"
          using \<C>_\<alpha>_independent'[OF assms(3-4) assms(1-2)] ih
          using \<open>v' = v + 1\<close> less.prems 
          by presburger
        then show False
          using `color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v`
          by auto
      qed
      then show ?thesis
        using \<open>color_fun (\<C> \<pi> \<alpha>) (v + 1) = color_fun (\<C> \<pi> \<alpha>) v\<close> \<open>v' = v + 1\<close> ih
         by auto
    qed
  qed
qed


subsection \<open> Individualize \<close>

definition individualize_fun :: "nat \<Rightarrow> (nat \<Rightarrow> color) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> color)" where 
  "individualize_fun n \<pi> v = 
    (if (\<forall> w < n. w \<noteq> v \<longrightarrow> \<pi> w \<noteq> \<pi> v) 
     then \<pi> 
     else (\<lambda> w. (if \<pi> w < \<pi> v \<or> w = v then \<pi> w else \<pi> w + 1)))"

definition individualize :: "coloring \<Rightarrow> nat \<Rightarrow> coloring" where 
  "individualize \<pi> v = color_fun_to_coloring (length \<pi>) (individualize_fun (length \<pi>) (color_fun \<pi>) v)"

lemma individualize_fun_all_colors [simp]:
  assumes "\<exists> k. \<pi> ` {0..<n} = {0..<k}" "v < n"
  shows "\<exists> k. individualize_fun n \<pi> v ` {0..<n} = {0..<k}"
  using assms
proof-
  obtain k where k: "\<pi> ` {0..<n} = {0..<k}"
    using assms
    by auto
  show ?thesis
  proof (cases "\<forall> w < n. w \<noteq> v \<longrightarrow> \<pi> w \<noteq> \<pi> v")
    case True
    then show ?thesis
      using k
      by (rule_tac x="k" in exI) (simp add: individualize_fun_def)
  next
    case False
    show ?thesis
    proof (cases "\<forall> w < n. \<pi> w < \<pi> v \<or> w = v")
      case True
      then show ?thesis
        using k
        unfolding individualize_fun_def
        by auto
    next
      case False
      show ?thesis
      proof (rule_tac x="k+1" in exI, safe)
        fix x
        assume x: "x \<in> {0..<n}"
        show "individualize_fun n \<pi> v x \<in> {0..<k + 1}"
        proof-
          have "individualize_fun n \<pi> v x \<le> \<pi> x + 1"
            unfolding individualize_fun_def
            by auto
          moreover
          have "\<pi> x + 1 < k + 1"
            using x k
            by auto
          ultimately
          show ?thesis
            by simp
        qed
      next
        fix c
        assume "c \<in> {0..<k+1}"
        have "\<pi> v < k"
          using `v < n` k
          by auto
        show "c \<in> individualize_fun n \<pi> v ` {0..<n}"
        proof (cases "c < \<pi> v")
          case True
          then show ?thesis
            using `\<not> (\<forall>w<n. \<pi> w < \<pi> v \<or> w = v)` \<open>\<pi> v < k\<close> k
            by (auto simp add: individualize_fun_def)
        next
          case False
          show ?thesis
          proof (cases "c = \<pi> v")
            case True
            then have "individualize_fun n \<pi> v v = c"
              using `\<not> (\<forall>w<n. \<pi> w < \<pi> v \<or> w = v)`
              by (simp add: individualize_fun_def)
            then show ?thesis
               using `v < n`
               by auto
          next
            case False
            then have "c > 0" "c > \<pi> v"
              using `\<not> (c < \<pi> v)`
              by auto
            then have "c - 1 \<in> {0..<k}"
              using `c \<in> {0..<k+1}`
              by auto
            then obtain w where "w < n" "\<pi> w = c - 1" "w \<noteq> v"
              using k `\<not> (\<forall>w<n. w \<noteq> v \<longrightarrow> \<pi> w \<noteq> \<pi> v)` `c > \<pi> v` `c > 0`
              by (smt (verit) add_0 diff_zero imageE in_set_conv_nth length_upt nth_upt set_upt)
            then have "individualize_fun n \<pi> v w = c"
              using `\<not> (\<forall>w<n. w \<noteq> v \<longrightarrow> \<pi> w \<noteq> \<pi> v)` `c > 0` \<open>\<pi> v < c\<close>
               by (auto simp add: individualize_fun_def)
            then show ?thesis
              using `w < n`
              by auto
            qed
          qed
        qed
      qed
    qed
  qed

lemma individualize_fun_finer [simp]:
  assumes "v < n" "v1 < n" "v2 < n" 
          "\<pi> v1 < \<pi> v2" 
  shows   "individualize_fun n \<pi> v v1 < individualize_fun n \<pi> v v2"
  using assms
  unfolding individualize_fun_def
  by auto

lemma individualize_finer [simp]:
  assumes "v < length \<pi>"
  shows "finer (individualize \<pi> v) \<pi>"
  using assms
  unfolding finer_def individualize_def
  by auto

lemma individualize_length [simp]:
  assumes "v < length \<pi>"
  shows "length (individualize \<pi> v) = length \<pi>"
  using assms
  using finer_length individualize_finer
  by blast

lemma individualize_fun_retains_color [simp]:
  assumes "v < n" 
  shows "individualize_fun n \<pi> v v = \<pi> v"
  using assms
  by (simp add: individualize_fun_def)

lemma individualize_retains_color:
  assumes "v < length \<pi>" 
  shows "color_fun \<pi> v \<in> set (colors (individualize \<pi> v))"
  using assms
  unfolding individualize_def all_colors
  by force

lemma individualize_fun_cell_v [simp]:
  assumes "v < n"
  shows "{w. w < n \<and> individualize_fun n \<pi> v w = \<pi> v} = {v}"
  using assms
  by (auto simp add: individualize_fun_def)

lemma individualize_fun_cell_v':
  assumes "v < n" "w < n" "individualize_fun n \<pi> v w = \<pi> v"
  shows "w = v"
proof-
  have "w \<in> {w. w < n \<and> individualize_fun n \<pi> v w = \<pi> v}"
    using assms
    by blast
  then show ?thesis
    using `v < n`
    by simp
qed

lemma individualize_cell_v [simp]:
  assumes "v < length \<pi>"
  shows "cell (individualize \<pi> v) (color_fun \<pi> v) = {v}"
  using \<open>v < length \<pi>\<close>  
  unfolding cell_def individualize_def
  by (auto simp add: individualize_fun_cell_v')

lemma individualize_singleton:
  assumes "v < length \<pi>"
  shows "{v} \<in> set (cells (individualize \<pi> v))"
  using assms individualize_retains_color
  unfolding cells_def
  by force

lemma individualize_singleton_preserve:
  assumes "{v'} \<in> set (cells \<pi>)" "v' < length \<pi>" "v < length \<pi>"
  shows "{v'} \<in> set (cells (individualize \<pi> v))"
  using assms finer_singleton individualize_finer
  by blast

lemma individualize_fun_perm [simp]:
  assumes "perm_dom p = length \<pi>" "v < length \<pi>" "w < length \<pi>"
  shows "individualize_fun (length (perm_coloring p \<pi>)) (color_fun (perm_coloring p \<pi>)) (perm_fun p v) (perm_fun p w) =
         individualize_fun (length \<pi>) (color_fun \<pi>) v w"
  using assms
  unfolding individualize_fun_def
  by (smt (verit, ccfv_SIG) color_fun_perm_coloring_app comp_apply length_perm_coloring perm_dom_perm_inv perm_fun_perm_inv1 perm_fun_perm_inv_range) 

lemma individualize_perm [simp]:
  assumes "perm_dom p = length \<pi>" "v < length \<pi>"
  shows "individualize (perm_coloring p \<pi>) (perm_fun p v) =
         perm_coloring p (individualize \<pi> v)"
  using assms individualize_fun_perm color_fun_to_coloring_perm' color_fun_all_colors individualize_fun_all_colors
  unfolding individualize_def
  by auto

end