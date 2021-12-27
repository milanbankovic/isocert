theory Coloring
  imports Main Permutation
begin

text \<open>Graph coloring as a function\<close>
type_synonym coloring = "nat \<Rightarrow> nat"

text \<open>We assume that only relevant nodes are 0 to n-1 so this gives the coloring 
representation in a form of a list\<close>

definition color_list :: "nat \<Rightarrow> coloring \<Rightarrow> nat list" where
  "color_list n \<pi> = map \<pi> [0..<n]"

lemma color_list [simp]: 
  assumes "v < n"
  shows "color_list n \<pi> ! v = \<pi> v"
  using assms
  by (simp add: color_list_def)

lemma color_list_eq:
  assumes "\<forall> v < n. f1 v = f2 v"
  shows "color_list n f1 = color_list n f2"
  using assms
  unfolding color_list_def
  by auto

text \<open>Coloring from the color list\<close>
definition coloring :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat)" where
  "coloring n colors = (\<lambda> v. if v < n then colors ! v else undefined)"

lemma coloring [simp]:
  assumes "v < n"
  shows "coloring n colors v = colors ! v"
  using assms
  by (simp add: coloring_def)

lemma coloring_color_list [simp]:
  assumes "v < n"
  shows "coloring n (color_list n \<pi>) v = \<pi> v"
  by (simp add: assms color_list_def)

lemma color_list_coloring [simp]:
  assumes "length colors = n"
  shows "color_list n (coloring n colors) = colors"
  by (metis (mono_tags, lifting) assms color_list_def coloring lessThan_atLeast0 lessThan_iff map_eq_conv map_nth set_upt)

text \<open>All colors used in a coloring\<close>
definition all_colors :: "nat \<Rightarrow> coloring \<Rightarrow> nat list" where
  "all_colors n \<pi> = map \<pi> [0..<n]"

text \<open>Number of colors used\<close>
definition num_colors :: "nat \<Rightarrow> coloring \<Rightarrow> nat" where
  "num_colors n \<pi> = card (set (all_colors n \<pi>))"

text \<open>Cell of a coloring is the set of all vertices colored by the given color\<close>
definition cell :: "nat \<Rightarrow> coloring \<Rightarrow> nat \<Rightarrow> nat set" where
  "cell n \<pi> c = {v. v < n \<and> \<pi> v = c}"

text \<open>The list of all cells of a given coloring (some might be empty)\<close>
definition cells :: "nat \<Rightarrow> coloring \<Rightarrow> (nat set) list" where
  "cells n \<pi> = map (\<lambda> c. cell n \<pi> c) (all_colors n \<pi>)" 

lemma cells_disjunct:
  assumes "a \<in> c1" "a \<in> c2" "c1 \<in> set (cells n \<pi>)" "c2 \<in> set (cells n \<pi>)"
  shows "c1 = c2"
  using assms
  unfolding cells_def
  by (auto simp add: cell_def)

lemma cells_coloring_color_list [simp]:
  shows "cells n (coloring n (color_list n \<pi>)) = cells n \<pi>"
  by (auto simp add: cells_def all_colors_def cell_def)

text \<open>Nodes 0 to n-1 are colored using all colors from 0 to k-1 for some k\<close>
definition all_k_colors :: "nat \<Rightarrow> coloring \<Rightarrow> bool" where
  "all_k_colors n \<pi> \<longleftrightarrow> set (all_colors n \<pi>) = {0..<num_colors n \<pi>}"

lemma all_k_colors_ex_color:
  assumes "all_k_colors n \<pi>"
  shows "\<forall> c < num_colors n \<pi>. \<exists> v < n. \<pi> v = c"
  using assms
  unfolding all_k_colors_def all_colors_def
  by (metis (mono_tags, lifting) atLeast0LessThan image_iff lessThan_iff set_map set_upt)

text \<open>Check if the color \<pi>' refines the coloring \<pi> - each cells of \<pi>' is a subset of a cell of \<pi>\<close>
definition finer :: "nat \<Rightarrow> coloring \<Rightarrow> coloring \<Rightarrow> bool" where
  "finer n \<pi>' \<pi> \<longleftrightarrow> (\<forall> v1 < n. \<forall> v2 < n. \<pi> v1 < \<pi> v2 \<longrightarrow> \<pi>' v1 < \<pi>' v2)"

lemma finer_refl:
  shows "finer n \<pi> \<pi>"
  unfolding finer_def
  by auto

lemma finer_trans:
  assumes "finer n \<pi>1 \<pi>2" "finer n \<pi>2 \<pi>3"
  shows "finer n \<pi>1 \<pi>3"
  using assms
  using finer_def 
  by auto

lemma finer_same_color:
  assumes "finer n \<pi>' \<pi>" "v1 < n" "v2 < n" "\<pi>' v1 = \<pi>' v2" 
  shows "\<pi> v1 = \<pi> v2"
  using assms
  unfolding finer_def
  by (metis less_imp_not_eq less_linear)

lemma finer_cell_subset:
  assumes "n > 0" "finer n \<pi>' \<pi>" "all_k_colors n \<pi>"
  shows "\<forall> C' \<in> set (cells n \<pi>'). \<exists> C \<in> set (cells n \<pi>). C' \<subseteq> C"
proof safe
  fix C'
  assume "C' \<in> set (cells n \<pi>')"
  show "\<exists> C \<in> set (cells n \<pi>). C' \<subseteq> C"
  proof (cases "C' = {}")
    case True
    then show ?thesis
      using \<open>n > 0\<close>
      by (auto simp add: cells_def num_colors_def all_colors_def)
  next
    case False
    then obtain v where "v < n" "v \<in> C'"
      using \<open>C' \<in> set (cells n \<pi>')\<close>
      unfolding cell_def cells_def
      by auto
    let ?C = "cell n \<pi> (\<pi> v)"
    have "?C \<in> set (cells n \<pi>)"
      using \<open>v < n\<close> \<open>all_k_colors n \<pi>\<close>
      unfolding cells_def all_k_colors_def
      by (auto simp add: num_colors_def all_colors_def)
    moreover
    have "C' \<subseteq> ?C"
    proof
      fix v'
      assume "v' \<in> C'"
      then have "v' < n" "\<pi>' v' = \<pi>' v"
        using \<open>C' \<in> set (cells n \<pi>')\<close> \<open>v \<in> C'\<close>
        unfolding cells_def cell_def
        by auto
      then have "\<pi> v' = \<pi> v"
        using \<open>v < n\<close> \<open>finer n \<pi>' \<pi>\<close> finer_same_color 
        by blast
      then show "v' \<in> ?C"
        using \<open>v' < n\<close>
        unfolding cell_def
        by auto
    qed
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma finer_singleton:
  assumes "{v} \<in> set (cells n \<pi>1)" "v < n" "finer n \<pi>2 \<pi>1"
  shows "{v} \<in> set (cells n \<pi>2)"
proof-
  obtain c where c: "c \<in> set (all_colors n \<pi>1)" "\<pi>1 v = c" "cell n \<pi>1 c = {v}"
    using assms
    by (smt (z3) cell_def cells_def in_set_conv_nth length_map mem_Collect_eq nth_map singletonI)
  let ?c = "\<pi>2 v"
  have "cell n \<pi>2 ?c = {v}"
  proof-
    have "\<forall> v' < n. v' \<noteq> v \<longrightarrow> \<pi>2 v' \<noteq> ?c"
    proof safe
      fix v'
      assume "v' < n" "\<pi>2 v' = \<pi>2 v" "v' \<noteq> v"
      then have "\<pi>1 v' = \<pi>1 v"
        using assms(2-3) finer_same_color by blast
      then have "v' \<in> cell n \<pi>1 c"
        by (simp add: \<open>v' < n\<close> c(2) cell_def)
      then show False
        using assms c \<open>v' \<noteq> v\<close>
        by blast
    qed
    then show ?thesis
      using c(3) cell_def by fastforce
  qed
  then show ?thesis
    by (metis all_colors_def assms(2) cells_def image_eqI lessThan_atLeast0 lessThan_iff set_map set_upt)
qed    


text \<open>A coloring is discrete if each vertex is colored by a different color {0..<n}\<close>
definition discrete :: "nat \<Rightarrow> coloring \<Rightarrow> bool" where
  "discrete n \<pi> \<longleftrightarrow> set (all_colors n \<pi>) = {0..<n}"

lemma discrete_coloring_is_permutation:
  assumes "discrete n \<pi>"
  shows "is_perm_fun n \<pi>"
  using assms finite_surj_inj[of "{0..<n}" \<pi>]
  unfolding discrete_def is_perm_fun_def all_colors_def
  unfolding bij_betw_def 
  by auto

text\<open>The effect of vertices perm on colors\<close>

definition perm_coloring :: "perm \<Rightarrow> coloring \<Rightarrow> coloring" where
  "perm_coloring p \<pi> = \<pi> \<circ> (perm_fun (perm_inv p))"

lemma perm_coloring_perm_fun [simp]:
  assumes "perm_dom p = n" "v < n"
  shows "perm_coloring p \<pi> (perm_fun p v) = \<pi> v"
  using assms
  unfolding perm_coloring_def
  by auto

lemma num_colors_perm_coloring [simp]:
  assumes "perm_dom p = n"
  shows "num_colors n (perm_coloring p \<pi>) = num_colors n \<pi>"
proof-
  have "perm_fun (perm_inv p) ` {0..< n} = {0..<n}"
    by (metis assms bij_betw_def is_perm_fun is_perm_fun_def perm_dom_perm_inv)
  then show ?thesis
    unfolding Coloring.num_colors_def all_colors_def perm_coloring_def is_perm_fun_def
    by (metis image_comp image_set set_upt)
qed

lemma perm_coloring_perm_id:
  assumes "v < n"
  shows "(perm_coloring (perm_id n) \<pi>) v = \<pi> v"
  using assms
  unfolding perm_coloring_def
  by auto

lemma perm_coloring_perm_comp:
  assumes "perm_dom p1 = n" "perm_dom p2 = n" "v < n" 
  shows "perm_coloring (perm_comp p1 p2) \<pi> v = 
         perm_coloring p1 (perm_coloring p2 \<pi>) v"
  using assms
  by (simp add: perm_coloring_def)

lemma color_list_perm_coloring_perm_id [simp]:
  assumes "length colors = n"
  shows "color_list n (perm_coloring (perm_id n) (coloring n colors)) = colors"
  using assms
  by (metis color_list_coloring color_list_eq perm_coloring_perm_id)


text \<open>Permute coloring based on its discrete refinement\<close>
abbreviation \<C> :: "nat \<Rightarrow> coloring \<Rightarrow> coloring \<Rightarrow> coloring" where
  "\<C> n \<pi> \<alpha> \<equiv> perm_coloring (make_perm n \<alpha>) \<pi>" 

lemma \<C>_all_k_colors:
  assumes "all_k_colors n \<pi>" "is_perm_fun n \<alpha>"
  shows "all_k_colors n (\<C> n \<pi> \<alpha>)"
proof-
  have "perm_fun (perm_inv (make_perm n \<alpha>)) ` {0..<n} = {0..<n}"
    by (metis assms(2) bij_betw_def is_perm_fun is_perm_fun_def perm_dom_make_perm perm_dom_perm_inv)
  moreover
  have "num_colors n (\<C> n \<pi> \<alpha>) = num_colors n \<pi>"
    by (simp add: assms(2))
  ultimately
  show ?thesis
    using assms(1)
    unfolding all_k_colors_def all_colors_def perm_coloring_def
    by (metis image_comp image_set set_upt)
qed

lemma \<C>_id_finer:
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>"
  shows "finer n id (\<C> n \<pi> \<alpha>)"
  unfolding finer_def
proof safe
  have "is_perm_fun n \<alpha>"
    by (simp add: assms(2) discrete_coloring_is_permutation)
  let ?\<alpha>i = "perm_fun (perm_inv (make_perm n \<alpha>))"
  fix v w
  assume lt: "v < n" "w < n"
  assume "\<C> n \<pi> \<alpha> v < \<C> n \<pi> \<alpha> w"
  then have "\<pi> (?\<alpha>i v) < \<pi> (?\<alpha>i w)"
    unfolding perm_coloring_def comp_def
    by simp
  then have "\<alpha> (?\<alpha>i v) < \<alpha> (?\<alpha>i w)"
    using `finer n \<alpha> \<pi>` lt
    unfolding finer_def
    by (metis \<open>is_perm_fun n \<alpha>\<close> perm_dom_make_perm perm_fun_perm_inv_range)
  then have "v < w"
    by (simp add: \<open>is_perm_fun n \<alpha>\<close> lt(1) lt(2))
  then show "id v < id w"
    by simp
qed

lemma \<C>_mono:
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>" 
  assumes "x < n" "y < n" "x \<le> y"
  shows "\<C> n \<pi> \<alpha> x \<le> \<C> n \<pi> \<alpha> y"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) finer_def \<C>_id_finer id_apply leD not_le_imp_less)

lemma \<C>_0:
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>"
  assumes "n > 0" "all_k_colors n \<pi>"
  shows "\<C> n \<pi> \<alpha> 0 = 0"
proof-
  let ?c = "\<C> n \<pi> \<alpha>"
  have "all_k_colors n ?c"
    by (simp add: assms(2) assms(4) \<C>_all_k_colors discrete_coloring_is_permutation)
  moreover
  have "num_colors n ?c > 0"
    by (metis all_colors_def all_k_colors_def assms(2) assms(3) assms(4) atLeastLessThan_upt discrete_coloring_is_permutation image_iff lessThan_atLeast0 lessThan_iff less_nat_zero_code neq0_conv num_colors_perm_coloring perm_dom_make_perm set_map)
  ultimately obtain x where "x < n" "?c x = 0"
    using all_k_colors_ex_color[of n ?c]
    by blast
  then show ?thesis
    using \<C>_mono assms
    by (metis leD neq0_conv zero_le)
qed

lemma \<C>_consecutive_colors:
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>"
  assumes "all_k_colors n \<pi>" "x + 1 < n" 
  shows "\<C> n \<pi> \<alpha> (x + 1) = (\<C> n \<pi> \<alpha> x) \<or> 
         \<C> n \<pi> \<alpha> (x + 1) = (\<C> n \<pi> \<alpha> x) + 1"
proof-
  have "is_perm_fun n \<alpha>"
    by (simp add: assms(2) discrete_coloring_is_permutation)

  let ?\<alpha> = "make_perm n \<alpha>"
  let ?c = "perm_coloring ?\<alpha> \<pi>"
  have "?c (x + 1) \<ge> ?c x"
    using \<C>_mono[OF assms(1-2)] assms(4)
    by auto
  moreover
  have "?c (x + 1) \<le> ?c x + 1"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "?c (x + 1) > ?c x + 1"
      by simp

    have "\<exists> y. y < n \<and> ?c y = ?c x + 1"
    proof-
      have "all_k_colors n ?c"
        by (simp add: \<C>_all_k_colors \<open>is_perm_fun n \<alpha>\<close> assms(3))
      moreover
      have "?c x + 1 < num_colors n ?c"
        using \<open>?c x + 1 < ?c (x + 1)\<close> \<open>x + 1 < n\<close>
        by (smt (z3) all_colors_def all_k_colors_def atLeastLessThan_upt calculation image_eqI image_set le_less_trans lessThan_atLeast0 lessThan_iff not_le_imp_less not_less_iff_gr_or_eq)
      ultimately show ?thesis
        using all_k_colors_ex_color
        by auto
    qed
    then obtain y where "y < n" "?c y = ?c x + 1"
      by auto
    have "?c x < ?c y" "?c y < ?c (x + 1)"
      using \<open>?c y = ?c x + 1\<close>
      using \<open>?c x + 1 < ?c (x + 1)\<close> 
      by auto
    then have "x < y \<and> y < x + 1"
      by (metis \<C>_mono \<open>y < n\<close> add_lessD1 assms(1) assms(2) assms(4) leD not_le_imp_less)
    then show False
      by auto
  qed
  ultimately
  show ?thesis
    by auto
qed

lemma \<C>_card_cell:
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>"
  shows "card (cell n (\<C> n \<pi> \<alpha>) c) = card (cell n \<pi> c)"
proof-
  have "is_perm_fun n \<alpha>"
    by (simp add: assms(2) discrete_coloring_is_permutation)

  let ?c = "\<C> n \<pi> \<alpha>"
  have "cell n ?c c = {x. x < n \<and> ?c x = c}"
    unfolding cell_def
    by simp
  also have "... = {\<alpha> t | t. t < n \<and> ?c (\<alpha> t) = c}"
    using \<open>is_perm_fun n \<alpha>\<close>
    by (smt (verit, best) Collect_cong atLeast0LessThan bij_betw_def image_iff is_perm_fun_def lessThan_iff)
  also have "... = {\<alpha> t | t. t < n \<and> \<pi> t = c}"
    unfolding perm_coloring_def comp_def
    using \<open>is_perm_fun n \<alpha>\<close> by auto
  also have "... = \<alpha> ` (cell n \<pi> c)"
    unfolding cell_def
    by auto
  finally
  have *: "cell n ?c c = \<alpha> ` cell n \<pi> c"
    .
  show ?thesis
  proof (rule bij_betw_same_card[symmetric])
    show "bij_betw \<alpha> (cell n \<pi> c) (cell n ?c c)"
      using *
      unfolding bij_betw_def
      by (smt (verit, del_insts) \<open>is_perm_fun n \<alpha>\<close> atLeast0LessThan bij_betw_def cell_def inj_onD inj_onI is_perm_fun_def lessThan_iff mem_Collect_eq)
  qed
qed

lemma \<C>_\<alpha>_independent':
  assumes "all_k_colors n \<pi>" 
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>" 
  assumes "finer n \<beta> \<pi>" "discrete n \<beta>" 
  assumes "\<forall> y \<le> x. \<C> n \<pi> \<alpha> y = \<C> n \<pi> \<beta> y" "x + 1 < n"
  assumes "\<C> n \<pi> \<alpha> (x + 1) = (\<C> n \<pi> \<alpha> x) + 1"
  shows "\<C> n \<pi> \<beta> (x + 1) = (\<C> n \<pi> \<beta> x) + 1"
proof (rule ccontr)
  let ?\<alpha> = "\<C> n \<pi> \<alpha>"
  let ?\<beta> = "\<C> n \<pi> \<beta>"

  assume "\<not> ?thesis"
  then have "?\<beta> (x + 1) = ?\<beta> x"
    using \<C>_consecutive_colors[OF assms(4-5) assms(1) assms(7)]
    by simp

  have "card (cell n ?\<beta> (?\<alpha> x)) > card (cell (x + 1) ?\<beta> (?\<alpha> x))"
  proof-
    have "cell (x + 1) ?\<beta> (?\<alpha> x) \<union> {x + 1} \<subseteq> cell n ?\<beta> (?\<alpha> x)"
      using \<open>?\<beta> (x + 1) = ?\<beta> x\<close>
      using assms(6-7)
      unfolding cell_def
      by auto
    moreover
    have "finite (cell n ?\<beta> (?\<alpha> x))"
      unfolding cell_def
      by auto
    ultimately
    have "card (cell (x + 1) ?\<beta> (?\<alpha> x) \<union> {x + 1}) \<le> card (cell n ?\<beta> (?\<alpha> x))"
      by (meson card_mono)
    thus ?thesis
      unfolding cell_def
      by auto
  qed

  moreover

  have "\<forall> y. x < y \<and> y < n \<longrightarrow> ?\<alpha> x < ?\<alpha> y"
    by (metis \<C>_mono assms(2) assms(3) assms(7) assms(8) discrete)

  then have "card (cell n ?\<alpha> (?\<alpha> x)) = card (cell (x + 1) ?\<alpha> (?\<alpha> x))"
    unfolding cell_def
    by (metis assms(7) dual_order.strict_trans less_add_one not_less_iff_gr_or_eq)

  moreover

  have "card (cell n ?\<alpha> (?\<alpha> x)) = card (cell n ?\<beta> (?\<alpha> x))"
    by (simp add: assms(2) assms(3) assms(4) assms(5) \<C>_card_cell)

  moreover

  have "cell (x + 1) ?\<alpha> (?\<alpha> x) = cell (x + 1) ?\<beta> (?\<alpha> x)"
    using \<open>\<forall> y \<le> x. \<C> n \<pi> \<alpha> y = \<C> n \<pi> \<beta> y\<close>
    unfolding cell_def
    by auto
  then have "card (cell (x + 1) ?\<alpha> (?\<alpha> x)) = card (cell (x + 1) ?\<beta> (?\<alpha> x))"
    by simp

  ultimately

  show False
    by simp
qed

lemma \<C>_\<alpha>_independent:
  assumes "all_k_colors n \<pi>" 
  assumes "finer n \<alpha> \<pi>" "discrete n \<alpha>" 
  assumes "finer n \<beta> \<pi>" "discrete n \<beta>" 
  assumes "x < n"
  shows "\<C> n \<pi> \<alpha> x = \<C> n \<pi> \<beta> x"
  using \<open>x < n\<close>
proof (induction x rule: less_induct)
  case (less x')
  show ?case
  proof (cases "x' = 0")
    case True
    then have "Min {c. c < n} = 0"
      by (metis \<open>x' < n\<close> empty_Collect_eq eq_Min_iff finite_Collect_less_nat mem_Collect_eq zero_le)
    then show ?thesis
      using assms \<C>_0 True
      by simp
  next
    case False
    then obtain x where "x' = x + 1"
      by (metis add.commute add.left_neutral canonically_ordered_monoid_add_class.lessE less_one linorder_neqE_nat)
    have ih: "\<forall> y \<le> x. \<C> n \<pi> \<alpha> y = \<C> n \<pi> \<beta> y"
      using less.IH
      using \<open>x' = x + 1\<close> less.prems by force
    show ?thesis
    proof (cases "\<C> n \<pi> \<alpha> (x + 1) = (\<C> n \<pi> \<alpha> x) + 1")
      case True
      then have "\<C> n \<pi> \<beta> (x + 1) = (\<C> n \<pi> \<beta> x) + 1"
        using \<C>_\<alpha>_independent'[OF assms(1-5) ih]
        using \<open>x' = x + 1\<close> less.prems by blast
      thus ?thesis
        using True \<open>x' = x + 1\<close>
        using less.IH less.prems by auto
    next
      case False
      then have "\<C> n \<pi> \<alpha> (x + 1) = \<C> n \<pi> \<alpha> x"
        using \<C>_consecutive_colors \<open>x' = x + 1\<close> assms(1) assms(2) assms(3) less.prems by blast
      have "\<C> n \<pi> \<beta> (x + 1) = \<C> n \<pi> \<beta> x"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have "\<C> n \<pi> \<beta> (x + 1) = \<C> n \<pi> \<beta> x + 1"
          using \<C>_consecutive_colors \<open>x' = x + 1\<close> assms(1) assms(4) assms(5) less.prems by blast
        then have "\<C> n \<pi> \<alpha> (x + 1) = \<C> n \<pi> \<alpha> x + 1"
          using \<C>_\<alpha>_independent'[OF assms(1) assms(4-5) assms(2-3), of x] ih
          using \<open>x' = x + 1\<close> less.prems 
          by presburger
        then show False
          using `\<C> n \<pi> \<alpha> (x + 1) = \<C> n \<pi> \<alpha> x`
          by auto
      qed
      then show ?thesis
        using \<open>\<C> n \<pi> \<alpha> (x + 1) = \<C> n \<pi> \<alpha> x\<close> \<open>x' = x + 1\<close> ih by auto
    qed
  qed
qed


end