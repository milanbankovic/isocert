theory GraphIsomorphism
  imports Main ColoredGraph
begin

section \<open>Permutations of graphs\<close>

subsection\<open>The effect of vertices perm on edges\<close>
definition perm_edges :: "perm \<Rightarrow> (nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set" where
  "perm_edges p es = (perm_fun_pair p) ` es" 

lemma perm_edges_dom:
  assumes "\<forall> (v1, v2) \<in> E. v1 < n \<and> v2 < n" 
          "(v1, v2) \<in> perm_edges p E" "perm_dom p = n"
  shows "v1 < n \<and> v2 < n"
  using assms fst_conv snd_conv
  unfolding perm_edges_def perm_fun_pair_def
  by (metis (no_types, lifting) case_prodE imageE perm_comp_perm_inv2 perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_solve)

lemma card_perm_edges [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "card (perm_edges p (edges G)) = card (edges G)"
proof-
  have "inj_on (perm_fun_pair p) (edges G)"
    using assms
    unfolding perm_fun_pair_def
    by transfer (smt (verit, ccfv_threshold) Pair_inject distinct_perm edge_vertices(1) edge_vertices(2) edges.abs_eq eq_onp_same_args inj_on_def nth_eq_iff_index_eq num_vertices.abs_eq perm_fun'_def prod.collapse)
  then show ?thesis
    using assms
    unfolding perm_edges_def Let_def
    by (auto simp add: card_image)
qed

lemma perm_edges_perm_id' [simp]:
  assumes "\<forall> (x, y) \<in> es. x < n \<and> y < n"
  shows "perm_edges (perm_id n) es = es" 
  using assms
  unfolding perm_edges_def
  by force

lemma perm_edges_perm_id [simp]:
  shows "perm_edges (perm_id (num_vertices G)) (edges G) = edges G"
  unfolding perm_edges_def
  by force
  
lemma perm_edges_perm_comp [simp]:
  assumes "perm_dom p1 = (num_vertices G)" "perm_dom p2 = (num_vertices G)"
  shows "perm_edges (perm_comp p1 p2) (edges G) = 
         perm_edges p1 (perm_edges p2 (edges G))"
  using assms
  unfolding perm_edges_def
  by force
  
subsection \<open>The effect of vertices perm on the colored graph\<close>
definition perm_graph_Rep :: "perm \<Rightarrow> colored_graph_rec \<Rightarrow> colored_graph_rec" where
  "perm_graph_Rep p G = 
   \<lparr>
      num_vertices' = num_vertices' G,
      edges' = perm_edges p (edges' G),
      colors' = perm_coloring p (colors' G)
   \<rparr>"

definition perm_graph :: "perm => colored_graph => colored_graph" where
  "perm_graph p G = Abs_colored_graph (perm_graph_Rep p (Rep_colored_graph G))"
  

lemma n_vertex_perm_graph_Rep:
  assumes "n_vertex G" "perm_dom p = num_vertices' G"
  shows "n_vertex (perm_graph_Rep p G)"
  using assms
  unfolding n_vertex_def Let_def perm_graph_Rep_def
  by (smt (verit, ccfv_threshold) case_prodD case_prodI2 length_perm_coloring perm_edges_dom select_convs(1) select_convs(2) select_convs(3)) 

lemma perm_graph_Abs_inverse [simp]:
  assumes "perm_dom p = num_vertices' G" "n_vertex G"
  shows "Rep_colored_graph (Abs_colored_graph (perm_graph_Rep p G)) = perm_graph_Rep p G"
  using assms
  by (subst Abs_colored_graph_inverse) (simp_all add: n_vertex_perm_graph_Rep) 

lemma num_vertices_perm_graph [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "num_vertices (perm_graph p G) = num_vertices G"
  using assms
  using Rep_colored_graph num_vertices.rep_eq perm_graph_Abs_inverse perm_graph_Rep_def perm_graph_def
  by auto 

lemma vertex_perm_graph [simp]:
  assumes "perm_dom p = num_vertices G" "vertex G v"
  shows "vertex (perm_graph p G) (perm_fun p v)"
  using assms
  by simp

lemma edges_perm_graph [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "edges (perm_graph p G) = perm_edges p (edges G)"
  using assms Rep_colored_graph edges.rep_eq num_vertices.rep_eq perm_graph_Abs_inverse perm_graph_Rep_def perm_graph_def
  by force 

lemma edges_perm_graph_perm:
  assumes "perm_dom p = num_vertices G" "vertex G v" "vertex G w"
  shows "(perm_fun p v, perm_fun p w) \<in> edges (perm_graph p G) \<longleftrightarrow> (v, w) \<in> edges G"
proof
  assume "(v, w) \<in> edges G"
  then show "(perm_fun p v, perm_fun p w) \<in> edges (perm_graph p G)"
    using assms image_iff 
    by (force simp add: perm_edges_def perm_fun_pair_def)
next
  assume "(perm_fun p v, perm_fun p w) \<in> edges (perm_graph p G)"
  then obtain v' w' where "(v', w') \<in> edges G" "perm_fun p v' = perm_fun p v" "perm_fun p w' = perm_fun p w"
    using assms
    by (force simp add: perm_edges_def perm_fun_pair_def)
  then show "(v, w) \<in> edges G"
    using perm_fun_inj[OF assms(1), of v v']
    using perm_fun_inj[OF assms(1), of w w'] assms(2-3)
    by auto
qed

lemma colors_perm_graph [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "colors (perm_graph p G) = perm_coloring p (colors G)"
  using assms
  using Rep_colored_graph colors.rep_eq num_vertices.rep_eq perm_graph_Abs_inverse perm_graph_Rep_def perm_graph_def
  by force

lemma num_colors_perm_graph [simp]:
  assumes "perm_dom p = num_vertices G"
  shows "num_colors (perm_graph p G) = num_colors G"
  using assms
  by simp

lemma recolor_perm[simp]:
  assumes "perm_dom p = num_vertices G" "length \<pi> = num_vertices G"
  shows "recolor (perm_graph p G) (perm_coloring p \<pi>) = perm_graph p (recolor G \<pi>)" (is "?lhs=?rhs")
proof (rule graph_eqI)
  show "num_vertices ?lhs = num_vertices ?rhs" "edges ?lhs = edges ?rhs"
    using assms
    by simp_all
next
  show "colors ?lhs = colors ?rhs"
    using assms
    by simp
qed
  
lemma perm_graph_coloring_perm_node [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "color_fun (perm_graph p G) (perm_fun p v) = color_fun G v"
  using assms
  by auto

lemma perm_graph_perm_id [simp]:
  shows "perm_graph (perm_id (num_vertices G)) G = G"
  unfolding perm_graph_def
  by (metis (full_types) Rep_colored_graph_inverse colors.rep_eq edges.rep_eq length_colors_num_vertices old.unit.exhaust perm_coloring_perm_id perm_edges_perm_id perm_graph_Rep_def surjective)

lemma perm_graph_perm_comp [simp]:
  assumes "perm_dom p1 = num_vertices G" "perm_dom p2 = num_vertices G"
  shows "perm_graph (perm_comp p1 p2) G = perm_graph p1 (perm_graph p2 G)"
  using assms
  using perm_graph_def Rep_colored_graph colors.rep_eq edges.rep_eq length_colors_num_vertices mem_Collect_eq num_vertices.rep_eq perm_coloring_perm_comp perm_edges_perm_comp perm_graph_Abs_inverse perm_graph_Rep_def
  by force
  
lemma perm_graph_perm_inv1 [simp]: 
  assumes "perm_dom p = num_vertices G"
  shows "perm_graph (perm_inv p) (perm_graph p G) = G"
  using assms
  by (metis perm_comp_perm_inv1 perm_dom_perm_inv perm_graph_perm_comp perm_graph_perm_id)

lemma perm_graph_perm_inv2 [simp]: 
  assumes "perm_dom p = num_vertices G"
  shows "perm_graph p (perm_graph (perm_inv p) G) = G"
  by (metis assms perm_dom_perm_inv perm_graph_perm_inv1 perm_inv_inv)

lemma cells_perm_graph:
  assumes "perm_dom p = num_vertices G"
  shows "cells (colors (perm_graph p G)) = map (perm_fun_set p) (cells (colors G))"
  using assms
  by simp

subsection \<open>Isomorphisms\<close>

definition is_isomorphism :: "perm \<Rightarrow> colored_graph \<Rightarrow> colored_graph \<Rightarrow> bool" where
  "is_isomorphism p G1 G2 \<longleftrightarrow> 
      perm_dom p = num_vertices G1 \<and> 
      perm_graph p G1 = G2"

definition isomorphic :: "colored_graph \<Rightarrow> colored_graph \<Rightarrow> bool" (infixl "\<simeq>" 100) where
  "isomorphic G1 G2 \<longleftrightarrow> (\<exists> p. is_isomorphism p G1 G2)"

lemma isomorphic_num_vertices:
  assumes "isomorphic G1 G2"
  shows "num_vertices G1 = num_vertices G2"
  using assms
  unfolding isomorphic_def is_isomorphism_def
  by auto

lemma isomorphic_num_edges:
  assumes "isomorphic G1 G2"
  shows "card (edges G1) = card (edges G2)"
  using assms
  unfolding isomorphic_def is_isomorphism_def
  by auto

subsubsection \<open>Automorphisms\<close>

definition is_automorphism :: "colored_graph \<Rightarrow> perm \<Rightarrow> bool" where
  "is_automorphism G p \<longleftrightarrow> is_isomorphism p G G"

definition automorphisms :: "colored_graph \<Rightarrow> perm set" where
  "automorphisms G = {p. is_automorphism G p}"

lemma id_automorphism [simp]:
  shows "perm_id (num_vertices G) \<in> automorphisms G"
  unfolding automorphisms_def is_automorphism_def is_isomorphism_def
  by auto

lemma perm_comp_automorphism [simp]:
  assumes "is_automorphism G p1" "is_automorphism G p2"
  shows "is_automorphism G (perm_comp p1 p2)"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by auto

lemma perm_inv_automorphism [simp]:
  assumes "is_automorphism G p"
  shows "is_automorphism G (perm_inv p)"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by (metis perm_dom_perm_inv perm_graph_perm_inv1)

lemma automorphism_retains_colors [simp]:
  assumes "is_automorphism G p" "vertex G v"
  shows "(color_fun G) (perm_fun p v) = (color_fun G) v"
  using assms
  unfolding is_automorphism_def is_isomorphism_def
  by (metis perm_graph_coloring_perm_node)

lemma is_automorphism_perm_inv:
  assumes "is_automorphism G p"
  shows "is_automorphism G (perm_inv p)"
  unfolding is_automorphism_def is_isomorphism_def
  using assms
  by (metis is_automorphism_def is_isomorphism_def perm_dom_perm_inv perm_graph_perm_inv1)

subsection \<open>Canonical forms\<close>

definition is_canon_form :: "(colored_graph \<Rightarrow> colored_graph) \<Rightarrow> bool" where
  "is_canon_form C \<longleftrightarrow> 
   (\<forall> G. G \<simeq> C G \<and> 
         (\<forall> p. perm_dom p = num_vertices G \<longrightarrow> C (perm_graph p G) = C G))"

lemma isomorphic_same_canon_form:
  assumes "is_canon_form C"
  shows "G \<simeq> G' \<longleftrightarrow> C G = C G'"
proof
  assume "G \<simeq> G'"
  then show "C G = C G'"
    using assms
    unfolding is_canon_form_def isomorphic_def
    by (metis is_isomorphism_def)
next
  assume "C G = C G'"
  show "G \<simeq> G'"
  proof-
    obtain p where "perm_dom p = num_vertices G" "perm_graph p G = C G"
      using assms
      unfolding is_canon_form_def isomorphic_def is_isomorphism_def
      by auto
    moreover
    obtain p' where "perm_dom p' = num_vertices G'" "perm_graph p' G' = C G'"
      using assms
      unfolding is_canon_form_def isomorphic_def is_isomorphism_def
      by auto
    ultimately
    have "perm_graph p G = perm_graph p' G'"
      using `C G = C G'`
      by simp
    then show ?thesis
      by (metis \<open>perm_dom p = num_vertices G\<close> \<open>perm_dom p' = num_vertices G'\<close> is_isomorphism_def isomorphic_def isomorphic_num_vertices perm_dom_perm_comp perm_dom_perm_inv perm_graph_perm_comp perm_graph_perm_inv1)
  qed
qed

definition orbits :: "colored_graph \<Rightarrow> vertex \<Rightarrow> vertex set" where 
  "orbits G v = {perm_fun p v | p. p \<in> automorphisms G}"

definition is_orbit_subset :: "perm set \<Rightarrow> vertex set \<Rightarrow> bool" where 
  "is_orbit_subset A \<Omega> \<longleftrightarrow> (\<forall> v1 \<in> \<Omega>. \<forall> v2 \<in> \<Omega>. \<exists> p \<in> A. perm_fun p v1 = v2)"

end