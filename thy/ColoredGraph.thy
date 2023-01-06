theory ColoredGraph
imports Main Coloring Permutation
begin

section \<open>Colored graphs\<close>

type_synonym vertex = nat

record colored_graph_rec = 
   num_vertices' :: nat
   edges' :: "(vertex \<times> vertex) set"
   colors' :: coloring \<comment> \<open>map each vertex to its color\<close>

abbreviation n_vertex_edges :: "nat \<Rightarrow> (vertex \<times> vertex) set \<Rightarrow> bool" where
  "n_vertex_edges n es \<equiv> (\<forall> (v1, v2) \<in> es. v1 < n \<and> v2 < n)"

text \<open>Edges and colors are consistent with the fact that the graph has n vertices\<close>
text \<open>This is basically an invariant of the colored_graph datatype\<close>
definition n_vertex :: "colored_graph_rec \<Rightarrow> bool"  where
  "n_vertex G \<longleftrightarrow> (let n = num_vertices' G 
                    in n_vertex_edges n (edges' G) \<and>
                       length (colors' G) = n)"

lemma finite_edges':
  assumes "n_vertex G"
  shows "finite (edges' G)"
proof-
  have "edges' G \<subseteq> {0..<num_vertices' G} \<times> {0..<num_vertices' G}"
    using assms
    unfolding n_vertex_def Let_def
    by auto
  then show ?thesis
    using finite_subset
    by auto
qed
  
typedef colored_graph = "{G :: colored_graph_rec. n_vertex G}"
proof-
  have "length (coloring []) = 0"
    by (simp add: eq_onp_same_args length.abs_eq) 
  then show ?thesis
    by (rule_tac x="\<lparr>num_vertices' = 0, edges' = {}, colors' = coloring []\<rparr>" in exI, simp add: n_vertex_def)
qed

copy_bnf (no_warn_transfer) 's colored_graph_rec_ext
setup_lifting type_definition_colored_graph

lift_definition num_vertices :: "colored_graph => nat" is num_vertices'
done

lift_definition colors :: "colored_graph => coloring" is colors'
done

lift_definition edges :: "colored_graph => (vertex \<times> vertex) set" is edges'
done

lemma graph_eqI:
  assumes "num_vertices G = num_vertices G'"
          "edges G = edges G'"
          "colors G = colors G'"
  shows "G = G'"
  using assms
  by transfer simp


lemma length_colors_num_vertices [simp]:
  "length (colors G) = num_vertices G"
  by transfer (simp add: n_vertex_def Let_def)

text \<open>Check if v is a valid vertex of the graph G\<close>
abbreviation vertex :: "colored_graph \<Rightarrow> vertex \<Rightarrow> bool" where
  "vertex G v \<equiv> v < num_vertices G"

lemma edge_vertices [simp]:
  assumes "(v1, v2) \<in> edges G"
  shows "vertex G v1" "vertex G v2"
proof-
  show "vertex G v1"
    using assms
    by transfer (metis case_prodD n_vertex_def)
  show "vertex G v2"
    using assms
    by transfer (metis case_prodD n_vertex_def)
qed
  
lemma finite_edges [simp]:
  shows "finite (edges G)"
  by transfer (simp add: finite_edges')

lemma vertex_perm_fun [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "vertex G (perm_fun p v)"
  using assms
  by (metis perm_dom_perm_inv perm_fun_perm_inv_range perm_inv_inv)

lemma vertex_perm_fun_inv [simp]:
  assumes "vertex G v" "perm_dom p = num_vertices G"
  shows "vertex G (perm_fun (perm_inv p) v)"
  by (simp add: assms(1) assms(2))

text \<open>Coloring function\<close>
abbreviation color_fun :: "colored_graph \<Rightarrow> (vertex \<Rightarrow> color)" where
  "color_fun G \<equiv> Coloring.color_fun (colors G)"

abbreviation num_colors :: "colored_graph \<Rightarrow> nat" where
  "num_colors G \<equiv> Coloring.num_colors (colors G)"

 
text \<open>The number of colors is limited by number of vertices\<close>
lemma num_colors_ub:
  shows "num_colors G \<le> num_vertices G"
  by transfer (metis Coloring.colors_def all_colors card_atLeastLessThan card_length diff_zero length_map length_upt n_vertex_def set_upt)


text \<open>Recolor graph by the given coloring\<close>

definition recolor :: "colored_graph \<Rightarrow> coloring \<Rightarrow> colored_graph" where
  "recolor G \<pi> = Abs_colored_graph ((Rep_colored_graph G) \<lparr> colors' := \<pi> \<rparr>)"

lemma recolor_Abs_inverse [simp]:
  assumes "length \<pi> = num_vertices' G" "n_vertex G"
  shows "Rep_colored_graph (Abs_colored_graph (G\<lparr>colors' := \<pi>\<rparr>)) = G\<lparr>colors' := \<pi>\<rparr>"
proof-
  have "n_vertex (G\<lparr>colors' := \<pi>\<rparr>)"
    using assms
    unfolding n_vertex_def Let_def
    by auto
  then show ?thesis
    by (subst Abs_colored_graph_inverse, auto)
qed  
  
lemma num_vertices_recolor [simp]:
  assumes "length \<pi> = num_vertices G"
  shows "num_vertices (recolor G \<pi>) = num_vertices G"
  using assms
  unfolding recolor_def
  by transfer (simp add: num_vertices.rep_eq)

lemma vertex_recolor [simp]:
  assumes "length \<pi> = num_vertices G" "vertex G v"
  shows "vertex (recolor G \<pi>) v"
  using assms
  by simp

lemma edges_recolor [simp]:
  assumes "length \<pi> = num_vertices G"
  shows "edges (recolor G \<pi>) = edges G"
  using assms
  unfolding recolor_def
  by transfer (simp add: edges.rep_eq)

lemma colors_recolor [simp]:
  assumes "length \<pi> = num_vertices G"
  shows "colors (recolor G \<pi>) = \<pi>"
  using assms
  unfolding recolor_def
  by transfer (simp add: colors.rep_eq)
  
lemma color_fun_recolor [simp]:
  assumes "length \<pi> = num_vertices G"
  shows "color_fun (recolor G \<pi>) = Coloring.color_fun \<pi>"
  using assms
  by auto

lemma cells_recolor [simp]:
  assumes "length \<pi> = num_vertices G"
  shows "cells (colors (recolor G \<pi>)) = cells \<pi>"
  using assms
  by simp

lemma num_colors_recolor:
  assumes "length \<pi> = num_vertices G"
  shows "num_colors (recolor G \<pi>) = Coloring.num_colors \<pi>"
  using assms
  by simp

lemma recolor_id [simp]:
  shows "recolor G (colors G) = G"
  by (simp add: Rep_colored_graph_inverse colors.rep_eq recolor_def)


lemma recolor_recolor[simp]:
  assumes "length \<pi> = num_vertices G" "length \<pi>' = num_vertices G"
  shows "recolor (recolor G \<pi>) \<pi>' = recolor G \<pi>'"
  using assms
  by (simp add: graph_eqI)



end