theory ProofFormat
  imports Main McKayPiperno
begin 

type_synonym node = "nat list"
type_synonym vertex = nat
type_synonym cell = "vertex set"
type_synonym orbit = "vertex set"


datatype fact = 
      ColoringEqual node coloring
   |  ColoringFiner node coloring
   |  IsTargetCell node cell
   |  InvariantsEqual node node
   |  Orbit node orbit
   |  Pruned node
   |  OnPath node
   |  Canonical coloring 
   |  IsNode node


datatype rule = 
     ColoringAxiom
   | Individualize node vertex coloring
   | SplitColoring node coloring
   | Equitable node coloring
   | TargetCell node coloring
   | InvariantAxiom node
   | InvariantsEqualSym node node
   | InvariantsEqualStep node vertex coloring node vertex coloring
   | OrbitsAxiom node vertex
   | MergeOrbits node orbit orbit perm vertex vertex
   | PruneInvariant node vertex coloring node vertex coloring
   | PathAxiom
   | ExtendPath node cell vertex
   | CanonicalLeaf node coloring
   | PruneParent node cell
   | PruneLeaf node coloring node coloring
   | PruneAutomorphism node node perm
   | PruneOrbits node orbit vertex vertex

record fact_database = 
  graph :: colored_graph
  facts :: "fact set"

definition add_fact :: "fact_database \<Rightarrow> fact \<Rightarrow> fact_database" where
  "add_fact db f = db \<lparr> facts := (facts db) \<union> {f}  \<rparr>"

context McKayPiperno
begin

primrec valid_fact :: "colored_graph \<Rightarrow> fact \<Rightarrow> bool" where
  "valid_fact G (ColoringEqual \<nu> \<pi>) \<longleftrightarrow> 
    \<nu> \<in> nodes (tree G) \<and> 
    \<R>' G \<nu> = \<pi>"
| "valid_fact G (ColoringFiner \<nu> \<pi>) \<longleftrightarrow>
    \<nu> \<in> nodes (tree G) \<and>
    length \<pi> = num_vertices G \<and>
    \<R>' G \<nu> = colors (\<F>' (recolor G \<pi>))"
| "valid_fact G (IsTargetCell \<nu> W) \<longleftrightarrow>
    \<nu> \<in> nodes (tree G) \<and> 
    finite W \<and> W \<noteq> {} \<and>
    fset (\<T>' G \<nu>) = W"
| "valid_fact G (InvariantsEqual \<nu>1 \<nu>2) \<longleftrightarrow> 
   \<nu>1 \<in> nodes (tree G) \<and>
   \<nu>2 \<in> nodes (tree G) \<and>
   List.length \<nu>1 = List.length \<nu>2 \<and>
   \<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2"
| "valid_fact G (Orbit \<nu> \<Omega>) \<longleftrightarrow> 
   \<nu> \<in> nodes (tree G) \<and>
   (\<forall> v \<in> \<Omega>. vertex G v) \<and> 
   is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) \<Omega>"
| "valid_fact G (Pruned \<nu>) \<longleftrightarrow>  
   \<nu> \<in> nodes (tree G) \<and>
   the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>)"
| "valid_fact G (OnPath \<nu>) \<longleftrightarrow>
   \<nu> \<in> nodes (tree G) \<and>
   the_max_leaf G (tree G) \<in> leaves G (expand_tree G \<nu>)"
| "valid_fact G (Canonical \<pi>) \<longleftrightarrow>
   discrete \<pi> \<and> length \<pi> = num_vertices G \<and> 
   canon_form G = perm_graph (discrete_coloring_perm \<pi>) G"
| "valid_fact G (IsNode \<nu>) \<longleftrightarrow>
   \<nu> \<in> nodes (tree G)"


definition valid_fact_database :: "fact_database \<Rightarrow> bool" where
  "valid_fact_database db \<longleftrightarrow> (\<forall> f \<in> facts db. valid_fact (graph db) f)"

primrec check_rule :: "rule \<Rightarrow> fact_database \<Rightarrow> fact_database option" where
  "check_rule ColoringAxiom db =
      Some (add_fact (add_fact db (IsNode [])) (ColoringFiner [] (colors (graph db))))"
| "check_rule (Individualize \<nu> v \<pi>) db = (
      if IsNode (v # \<nu>) \<in> facts db \<and>
         ColoringEqual \<nu> \<pi> \<in> facts db
      then Some (add_fact db (ColoringFiner (v # \<nu>) (individualize \<pi> v)))
      else None
  )"
| "check_rule (SplitColoring \<nu> \<pi>) db = (
      let k  = Coloring.num_colors \<pi>;
          Ws = { j \<in> {0..<k} . split (recolor (graph db) \<pi>) j \<prec> \<pi> }
       in if ColoringFiner \<nu> \<pi> \<in> facts db \<and>
             card Ws > 0
          then Some (add_fact db (ColoringFiner \<nu> (split (recolor (graph db) \<pi>) (Min Ws))))
          else None
  )"
| "check_rule (Equitable \<nu> \<pi>) db = (
      let k = Coloring.num_colors \<pi>
       in if ColoringFiner \<nu> \<pi> \<in> facts db \<and>
             (\<forall> c \<in> {0..<k}. split (recolor (graph db) \<pi>) c = \<pi>)
          then Some (add_fact db (ColoringEqual \<nu> \<pi>))
          else None
  )"
| "check_rule (TargetCell \<nu> \<pi>) db = (
      if ColoringEqual \<nu> \<pi> \<in> facts db \<and> 
         \<T>'_color \<pi> \<noteq> None 
      then let c = the (\<T>'_color \<pi>)
            in Some (fold (\<lambda>v db'. add_fact db' (IsNode (v # \<nu>))) (sorted_list_of_set (cell \<pi> c)) 
                                  (add_fact db  (IsTargetCell \<nu> (cell \<pi> c))))
      else None
  )"
| "check_rule (InvariantAxiom \<nu>) db = (
      if IsNode \<nu> \<in> facts db
      then Some (add_fact db (InvariantsEqual \<nu> \<nu>))
      else None
  )"
| "check_rule (InvariantsEqualSym \<nu>1 \<nu>2) db = (
      if InvariantsEqual \<nu>1 \<nu>2 \<in> facts db
      then Some (add_fact db (InvariantsEqual \<nu>2 \<nu>1))
      else None
  )"
| "check_rule (InvariantsEqualStep \<nu>1 v1 \<pi>1 \<nu>2 v2 \<pi>2) db = (
      if InvariantsEqual \<nu>1 \<nu>2 \<in> facts db \<and>
         ColoringEqual (v1 # \<nu>1) \<pi>1 \<in> facts db \<and>
         ColoringEqual (v2 # \<nu>2) \<pi>2 \<in> facts db \<and>
         \<f>_hash (\<f> (graph db) \<pi>1) = \<f>_hash (\<f> (graph db) \<pi>2)
      then Some (add_fact db (InvariantsEqual (v1 # \<nu>1) (v2 # \<nu>2)))
      else None
  )"
| "check_rule (OrbitsAxiom \<nu> v) db = (
      if IsNode \<nu> \<in> facts db \<and> 
         vertex (graph db) v
      then Some (add_fact db (Orbit \<nu> {v}))
      else None)"
| "check_rule (MergeOrbits \<nu> \<Omega>1 \<Omega>2 \<sigma> v1 v2) db = (
      if Orbit \<nu> \<Omega>1 \<in> facts db \<and>
         Orbit \<nu> \<Omega>2 \<in> facts db \<and>
         is_automorphism (graph db) \<sigma> \<and>
         \<nu> = perm_fun_list \<sigma> \<nu> \<and>
         v1 \<in> \<Omega>1 \<and> v2 \<in> \<Omega>2 \<and>
         v2 = perm_fun \<sigma> v1
      then Some (add_fact db (Orbit \<nu> (\<Omega>1 \<union> \<Omega>2)))
      else None
  )"
| "check_rule (PruneInvariant \<nu>1 v1 \<pi>1 \<nu>2 v2 \<pi>2) db = (
      if InvariantsEqual \<nu>1 \<nu>2 \<in> facts db \<and>
         ColoringEqual (v1 # \<nu>1) \<pi>1 \<in> facts db \<and>
         ColoringEqual (v2 # \<nu>2) \<pi>2 \<in> facts db \<and>
         \<f>_hash (\<f> (graph db) \<pi>1) > \<f>_hash (\<f> (graph db) \<pi>2)
      then Some (add_fact db (Pruned (v2 # \<nu>2)))
      else None
  )"
| "check_rule PathAxiom db = 
      Some (add_fact db (OnPath []))"
| "check_rule (ExtendPath \<nu> W v) db = (
      if OnPath \<nu> \<in> facts db \<and>
         IsTargetCell \<nu> W \<in> facts db \<and>
         (\<forall> w \<in> W - {v}. Pruned (w # \<nu>) \<in> facts db) \<and>
         v \<in> W
      then Some (add_fact db (OnPath (v # \<nu>)))
      else None
   )"
| "check_rule (CanonicalLeaf \<nu> \<pi>) db = (
      if OnPath \<nu> \<in> facts db \<and>
         ColoringEqual \<nu> \<pi> \<in> facts db \<and>
         discrete \<pi>
      then Some (add_fact db (Canonical \<pi>))
      else None
  )"
| "check_rule (PruneParent \<nu> W) db = (
      if IsTargetCell \<nu> W \<in> facts db \<and>
         (\<forall> v \<in> W. Pruned (v # \<nu>) \<in> facts db)
      then Some (add_fact db (Pruned \<nu>))
      else None
  )"
| "check_rule (PruneLeaf \<nu>1 \<pi>1 \<nu>2 \<pi>2) db = (
      if ColoringEqual \<nu>1 \<pi>1 \<in> facts db \<and>
         ColoringEqual \<nu>2 \<pi>2 \<in> facts db \<and>
         InvariantsEqual \<nu>1 \<nu>2 \<in> facts db \<and>
         discrete \<pi>2 \<and> (\<not> discrete \<pi>1 \<or> \<g> (num_vertices (graph db)) (perm_edges (discrete_coloring_perm \<pi>1) (edges (graph db))) > 
                                         \<g> (num_vertices (graph db)) (perm_edges (discrete_coloring_perm \<pi>2) (edges (graph db))))
      then Some (add_fact db (Pruned \<nu>2)) 
      else None
  )"
| "check_rule (PruneAutomorphism \<nu>1 \<nu>2 \<sigma>) db = (
      if IsNode \<nu>1 \<in> facts db \<and> IsNode \<nu>2 \<in> facts db \<and>
         rev \<nu>1 < rev \<nu>2 \<and> 
         is_automorphism (graph db) \<sigma> \<and> 
         perm_fun_list \<sigma> \<nu>1 = \<nu>2 
      then Some (add_fact db (Pruned \<nu>2))
      else None
  )"
| "check_rule (PruneOrbits \<nu> \<Omega> v1 v2) db = (
      if IsNode (v1 # \<nu>) \<in> facts db \<and> IsNode (v2 # \<nu>) \<in> facts db \<and>
         Orbit \<nu> \<Omega> \<in> facts db \<and>
         v1 \<in> \<Omega> \<and> v2 \<in> \<Omega> \<and> v1 < v2
      then Some (add_fact db (Pruned (v2 # \<nu>)))
      else None
  )"

lemma valid_coloring_equal_length:
  assumes "valid_fact G (ColoringEqual \<nu> \<pi>)"
  shows "length \<pi> = num_vertices G"
  using assms
  by auto

lemma valid_coloring_finer_length:
  assumes "valid_fact G (ColoringFiner \<nu> \<pi>)"
  shows "length \<pi> = num_vertices G"
  using assms
  by auto

lemma length_split_Min [simp]:
  assumes "length \<pi> = num_vertices G" "{j. j < Coloring.num_colors \<pi> \<and> split (recolor G \<pi>) j \<prec> \<pi>} \<noteq> {}"
  shows "length (split (recolor G \<pi>) (Min {j. j < Coloring.num_colors \<pi> \<and> split (recolor G \<pi>) j \<prec> \<pi>})) = num_vertices G"
  using assms Min_in[of "{j. j < Coloring.num_colors \<pi> \<and> split (recolor G \<pi>) j \<prec> \<pi>}"]
  by auto

lemma split_rule:
  assumes "\<R>' G \<nu> = colors (\<F>' (recolor G \<pi>))" 
          "length \<pi> = num_vertices G"
          "{j \<in> {0..<num_colors (recolor G \<pi>)}. split (recolor G \<pi>) j \<prec> ColoredGraph.colors (recolor G \<pi>)} \<noteq> {}"
  shows "\<R>' G \<nu> = colors (\<F>' (recolor G (split (recolor G \<pi>) (Min {j \<in> {0..<num_colors (recolor G \<pi>)}. split (recolor G \<pi>) j \<prec> ColoredGraph.colors (recolor G \<pi>)}))))" 
  using assms \<F>'.simps[of "recolor G \<pi>"]
  unfolding Let_def split_graph_def
  by (auto simp add: Let_def split_graph_def)

lemma equitable_rule:
  assumes "{j. j < Coloring.num_colors \<pi> \<and> split (recolor G \<pi>) j \<prec> \<pi>} = {}" 
          "length \<pi> = num_vertices G"
          "\<R>' G \<nu> = colors (\<F>' (recolor G \<pi>))"
  shows "\<R>' G \<nu> = \<pi>"
  using assms \<F>'.simps[of "recolor G \<pi>"]
  by (auto simp add: Let_def)

lemma target_cell_rule:
  assumes "\<R>' G \<nu> = \<pi>" "\<T>'_color \<pi> = Some c"
  shows "fset (\<T>' G \<nu>) = cell \<pi> c" "fset (\<T>' G \<nu>) \<noteq> {}"
  using assms cell_non_empty[of c \<pi>] \<T>'_color_in_colors[of \<pi> c] \<T>'_color_cell_gt1[of \<pi> c] \<T>'_is_cell[of G \<nu> c]
  by auto

lemma target_cell_expand_rule: 
  assumes "\<R>' G \<nu> = \<pi>" "\<T>'_color \<pi> = Some c" "\<nu> \<in> nodes (tree G)" "v \<in> cell \<pi> c"
  shows "v # \<nu> \<in> nodes (tree G)"
  by (simp add: \<T>'_is_cell assms(1) assms(2) assms(3) assms(4) nodes_extend)

lemma invariants_equal_step_rule:
  assumes "(v1 # \<nu>1) \<in> nodes (tree G)" "(v2 # \<nu>2) \<in> nodes (tree G)"
    "\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2" "\<f>h G (v1 # \<nu>1) = \<f>h G (v2 # \<nu>2)"
  shows "\<Phi>_lex' G (v1 # \<nu>1) = \<Phi>_lex' G (v2 # \<nu>2)"
  using assms
  unfolding \<Phi>_lex'_def
  by auto

lemma orbits_axiom_rule [simp]:
  assumes "vertex G v"
  shows "is_orbit_subset (automorphisms G) {v}"
  using assms id_automorphism perm_fun_perm_id 
  unfolding is_orbit_subset_def
  by blast

lemma merge_orbits_rule:
  assumes "\<nu> \<in> nodes (tree G)"
          "is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) \<Omega>1"
          "is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) \<Omega>2"
          "\<forall> v \<in> \<Omega>1. vertex G v" "\<forall> v \<in> \<Omega>2. vertex G v"
          "is_automorphism G \<sigma>" "\<nu> = perm_fun_list \<sigma> \<nu>"
          "v1 \<in> \<Omega>1" "v2 \<in> \<Omega>2" "vertex G v1" "vertex G v2" "perm_fun \<sigma> v1 = v2"
  shows "is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) (\<Omega>1 \<union> \<Omega>2)"
proof-
  have "is_vertex_list G \<nu>"
    using assms(1) nodes_is_vertex_list
    by simp

  let ?A = "automorphisms (recolor G (\<R>' G \<nu>))"
  {
    fix u1 u2 \<Omega>1 \<Omega>2 v1 v2 \<sigma>
    assume "is_orbit_subset ?A \<Omega>1"
           "is_orbit_subset ?A \<Omega>2"
           "\<forall> v \<in> \<Omega>1. vertex G v" "\<forall> v \<in> \<Omega>2. vertex G v"
           "is_automorphism G \<sigma>" "\<nu> = perm_fun_list \<sigma> \<nu>"
           "u1 \<in> \<Omega>1" "u2 \<in> \<Omega>2" "v1 \<in> \<Omega>1" "v2 \<in> \<Omega>2" "vertex G v1" "vertex G v2" "perm_fun \<sigma> v1 = v2"
    have "\<exists>p\<in>?A. perm_fun p u1 = u2"
    proof-
      obtain \<sigma>1 \<sigma>2 where "\<sigma>1 \<in> ?A" "perm_fun \<sigma>1 v1 = u1" "\<sigma>2 \<in> ?A" "perm_fun \<sigma>2 v2 = u2"
        using `u1 \<in> \<Omega>1` `v1 \<in> \<Omega>1` `is_orbit_subset ?A \<Omega>1`
        using `u2 \<in> \<Omega>2` `v2 \<in> \<Omega>2` `is_orbit_subset ?A \<Omega>2`
        unfolding is_orbit_subset_def
        by meson
      have "vertex G u1" "vertex G u2"
        using \<open>\<forall>v\<in>\<Omega>1. vertex G v\<close> \<open>u1 \<in> \<Omega>1\<close> \<open>\<forall>v\<in>\<Omega>2. vertex G v\<close> \<open>u2 \<in> \<Omega>2\<close>
        by auto
      have "\<sigma> \<in> ?A"
      proof-
        have "perm_graph \<sigma> (recolor G (\<R>' G \<nu>)) = recolor G (\<R>' G \<nu>)"
        proof-
          have "perm_coloring \<sigma> (\<R>' G \<nu>) = (\<R>' G \<nu>)"
            using \<R>_perm \<open>\<nu> = perm_fun_list \<sigma> \<nu>\<close> \<open>is_automorphism G \<sigma>\<close> `is_vertex_list G \<nu>` is_automorphism_def is_isomorphism_def
            by fastforce
          then show ?thesis
            by (smt (verit, best) \<R>_length' \<open>is_automorphism G \<sigma>\<close> `is_vertex_list G \<nu>` is_automorphism_def is_isomorphism_def recolor_perm)
        qed
        then show ?thesis
          using `is_vertex_list G \<nu>` `is_automorphism G \<sigma>`
          unfolding automorphisms_def is_automorphism_def  is_isomorphism_def
          by auto
      qed
      let ?\<sigma> = "perm_comp (perm_comp \<sigma>2 \<sigma>) (perm_inv \<sigma>1)"
      show ?thesis
      proof (rule_tac x="?\<sigma>" in bexI)
        show "perm_fun ?\<sigma> u1 = u2"
        proof-
          have "perm_dom \<sigma>1 = num_vertices G" "perm_dom \<sigma>2 = num_vertices G" "perm_dom \<sigma> = num_vertices G"
            using `\<sigma>1 \<in> ?A` `\<sigma>2 \<in> ?A` `\<sigma> \<in> ?A` `is_vertex_list G \<nu>`
            by (auto simp add: automorphisms_def is_automorphism_def is_isomorphism_def)
          then show ?thesis
            using `vertex G u1` `vertex G u2` \<open>vertex G v1\<close> `perm_fun \<sigma> v1 = v2` `perm_fun \<sigma>1 v1 = u1` `perm_fun \<sigma>2 v2 = u2`
            by fastforce 
        qed
      next
        show "?\<sigma> \<in> ?A"
          using \<open>\<sigma> \<in> ?A\<close> \<open>\<sigma>1 \<in> ?A\<close> \<open>\<sigma>2 \<in> ?A\<close> automorphisms_def 
          by auto 
      qed
    qed
  } note * = this
  show ?thesis
  unfolding is_orbit_subset_def
  proof safe
    fix u1 u2
    assume "u1 \<in> \<Omega>1" "u2 \<in> \<Omega>1"
    then show "\<exists>p\<in>automorphisms (recolor G (\<R>' G \<nu>)). perm_fun p u1 = u2"
      using assms
      by (simp add: is_orbit_subset_def)
  next    
    fix u1 u2
    assume "u1 \<in> \<Omega>2" "u2 \<in> \<Omega>2"
    then show "\<exists>p\<in>automorphisms (recolor G (\<R>' G \<nu>)). perm_fun p u1 = u2"
      using assms
      by (simp add: is_orbit_subset_def)
  next
    fix u1 u2
    assume "u1 \<in> \<Omega>1" "u2 \<in> \<Omega>2"
    then show "\<exists>p\<in>automorphisms (recolor G (\<R>' G \<nu>)). perm_fun p u1 = u2"
      using assms *
      by simp
  next
    fix u1 u2
    assume "u1 \<in> \<Omega>2" "u2 \<in> \<Omega>1"
    moreover have "is_automorphism G (perm_inv \<sigma>)" 
      using assms
      by auto
    moreover have  "\<nu> = perm_fun_list (perm_inv \<sigma>) \<nu>" 
      using `is_vertex_list G \<nu>` assms
      by (metis is_automorphism_def is_isomorphism_def is_vertex_list_def perm_fun_list_perm_inv)
    moreover have "perm_fun (perm_inv \<sigma>) v2 = v1"
      using assms
      using is_automorphism_def is_isomorphism_def perm_fun_perm_inv2
      by blast
    ultimately show "\<exists>p\<in>automorphisms (recolor G (\<R>' G \<nu>)). perm_fun p u1 = u2"
      using assms *[of \<Omega>2 \<Omega>1 "perm_inv \<sigma>" u1 u2 v2 v1]
      by simp
  qed
qed

lemma prune_invariant_rule:
  assumes  "v1 # \<nu>1 \<in> nodes (tree G)" "v2 # \<nu>2 \<in> nodes (tree G)"
          "List.length \<nu>1 = List.length \<nu>2"
          "\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2" "\<R>' G (v1 # \<nu>1) = \<pi>1" "\<R>' G (v2 # \<nu>2) = \<pi>2"
          "\<f>_hash (\<f> G \<pi>1) > \<f>_hash (\<f> G \<pi>2)"
   shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G (v2 # \<nu>2))"
proof (rule pruneA_max_leaf)
  show "pruneA G (v1 # \<nu>1) (v2 # \<nu>2)"
    unfolding pruneA_def
  proof safe
    show "List.length (v1 # \<nu>1) = List.length (v2 # \<nu>2)"
      using assms
      by simp
    show "\<Phi>' G (v2 # \<nu>2) < \<Phi>' G (v1 # \<nu>1)"
    proof-
      have *: "\<Phi>_lex' G (v1 # \<nu>1) > \<Phi>_lex' G (v2 # \<nu>2)"
        using assms using is_vertex_list_cons(1) nodes_is_vertex_list
        by (subst \<Phi>_lex'_gt) blast+
      then show ?thesis
        unfolding \<Phi>'_def
        by auto
    qed
    show "v1 # \<nu>1 \<in> nodes (tree G)" "v2 # \<nu>2 \<in> nodes (tree G)"
      by fact+
  qed
qed


lemma extend_path_rule: 
  assumes "\<nu> \<in> nodes (tree G)" "fset (\<T>' G \<nu>) \<noteq> {}" "the_max_leaf G (tree G) \<in> leaves G (expand_tree G \<nu>)"
          "\<forall> w \<in> fset (\<T>' G \<nu>) - {v}. the_max_leaf G (tree G) \<notin> leaves G (expand_tree G (w # \<nu>))"
        shows "the_max_leaf G (tree G) \<in> leaves G (expand_tree G (v # \<nu>))"
  using assms leaf_in_some_expand_tree[OF assms(1-3)]
  by auto

lemma prune_parent_rule:
  assumes "\<nu> \<in> nodes (tree G)" "\<forall> w \<in> fset (\<T>' G \<nu>). the_max_leaf G (tree G) \<notin> leaves G (expand_tree G (w # \<nu>))" "fset (\<T>' G \<nu>) \<noteq> {}"
  shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>)"
  using assms leaf_in_some_expand_tree[OF assms(1), of "the_max_leaf G (tree G)"]
  by auto

lemma canonical_leaf_rule:
  assumes "is_vertex_list G \<nu>" "the_max_leaf G (tree G) \<in> leaves G (expand_tree G \<nu>)" "\<R>' G \<nu> = \<pi>" "discrete \<pi>"
  shows "canon_form G = perm_graph (discrete_coloring_perm \<pi>) G"
proof-
  have "\<T>' G \<nu> = {||}"
    using `\<R>' G \<nu> = \<pi>` `discrete \<pi>` \<T>'_discrete[of G \<nu>]
    by (metis bot_fset_def fset_inverse)

  then have "the_max_leaf G (tree G) = \<nu>"
    using assms expand_tree.psimps[of G \<nu>] leaves.simps[of G \<nu> "{||}"] expand_tree_dom[OF assms(1)]
    by auto
  then show ?thesis
    using assms
    unfolding the_canon_form Let_def leaf_perm_def
    by auto
qed

lemma prune_leaf_rule_1:
  assumes "\<nu>1 \<in> nodes (tree G)" "\<nu>2 \<in> nodes (tree G)" "List.length \<nu>1 = List.length \<nu>2"
          "\<R>' G \<nu>1 = \<pi>1" "\<R>' G \<nu>2 = \<pi>2" "discrete \<pi>2" "\<not> discrete \<pi>1"
          "\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2" 
   shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
proof (rule ccontr)
  let ?\<nu> = "the_max_leaf G (tree G)"
  have "is_vertex_list G \<nu>1" "is_vertex_list G \<nu>2"
    using assms(1-2) nodes_is_vertex_list by blast+

  assume "\<not> ?thesis"
  then have "?\<nu> = \<nu>2"
    by (simp add: \<T>_discrete assms(2) assms(5) assms(6) expand_tree.psimps expand_tree_dom[OF `is_vertex_list G \<nu>2`])

  obtain \<nu>' where *: "\<nu>' \<in> leaves G (expand_tree G \<nu>1)" "\<nu>' \<noteq> \<nu>1"
    by (metis all_not_in_conv assms(1) assms(4) assms(7) leaves_expand_tree_iff_discrete_nodes_expand_tree leaves_expand_tree_not_empty nodes_is_vertex_list)  
    
  have "\<Phi>_lex' G ?\<nu> < \<Phi>_lex' G \<nu>'"
    using \<Phi>_lex_extend_nodes[OF assms(1) *] `?\<nu> = \<nu>2` \<open>\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2\<close> 
    by simp
  then have "\<Phi>' G ?\<nu> < \<Phi>' G \<nu>'"
    unfolding \<Phi>'_def
    by auto
  then show False
    using the_max_leaf_is_max[of \<nu>' G] "*"(1) assms(1) leaves_of_node tree_def 
    by auto
qed

lemma prune_leaf_rule_2:
  assumes "\<nu>1 \<in> nodes (tree G)" "\<nu>2 \<in> nodes (tree G)" "List.length \<nu>1 = List.length \<nu>2"
          "\<R>' G \<nu>1 = \<pi>1" "\<R>' G \<nu>2 = \<pi>2" "discrete \<pi>2" "discrete \<pi>1"
          "\<g> (num_vertices G) (perm_edges (discrete_coloring_perm \<pi>1) (edges G)) > 
           \<g> (num_vertices G) (perm_edges (discrete_coloring_perm \<pi>2) (edges G))"
          "\<Phi>_lex' G \<nu>1 = \<Phi>_lex' G \<nu>2" 
   shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
proof (rule ccontr)
  have "is_vertex_list G \<nu>1" "is_vertex_list G \<nu>2"
    using assms(1-2) nodes_is_vertex_list by blast+
  let ?\<nu> = "the_max_leaf G (tree G)"
  assume "\<not> ?thesis"
  then have "?\<nu> = \<nu>2"
    by (simp add: \<T>_discrete assms(2) assms(5) assms(6) expand_tree.psimps expand_tree_dom[OF `is_vertex_list G \<nu>2`])
  moreover
  have "\<Phi>' G \<nu>1 > \<Phi>' G \<nu>2"
    using assms
    unfolding \<Phi>'_def 
    by (auto simp add: leaf_perm_def less_option_def less_eq_option_def)
  ultimately
  show False
    using the_max_leaf_is_max[of \<nu>1 G]
    using assms(1) assms(4) assms(7) leaves_iff_discrete_nodes
    by auto
qed

lemma prune_automorphism_rule:
  assumes "\<nu>1 \<in> nodes (tree G)" "\<nu>2 \<in> nodes (tree G)" 
          "rev \<nu>1 < rev \<nu>2" "is_automorphism G \<sigma>" "perm_fun_list \<sigma> \<nu>1 = \<nu>2"
  shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G \<nu>2)"
proof (rule pruneC_max_leaf)
  show "pruneC G \<nu>1 \<nu>2"
    using assms
    unfolding automorphisms_def pruneC_def
    by auto
qed

lemma prune_orbits_rule':
  assumes "\<nu> \<in> nodes (tree G)" "is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) \<Omega>" "w1 \<in> \<Omega>" "w2 \<in> \<Omega>" "w1 < w2"
  shows "\<exists> \<sigma> \<in> automorphisms G. perm_fun_list \<sigma> (w1 # \<nu>) = (w2 # \<nu>)"
proof-
  obtain \<sigma> where "\<sigma> \<in> automorphisms (recolor G (\<R>' G \<nu>))" "perm_fun \<sigma> w1 = w2"
    using assms
    unfolding is_orbit_subset_def
    by auto
  then have "perm_coloring \<sigma> (\<R>' G \<nu>) = (\<R>' G \<nu>)"
    unfolding automorphisms_def is_automorphism_def is_isomorphism_def
    by (smt (verit, del_insts) \<R>'_length assms(1) colors_perm_graph colors_recolor mem_Collect_eq nodes_is_vertex_list)
  then have "perm_coloring \<sigma> (colors G) = colors G"
    using perm_coloring_finer
    by (metis \<R>_finer \<R>_length' \<open>\<sigma> \<in> automorphisms (recolor G (\<R>' G \<nu>))\<close> assms(1) automorphisms_def is_automorphism_def is_isomorphism_def length_colors_num_vertices mem_Collect_eq nodes_is_vertex_list num_vertices_recolor)
  then have "\<sigma> \<in> automorphisms G"
    using `\<sigma> \<in> automorphisms (recolor G (\<R>' G \<nu>))`
    by (smt (verit, ccfv_threshold) \<R>'_length assms(1) automorphisms_def is_automorphism_def is_isomorphism_def length_colors_num_vertices mem_Collect_eq nodes_is_vertex_list num_vertices_recolor recolor_id recolor_perm recolor_recolor)
  moreover have "perm_fun_list \<sigma> (w1 # \<nu>) = (w2 # \<nu>)"
  proof-
    have "\<forall> v \<in> set \<nu>. perm_fun \<sigma> v = v"
      using pointwise_stabilizer[of G \<nu> \<sigma>] `\<sigma> \<in> automorphisms (recolor G (\<R>' G \<nu>))` `\<sigma> \<in> automorphisms G` assms(1)
      by (simp add: automorphisms_def)
    then show ?thesis
      using `perm_fun \<sigma> w1 = w2`
      unfolding perm_fun_list_def
      by (simp add: list.map_ident_strong)
  qed
  ultimately show ?thesis
    by auto
qed

lemma prune_orbits_rule:
  assumes "\<nu> \<in> nodes (tree G)" "w1 # \<nu> \<in> nodes (tree G)" "w2 # \<nu> \<in> nodes (tree G)"
          "is_orbit_subset (automorphisms (recolor G (\<R>' G \<nu>))) \<Omega>"
          "w1 \<in> \<Omega>" "w2 \<in> \<Omega>" "w1 < w2"
        shows "the_max_leaf G (tree G) \<notin> leaves G (expand_tree G (w2 # \<nu>))"
proof-
  have "rev (w1 # \<nu>) < rev (w2 # \<nu>)"
    using `w1 < w2`
    by (simp add: less_list_code(2) less_list_code(3) lexordp_append_left_rightI lexordp_induct)
  then show ?thesis
    using assms(2-3)
    using prune_orbits_rule'[of \<nu> G, OF _ assms(4-7)]
    using prune_automorphism_rule[OF assms(2-3)] assms(1) 
    using automorphisms_def 
    by blast     
qed

lemma target_cell_graph [simp]:
  shows "graph (fold (\<lambda>v db'. add_fact db' (IsNode (v # \<nu>))) xs db) = graph db"
  by (induction xs rule: rev_induct) (auto simp add: add_fact_def)

lemma check_rule:
  assumes "valid_fact_database db" "check_rule rule db = Some db'"
  shows "valid_fact_database db'"
proof (cases rule)
  case ColoringAxiom
  then show ?thesis                       
    using assms
    unfolding valid_fact_database_def
    by (auto simp add: add_fact_def finer_refl)
next
  case (Individualize \<nu> v \<pi>)
  with assms have "(v # \<nu>) \<in> nodes (tree (graph db)) \<and> vertex (graph db) v" "\<R>' (graph db) \<nu> = \<pi>" "length \<pi> = num_vertices (graph db)" 
    using nodes_extend[of \<nu> "graph db" v]
    using is_vertex_list_cons(3)[of "graph db" v \<nu>] nodes_is_vertex_list 
    unfolding valid_fact_database_def
    by (force split: if_split_asm)+
  then show ?thesis
    using assms Individualize
    unfolding valid_fact_database_def
    by (auto simp add: add_fact_def split: if_split_asm)
next
  case (SplitColoring \<nu> \<pi>)
  then show ?thesis
    using assms
    using split_rule[of "graph db" \<nu> \<pi>]
    unfolding valid_fact_database_def
    apply (auto simp add: Let_def add_fact_def split: if_split_asm)
    apply force
    apply (metis (mono_tags) card.empty length_split_Min neq0_conv valid_coloring_finer_length)
    apply (metis (mono_tags, lifting) Min_in card_0_eq card_ge_0_finite mem_Collect_eq neq0_conv valid_fact.simps(2))
    done
next
  case (Equitable \<nu> \<pi>)
  then show ?thesis
    using assms equitable_rule[of \<pi> "graph db" \<nu>]
    unfolding valid_fact_database_def
    by (force split: if_split_asm simp add: add_fact_def finer_strict_def)
next
  case (TargetCell \<nu> \<pi>)
  show ?thesis
    unfolding valid_fact_database_def
  proof safe
    fix x
    assume "x \<in> facts db'"

    { fix db xs
      assume "x \<in> facts (fold (\<lambda>v db'. add_fact db' (IsNode (v # \<nu>))) xs db)"
      then have "x \<in> facts db \<or> (\<exists> v \<in> set xs. x = IsNode (v # \<nu>))"
        by (induction xs rule: rev_induct) (auto simp add: add_fact_def)
    }
    note * = this

    let ?c = "the (\<T>'_color \<pi>)"

    have "ColoringEqual \<nu> \<pi> \<in> facts db" "\<T>'_color \<pi> = Some ?c"
         "x \<in> facts db \<or> x = IsTargetCell \<nu> (cell \<pi> ?c) \<or> (\<exists> v \<in> cell \<pi> ?c. x = IsNode (v # \<nu>))"
         "graph db' = graph db"
      using assms(2) `x \<in> facts db'` TargetCell 
      using *[of "sorted_list_of_set (cell \<pi> ?c)"
                 "add_fact db (IsTargetCell \<nu> (cell \<pi> ?c))"] target_cell_graph
      by (auto split: if_split_asm simp add: add_fact_def)
    then show "valid_fact (graph db') x"
      using assms(1) target_cell_rule[of "graph db" \<nu> \<pi> ?c] target_cell_expand_rule
      unfolding valid_fact_database_def
      by auto
  qed
next
  case (InvariantAxiom \<nu>)
  then show ?thesis
    using assms
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (InvariantsEqualSym \<nu>1 \<nu>2)
  then show ?thesis
    using assms
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (InvariantsEqualStep \<nu>1 v1 \<pi>1 \<nu>2 v2 \<pi>2)
  then have "\<Phi>_lex' (graph db) (v1 # \<nu>1) = \<Phi>_lex' (graph db) (v2 # \<nu>2)"
    using assms invariants_equal_step_rule[of v1 \<nu>1 "graph db" v2 \<nu>2] 
    unfolding valid_fact_database_def
    by (smt (verit) check_rule.simps(8) option.simps(3) valid_fact.simps(1) valid_fact.simps(4))
  then show ?thesis
    using assms InvariantsEqualStep
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (OrbitsAxiom \<nu> v)
  then show ?thesis
    using assms
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (MergeOrbits \<nu> \<Omega>1 \<Omega>2 \<sigma> v1 v2)
  then have "is_orbit_subset (automorphisms (recolor (graph db) (\<R>' (graph db) \<nu>))) (\<Omega>1 \<union> \<Omega>2)"
    using assms
    unfolding valid_fact_database_def
    by (subst merge_orbits_rule) (auto split: if_split_asm)
  then show ?thesis
    using MergeOrbits assms 
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PruneInvariant \<nu>1 v1 \<pi>1 \<nu>2 v2 \<pi>2)
  then show ?thesis
    using assms prune_invariant_rule[of v1 \<nu>1 "graph db" v2 \<nu>2 \<pi>1 \<pi>2]
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PathAxiom)
  then show ?thesis
    using assms the_max_leaf_is_leaf
    unfolding valid_fact_database_def
    by (auto simp add: add_fact_def tree_def split: if_split_asm)
next
  case (ExtendPath \<nu> W v)
  then have "v # \<nu> \<in> nodes (tree (graph db))"
    using assms nodes_extend
    unfolding valid_fact_database_def
    by (auto simp add: add_fact_def split: if_split_asm)
  moreover
  have "the_max_leaf (graph db) (tree (graph db)) \<in> leaves (graph db) (expand_tree (graph db) (v # \<nu>))"
    using assms ExtendPath extend_path_rule
    unfolding valid_fact_database_def
    by (smt (verit) check_rule.simps(13) option.simps(3) valid_fact.simps(3) valid_fact.simps(6) valid_fact.simps(7))
  ultimately show ?thesis
    using assms ExtendPath 
    unfolding valid_fact_database_def
    by (auto simp add: add_fact_def split: if_split_asm)
next
  case (CanonicalLeaf \<nu> \<pi>)
  then show ?thesis
    using assms
    using canonical_leaf_rule[of "graph db" \<nu> \<pi>]
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PruneParent \<nu> W)
  then have "the_max_leaf (graph db) (tree (graph db)) \<notin> leaves (graph db) (expand_tree (graph db) \<nu>)"
    using assms
    using prune_parent_rule[of \<nu> "graph db"]
    unfolding valid_fact_database_def
    by (metis (no_types, lifting) check_rule.simps(15) option.simps(3) valid_fact.simps(3) valid_fact.simps(6))
  then show ?thesis
    using assms PruneParent
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PruneLeaf \<nu>1 \<pi>1 \<nu>2 \<pi>2)
  then show ?thesis
    using assms
    unfolding valid_fact_database_def
    using prune_leaf_rule_1[of \<nu>1 "graph db" \<nu>2 \<pi>1 \<pi>2]
    using prune_leaf_rule_2[of \<nu>1 "graph db" \<nu>2 \<pi>1 \<pi>2]    
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PruneAutomorphism \<nu>1 \<nu>2 \<sigma>)
  then show ?thesis
    using assms
    using prune_automorphism_rule[of \<nu>1 "graph db" \<nu>2 \<sigma>]
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
next
  case (PruneOrbits \<nu> \<Omega> v1 v2)
  then show ?thesis
    using assms
    using prune_orbits_rule[of \<nu> "graph db" v1 v2 \<Omega>]
    unfolding valid_fact_database_def
    by (force simp add: add_fact_def split: if_split_asm)
qed

fun check_rule_option :: "rule \<Rightarrow> fact_database option \<Rightarrow> fact_database option" where 
  "check_rule_option r None = None"
| "check_rule_option r (Some db) = check_rule r db"

lemma check_rule_option:
  assumes "valid_fact_database db" "check_rule_option rule (Some db) = Some db'"
  shows "valid_fact_database db'"
  using assms check_rule
  by auto

type_synonym graph_proof = "rule list"

definition check_proof :: "colored_graph \<Rightarrow> graph_proof \<Rightarrow> fact_database option" where
  "check_proof G pf = (
     let initial_db = Some \<lparr> graph = G, facts = {} \<rparr> 
      in fold check_rule_option pf initial_db)" 

lemma check_proof_step:
  assumes "valid_fact_database db" "fold check_rule_option pf (Some db) = Some db'"
  shows "valid_fact_database db'"
  using assms
proof (induction pf arbitrary: db' rule: rev_induct)
  case Nil
  then show ?case 
  by simp
next
  case (snoc r rs)
  let ?dbo'' = "fold check_rule_option rs (Some db)"
  have *: "check_rule_option r ?dbo'' = Some db'"
    using snoc
    by auto
  then obtain db'' where "?dbo'' = Some db''"
    by (cases ?dbo'', auto)
  then have "valid_fact_database db''"
    using snoc
    by auto
  then show ?case
    using * `?dbo'' = Some db''` check_rule_option
    by auto
qed

lemma check_rule_graph [simp]:
  assumes "check_rule r db = Some db'"
  shows "graph db' = graph db"
  using assms target_cell_graph
  by (cases r) (auto simp add: add_fact_def Let_def split: if_split_asm)

lemma check_rule_option_graph [simp]:
  assumes "check_rule_option r (Some db) = Some db'"
  shows "graph db' = graph db"
  using assms
  by simp

lemma check_proof_graph_step:
  assumes "fold check_rule_option pf (Some db) = Some db'"
  shows "graph db' = graph db"
  using assms
proof (induction pf arbitrary: db' rule: rev_induct)
  case Nil
  then show ?case 
  by simp
next
  case (snoc r rs)
  let ?dbo'' = "fold check_rule_option rs (Some db)"
  have *: "check_rule_option r ?dbo'' = Some db'"
    using snoc
    by auto
  then obtain db'' where "?dbo'' = Some db''"
    by (cases ?dbo'', auto)
  then show ?case
    using snoc *
    by auto
qed

lemma check_proof:
  assumes "check_proof G pf = Some db"
  shows "valid_fact_database db"
proof-
  have "valid_fact_database \<lparr> graph = G, facts = {} \<rparr>"
    by (simp add: valid_fact_database_def)
  then show ?thesis
    using assms check_proof_step
    unfolding check_proof_def
    by auto
qed

lemma check_proof_graph:
  assumes "check_proof G pf = Some db"
  shows "graph db = G"
  using assms check_proof_graph_step
  unfolding check_proof_def
  by auto
  

theorem soundness:
  assumes "check_proof G pf = Some db"
  assumes "Canonical \<pi> \<in> facts db"
  shows "discrete \<pi>" "length \<pi> = num_vertices G" 
        "canon_form G = perm_graph (discrete_coloring_perm \<pi>) G"
proof-
  have "valid_fact G (Canonical \<pi>)"
    using check_proof[OF assms(1)] assms(2) check_proof_graph[OF assms(1)]
    unfolding valid_fact_database_def
    by auto
  then show "discrete \<pi>" "length \<pi> = num_vertices G" 
            "canon_form G = perm_graph (discrete_coloring_perm \<pi>) G"
    by simp_all
qed

end
end