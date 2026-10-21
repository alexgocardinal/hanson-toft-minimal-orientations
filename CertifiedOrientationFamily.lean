import AcyclicPathRanking
import FullCriticality
import Init.Data.List.FinRange

namespace HansonToft

def orientationVertexList (k : Nat) : List (Vertex k) :=
  (List.finRange 7).map Vertex.cycle ++
    (List.finRange 7).flatMap
      (fun i => (List.finRange (k - 3)).map (Vertex.clique i))

theorem orientationVertexList_complete
    (k : Nat) (v : Vertex k) :
    v ∈ orientationVertexList k := by
  unfold orientationVertexList
  apply List.mem_append.mpr
  cases v with
  | cycle i =>
      left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  | clique i a =>
      right
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      exact List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩

noncomputable def orientationArcList
    (k : Nat) (d : Vertex k → Vertex k → Prop) :
    List (Vertex k × Vertex k) := by
  classical
  exact
    ((orientationVertexList k).flatMap
      (fun u => (orientationVertexList k).map (fun v => (u, v)))).filter
        (fun p => decide (d p.1 p.2))

theorem orientationArcList_mem
    (k : Nat) (d : Vertex k → Vertex k → Prop)
    (u v : Vertex k) :
    (u, v) ∈ orientationArcList k d ↔ d u v := by
  classical
  unfold orientationArcList
  constructor
  · intro h
    have hFilter := List.mem_filter.mp h
    exact of_decide_eq_true hFilter.2
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using h⟩
    apply List.mem_flatMap.mpr
    refine ⟨u, orientationVertexList_complete k u, ?_⟩
    exact List.mem_map.mpr
      ⟨v, orientationVertexList_complete k v, rfl⟩

theorem exists_consecutive_coloring_of_unique_orientation {k : Nat}
    (hk : 0 < k)
    (d : Vertex k → Vertex k → Prop)
    (hOrientation : IsOrientation k d)
    (hUnique : ∃ p, FullDirectedPath k d p ∧
      ∀ q, FullDirectedPath k d q → q = p) :
    ∃ color : Vertex k → Fin k,
      Proper k k color ∧ ConsecutiveEdgesFollow d color := by
  classical
  let arcs := orientationArcList k d
  let empty : Vertex k → Vertex k → Prop := fun _ _ => False
  let e := greedyAcyclicExtension arcs empty
  have hAllowed : ∀ p ∈ arcs, d p.1 p.2 := by
    intro p hp
    obtain ⟨u, v⟩ := p
    exact (orientationArcList_mem k d u v).mp hp
  have hEmptySub : ∀ u v, empty u v → d u v := by
    intro u v h
    exact False.elim h
  have hSub : ∀ u v, e u v → d u v :=
    greedyAcyclicExtension_sound d arcs empty hEmptySub hAllowed
  have hEmptyAcyclic : ArcAcyclic empty := by
    intro u v h
    exact False.elim h
  have hAcyclic : ArcAcyclic e :=
    greedyAcyclicExtension_acyclic arcs empty hEmptyAcyclic
  have hSaturated :
      ∀ u v, d u v → e u v ∨ ArcReach e v u := by
    intro u v huv
    exact greedyAcyclicExtension_saturated arcs empty (u, v)
      ((orientationArcList_mem k d u v).mpr huv)
  have hBound : ∀ v n, ArcLengthFrom e n v → n < k := by
    intro v n hn
    exact arcLengthFrom_bound_of_unique
      hk d e hSub hAcyclic hUnique v n hn
  obtain ⟨color, hIncreasing⟩ :=
    exists_bounded_arc_ranking hk e hBound
  have hNoBoth : ∀ u v, d u v → ¬ d v u := by
    intro u v huv
    exact (hOrientation.2 u v (hOrientation.1 u v huv)).mp huv
  have hDirection :
      ∀ u v, d u v →
        (color u).val < (color v).val ∨
          (color v).val + 2 ≤ (color u).val := by
    intro u v huv
    rcases hSaturated u v huv with hSelected | hReturn
    · exact Or.inl (hIncreasing u v hSelected)
    · rcases ArcReach.rank_alternative
        (fun w => (color w).val) hIncreasing hReturn with
        hEqual | hReverse | hGap
      · apply False.elim
        apply adj_irreflexive k u
        simpa only [hEqual] using hOrientation.1 u v huv
      · exact False.elim (hNoBoth u v huv (hSub v u hReverse))
      · exact Or.inr hGap
  have hChoice :
      ∀ u v, Adj k u v → d u v ∨ d v u := by
    intro u v hAdj
    by_cases huv : d u v
    · exact Or.inl huv
    · right
      apply Classical.byContradiction
      intro hvu
      exact huv ((hOrientation.2 u v hAdj).mpr hvu)
  refine ⟨color, ?_, ?_⟩
  · intro u v hAdj hEqual
    have hValues := congrArg Fin.val hEqual
    rcases hChoice u v hAdj with huv | hvu
    · rcases hDirection u v huv with hUp | hDown <;> omega
    · rcases hDirection v u hvu with hUp | hDown <;> omega
  · intro u v hAdj hNext
    rcases hChoice u v hAdj with huv | hvu
    · exact huv
    · rcases hDirection v u hvu with hUp | hDown <;> omega

theorem certified_no_minimal_orientation {k : Nat}
    (hk : 4 ≤ k) :
    NoMinimalOrientation k := by
  intro d hOrientation hUnique
  obtain ⟨color, hProper, hFollow⟩ :=
    exists_consecutive_coloring_of_unique_orientation
      (by omega) d hOrientation hUnique
  exact consecutive_coloring_rules_out_unique_orientation
    hk d color hProper hFollow hUnique

theorem certified_complete_family_statement :
    completeFamilyStatement := by
  intro k hk
  refine ⟨?_, certified_coloring_family_statement k hk,
    certified_no_minimal_orientation hk⟩
  apply edgeCriticalStatement_proved
  omega

#print axioms exists_consecutive_coloring_of_unique_orientation
#print axioms certified_no_minimal_orientation
#print axioms certified_complete_family_statement

end HansonToft
