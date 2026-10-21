import AcyclicArcConstruction

namespace HansonToft

theorem directed_list_reaches_member {k : Nat}
    (e : Vertex k → Vertex k → Prop)
    (u : Vertex k) (rest : List (Vertex k)) :
    DirectedEdgesAlong e (u :: rest) →
    ∀ v, v ∈ u :: rest → ArcReach e u v := by
  induction rest generalizing u with
  | nil =>
      intro hEdges v hv
      have hEqual : v = u := List.mem_singleton.mp hv
      subst v
      exact ArcReach.refl u
  | cons w tail ih =>
      intro hEdges v hv
      rcases List.mem_cons.mp hv with hEqual | hMem
      · subst v
        exact ArcReach.refl u
      · exact
          (ArcReach.tail (ArcReach.refl u) hEdges.1).trans
            (ih w hEdges.2 v hMem)

theorem directed_list_nodup_of_acyclic {k : Nat}
    (e : Vertex k → Vertex k → Prop)
    (hAcyclic : ArcAcyclic e)
    (p : List (Vertex k)) :
    DirectedEdgesAlong e p → p.Nodup := by
  induction p with
  | nil =>
      intro h
      exact List.nodup_nil
  | cons u rest ih =>
      intro hEdges
      cases rest with
      | nil =>
          simp
      | cons v tail =>
          apply List.nodup_cons.mpr
          refine ⟨?_, ih hEdges.2⟩
          intro hMem
          exact hAcyclic u v hEdges.1
            (directed_list_reaches_member
              e v tail hEdges.2 u hMem)

/-- A directed walk of exactly n edges starting at v. -/
inductive ArcLengthFrom {k : Nat}
    (e : Vertex k → Vertex k → Prop) :
    Nat → Vertex k → Prop
  | zero (v : Vertex k) : ArcLengthFrom e 0 v
  | step {n : Nat} {u v : Vertex k} :
      e u v → ArcLengthFrom e n v → ArcLengthFrom e (n + 1) u

theorem arcLengthFrom_realize {k : Nat}
    (e : Vertex k → Vertex k → Prop)
    {n : Nat} {v : Vertex k}
    (h : ArcLengthFrom e n v) :
    ∃ rest : List (Vertex k),
      rest.length = n ∧ DirectedEdgesAlong e (v :: rest) := by
  induction h with
  | zero =>
      exact ⟨[], rfl, True.intro⟩
  | step hEdge hPrevious ih =>
      obtain ⟨rest, hLength, hEdges⟩ := ih
      refine ⟨_ :: rest, ?_, hEdge, hEdges⟩
      simp only [List.length_cons]
      omega

theorem arcLengthFrom_bound_of_unique {k : Nat}
    (hk : 0 < k)
    (d e : Vertex k → Vertex k → Prop)
    (hSub : ∀ u v, e u v → d u v)
    (hAcyclic : ArcAcyclic e)
    (hUnique : ∃ p, FullDirectedPath k d p ∧
      ∀ q, FullDirectedPath k d q → q = p)
    (v : Vertex k) (n : Nat)
    (hLength : ArcLengthFrom e n v) :
    n < k := by
  obtain ⟨rest, hRestLength, hEdges⟩ :=
    arcLengthFrom_realize e hLength
  have hSimple :=
    directed_list_nodup_of_acyclic e hAcyclic (v :: rest) hEdges
  have hDirected :=
    directedEdgesAlong_of_subrelation d e hSub (v :: rest) hEdges
  have hBound :=
    unique_directed_path_bounds_length hk d hUnique
      (v :: rest) hSimple hDirected
  simp only [List.length_cons] at hBound
  omega

theorem arc_bounded_nat_maximum
    (P : Nat → Prop) (hZero : P 0) :
    ∀ bound : Nat,
      ∃ n, n ≤ bound ∧ P n ∧
        ∀ m, m ≤ bound → P m → m ≤ n := by
  classical
  intro bound
  induction bound with
  | zero =>
      refine ⟨0, Nat.le_refl 0, hZero, ?_⟩
      intro m hm hPm
      exact hm
  | succ bound ih =>
      by_cases hTop : P (bound + 1)
      · refine ⟨bound + 1, Nat.le_refl _, hTop, ?_⟩
        intro m hm hPm
        exact hm
      · obtain ⟨n, hn, hPn, hMaximum⟩ := ih
        refine ⟨n, by omega, hPn, ?_⟩
        intro m hm hPm
        have hNotTop : m ≠ bound + 1 := by
          intro hEqual
          apply hTop
          simpa only [hEqual] using hPm
        exact hMaximum m (by omega) hPm

theorem exists_bounded_arc_ranking {k : Nat}
    (hk : 0 < k)
    (e : Vertex k → Vertex k → Prop)
    (hBound : ∀ v n, ArcLengthFrom e n v → n < k) :
    ∃ color : Vertex k → Fin k,
      ∀ u v, e u v → (color u).val < (color v).val := by
  classical
  have hMax : ∀ v : Vertex k,
      ∃ n, n ≤ k ∧ ArcLengthFrom e n v ∧
        ∀ m, m ≤ k → ArcLengthFrom e m v → m ≤ n := by
    intro v
    exact arc_bounded_nat_maximum
      (fun n => ArcLengthFrom e n v) (ArcLengthFrom.zero v) k
  let height : Vertex k → Nat :=
    fun v => Classical.choose (hMax v)
  have hWitness : ∀ v, ArcLengthFrom e (height v) v := by
    intro v
    exact (Classical.choose_spec (hMax v)).2.1
  have hLess : ∀ v, height v < k := by
    intro v
    exact hBound v (height v) (hWitness v)
  have hMaximum :
      ∀ v n, ArcLengthFrom e n v → n ≤ height v := by
    intro v n hn
    have hSmall := hBound v n hn
    exact (Classical.choose_spec (hMax v)).2.2 n (by omega) hn
  let color : Vertex k → Fin k :=
    fun v => ⟨k - 1 - height v, by
      have h := hLess v
      omega⟩
  refine ⟨color, ?_⟩
  intro u v hEdge
  have hLonger : ArcLengthFrom e (height v + 1) u :=
    ArcLengthFrom.step hEdge (hWitness v)
  have hStep := hMaximum u (height v + 1) hLonger
  have hu := hLess u
  have hv := hLess v
  change k - 1 - height u < k - 1 - height v
  omega

theorem ArcReach.rank_alternative {α : Type}
    {e : α → α → Prop}
    (rank : α → Nat)
    (hIncreasing : ∀ u v, e u v → rank u < rank v)
    {x y : α} (h : ArcReach e x y) :
    x = y ∨ e x y ∨ rank x + 2 ≤ rank y := by
  induction h with
  | refl =>
      exact Or.inl rfl
  | @tail middle last hPath hEdge ih =>
      rcases ih with hEqual | hArc | hLong
      · right
        left
        simpa only [hEqual] using hEdge
      · right
        right
        have hFirst := hIncreasing _ _ hArc
        have hSecond := hIncreasing _ _ hEdge
        omega
      · right
        right
        have hLast := hIncreasing _ _ hEdge
        omega

def ConsecutiveEdgesFollow {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k) : Prop :=
  ∀ u v, Adj k u v →
    (color u).val + 1 = (color v).val → d u v

theorem consecutive_ranked_edges_are_directed {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hFollow : ConsecutiveEdgesFollow d color)
    (p : List (Vertex k)) :
    ∀ s, EdgesAlong p →
      RanksFrom (fun v => (color v).val) s p →
      DirectedEdgesAlong d p := by
  induction p with
  | nil =>
      intro s hEdges hRanks
      trivial
  | cons u rest ih =>
      intro s hEdges hRanks
      cases rest with
      | nil => trivial
      | cons v tail =>
          refine ⟨hFollow u v hEdges.1 ?_,
            ih (s + 1) hEdges.2 hRanks.2⟩
          have hu : (color u).val = s := hRanks.1
          have hv : (color v).val = s + 1 := hRanks.2.1
          omega

theorem consecutive_increasing_path_is_directed {k : Nat}
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hFollow : ConsecutiveEdgesFollow d color)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    FullDirectedPath k d p := by
  have hRanks :=
    ((fullIncreasingPath_iff_ranks color p).mp hp).2.2.2
  exact ⟨hp.1, hp.2.1,
    consecutive_ranked_edges_are_directed d color hFollow p 0
      hp.2.2.1 hRanks⟩

theorem consecutive_coloring_rules_out_unique_orientation {k : Nat}
    (hk : 4 ≤ k)
    (d : Vertex k → Vertex k → Prop)
    (color : Vertex k → Fin k)
    (hProper : Proper k k color)
    (hFollow : ConsecutiveEdgesFollow d color) :
    ¬ (∃ r, FullDirectedPath k d r ∧
      ∀ q, FullDirectedPath k d q → q = r) := by
  obtain ⟨p, q, hp, hq, hDifferent⟩ :=
    certified_two_paths_family k hk color hProper
  intro ⟨r, hr, hOnly⟩
  apply hDifferent
  exact
    (hOnly p
      (consecutive_increasing_path_is_directed d color hFollow p hp)).trans
    (hOnly q
      (consecutive_increasing_path_is_directed d color hFollow q hq)).symm

#print axioms directed_list_nodup_of_acyclic
#print axioms exists_bounded_arc_ranking
#print axioms ArcReach.rank_alternative
#print axioms consecutive_coloring_rules_out_unique_orientation

end HansonToft
