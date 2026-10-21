import PrefixPathSemantics

namespace HansonToft

def ReachesRank {k : Nat} (color : Vertex k → Fin k)
    (rank : Nat) (v : Vertex k) : Prop :=
  ∃ p, PrefixPathTo color rank v p

def MultipleRankPaths {k : Nat} (color : Vertex k → Fin k)
    (rank : Nat) (v : Vertex k) : Prop :=
  ∃ p q, PrefixPathTo color rank v p ∧
    PrefixPathTo color rank v q ∧ p ≠ q

theorem reachesRank_zero {k : Nat}
    (color : Vertex k → Fin k) (v : Vertex k) :
    ReachesRank color 0 v ↔ (color v).val = 0 := by
  constructor
  · rintro ⟨p, h⟩
    cases h with
    | zero v hColor => exact hColor
  · intro hColor
    exact ⟨[v], PrefixPathTo.zero v hColor⟩

theorem reachesRank_successor {k : Nat}
    (color : Vertex k → Fin k) (rank : Nat) (v : Vertex k) :
    ReachesRank color (rank + 1) v ↔
      (color v).val = rank + 1 ∧
      ∃ u, Adj k u v ∧ ReachesRank color rank u := by
  constructor
  · rintro ⟨p, h⟩
    cases h with
    | step previous v hEdge hColor =>
        exact ⟨hColor, _, hEdge, _, previous⟩
  · rintro ⟨hColor, u, hEdge, p, hp⟩
    exact ⟨p ++ [v], PrefixPathTo.step hp v hEdge hColor⟩

theorem prefixPathTo_zero_list {k : Nat}
    {color : Vertex k → Fin k}
    {v : Vertex k} {p : List (Vertex k)}
    (h : PrefixPathTo color 0 v p) :
    p = [v] := by
  cases h
  rfl

theorem no_multiple_rank_zero {k : Nat}
    (color : Vertex k → Fin k) (v : Vertex k) :
    ¬ MultipleRankPaths color 0 v := by
  rintro ⟨p, q, hp, hq, hDifferent⟩
  apply hDifferent
  exact (prefixPathTo_zero_list hp).trans
    (prefixPathTo_zero_list hq).symm

theorem multiple_final_rank_gives_two {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (v : Vertex k)
    (h : MultipleRankPaths color (k - 1) v) :
    HasTwoFullPaths k color := by
  obtain ⟨p, q, hp, hq, hDifferent⟩ := h
  exact ⟨p, q,
    prefixPathTo_full hk color v p hp,
    prefixPathTo_full hk color v q hq,
    hDifferent⟩

theorem unique_full_path_forbids_multiplicity {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (hUnique : HasUniqueFullPath k color) (v : Vertex k) :
    ¬ MultipleRankPaths color (k - 1) v := by
  intro hMultiple
  exact two_paths_exclude_unique color
    (multiple_final_rank_gives_two hk color v hMultiple) hUnique

#print axioms reachesRank_successor
#print axioms unique_full_path_forbids_multiplicity

end HansonToft
