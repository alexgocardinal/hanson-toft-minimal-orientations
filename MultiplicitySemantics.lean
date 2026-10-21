import ReachabilitySemantics

namespace HansonToft

theorem prefixPathTo_getLast {k : Nat}
    {color : Vertex k → Fin k} {rank : Nat}
    {v : Vertex k} {p : List (Vertex k)}
    (h : PrefixPathTo color rank v p) :
    p.getLast? = some v := by
  obtain ⟨front, rfl⟩ := prefixPathTo_last h
  exact List.getLast?_concat

theorem prefixPathTo_endpoint_unique {k : Nat}
    {color : Vertex k → Fin k} {rank : Nat}
    {u v : Vertex k} {p : List (Vertex k)}
    (hu : PrefixPathTo color rank u p)
    (hv : PrefixPathTo color rank v p) :
    u = v := by
  exact Option.some.inj
    ((prefixPathTo_getLast hu).symm.trans (prefixPathTo_getLast hv))

theorem prefixPathTo_successor_decompose {k : Nat}
    {color : Vertex k → Fin k} {rank : Nat}
    {v : Vertex k} {p : List (Vertex k)}
    (h : PrefixPathTo color (rank + 1) v p) :
    ∃ u front, PrefixPathTo color rank u front ∧
      Adj k u v ∧ (color v).val = rank + 1 ∧
      p = front ++ [v] := by
  cases h with
  | step previous v hEdge hColor =>
      exact ⟨_, _, previous, hEdge, hColor, rfl⟩

theorem multipleRankPaths_successor {k : Nat}
    (color : Vertex k → Fin k) (rank : Nat) (v : Vertex k) :
    MultipleRankPaths color (rank + 1) v ↔
      (color v).val = rank + 1 ∧
      ((∃ u, Adj k u v ∧ MultipleRankPaths color rank u) ∨
       (∃ u w, u ≠ w ∧ Adj k u v ∧ Adj k w v ∧
         ReachesRank color rank u ∧ ReachesRank color rank w)) := by
  constructor
  · rintro ⟨p, q, hp, hq, hDifferent⟩
    obtain ⟨u, front, hFront, hEdgeU, hColor, hpEq⟩ :=
      prefixPathTo_successor_decompose hp
    obtain ⟨w, back, hBack, hEdgeW, hColorW, hqEq⟩ :=
      prefixPathTo_successor_decompose hq
    have hFrontDifferent : front ≠ back := by
      intro heq
      apply hDifferent
      calc
        p = front ++ [v] := hpEq
        _ = back ++ [v] := congrArg (fun xs => xs ++ [v]) heq
        _ = q := hqEq.symm
    refine ⟨hColor, ?_⟩
    by_cases huw : u = w
    · subst w
      exact Or.inl
        ⟨u, hEdgeU, front, back, hFront, hBack, hFrontDifferent⟩
    · exact Or.inr
        ⟨u, w, huw, hEdgeU, hEdgeW, ⟨front, hFront⟩, ⟨back, hBack⟩⟩
  · rintro ⟨hColor, hAlternatives⟩
    rcases hAlternatives with hOne | hTwo
    · obtain ⟨u, hEdge, p, q, hp, hq, hDifferent⟩ := hOne
      refine ⟨p ++ [v], q ++ [v],
        PrefixPathTo.step hp v hEdge hColor,
        PrefixPathTo.step hq v hEdge hColor, ?_⟩
      intro heq
      exact hDifferent (List.append_inj_left' heq rfl)
    · obtain ⟨u, w, hDifferent, hEdgeU, hEdgeW, hReachU, hReachW⟩ := hTwo
      obtain ⟨p, hp⟩ := hReachU
      obtain ⟨q, hq⟩ := hReachW
      refine ⟨p ++ [v], q ++ [v],
        PrefixPathTo.step hp v hEdgeU hColor,
        PrefixPathTo.step hq v hEdgeW hColor, ?_⟩
      intro heq
      have hpq : p = q := List.append_inj_left' heq rfl
      subst q
      exact hDifferent (prefixPathTo_endpoint_unique hp hq)

#print axioms multipleRankPaths_successor

end HansonToft
