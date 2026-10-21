import ColorVariableSemantics

namespace HansonToft

theorem ranksFrom_nodup {α : Type}
    (color : α → Nat) (p : List α) :
    ∀ s, RanksFrom color s p → p.Nodup := by
  induction p with
  | nil =>
      intro s h
      simp
  | cons a rest ih =>
      intro s h
      refine List.nodup_cons.mpr ⟨?_, ih (s + 1) h.2⟩
      intro hMem
      obtain ⟨j, hj⟩ := color_member_has_index a rest hMem
      have hRank := ranksFrom_lookup color rest (s + 1)
        h.2 j.val a hj
      have hHead := h.1
      omega

theorem ranksFrom_append_one {α : Type}
    (color : α → Nat) (p : List α) (v : α) :
    ∀ s, RanksFrom color s p →
      color v = s + p.length →
      RanksFrom color s (p ++ [v]) := by
  induction p with
  | nil =>
      intro s h hv
      refine ⟨?_, True.intro⟩
      simpa using hv
  | cons a rest ih =>
      intro s h hv
      refine ⟨h.1, ?_⟩
      apply ih (s + 1) h.2
      simp only [List.length_cons] at hv
      omega

inductive PrefixPathTo {k : Nat} (color : Vertex k → Fin k) :
    Nat → Vertex k → List (Vertex k) → Prop
  | zero (v : Vertex k) (hColor : (color v).val = 0) :
      PrefixPathTo color 0 v [v]
  | step {r : Nat} {u : Vertex k} {p : List (Vertex k)}
      (previous : PrefixPathTo color r u p)
      (v : Vertex k) (hEdge : Adj k u v)
      (hColor : (color v).val = r + 1) :
      PrefixPathTo color (r + 1) v (p ++ [v])

theorem prefixPathTo_last {k : Nat}
    {color : Vertex k → Fin k} {r : Nat}
    {v : Vertex k} {p : List (Vertex k)}
    (h : PrefixPathTo color r v p) :
    ∃ front, p = front ++ [v] := by
  cases h
  · exact ⟨[], rfl⟩
  · exact ⟨_, rfl⟩

theorem prefixPathTo_properties {k : Nat}
    {color : Vertex k → Fin k} {r : Nat}
    {v : Vertex k} {p : List (Vertex k)}
    (h : PrefixPathTo color r v p) :
    p.length = r + 1 ∧ EdgesAlong p ∧
      RanksFrom (fun w => (color w).val) 0 p := by
  induction h with
  | zero v hColor =>
      exact ⟨rfl, True.intro, hColor, True.intro⟩
  | @step r u p previous v hEdge hColor ih =>
      obtain ⟨hLength, hEdges, hRanks⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · obtain ⟨front, hp⟩ := prefixPathTo_last previous
        have hOld : EdgesAlong (front ++ [u]) := by
          rw [← hp]
          exact hEdges
        have hNew := edgesAlong_append_vertex front u v hOld hEdge
        simpa [hp, List.append_assoc] using hNew
      · apply ranksFrom_append_one
          (fun w => (color w).val) p v 0 hRanks
        omega

theorem prefixPathTo_full {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (v : Vertex k) (p : List (Vertex k))
    (h : PrefixPathTo color (k - 1) v p) :
    FullIncreasingPath k color p := by
  obtain ⟨hLength, hEdges, hRanks⟩ := prefixPathTo_properties h
  apply (fullIncreasingPath_iff_ranks color p).mpr
  exact ⟨by omega,
    ranksFrom_nodup (fun w => (color w).val) p 0 hRanks,
    hEdges, hRanks⟩

#print axioms prefixPathTo_full

end HansonToft
