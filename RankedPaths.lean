import ColorDeletion

namespace HansonToft

def RanksFrom {α : Type} (color : α → Nat) :
    Nat → List α → Prop
  | _, [] => True
  | s, v :: rest => color v = s ∧ RanksFrom color (s + 1) rest

theorem ranksFrom_lookup {α : Type} (color : α → Nat)
    (p : List α) :
    ∀ s, RanksFrom color s p →
      ∀ j v, p[j]? = some v → color v = s + j := by
  induction p with
  | nil =>
      intro s h j v hv
      simp at hv
  | cons w rest ih =>
      intro s h j v hv
      cases j with
      | zero =>
          have hw : w = v := by simpa using hv
          subst v
          simpa using h.1
      | succ j =>
          have hv' : rest[j]? = some v := by simpa using hv
          have hh := ih (s + 1) h.2 j v hv'
          omega

theorem ranksFrom_of_lookup {α : Type} (color : α → Nat)
    (p : List α) :
    ∀ s, (∀ j v, p[j]? = some v → color v = s + j) →
      RanksFrom color s p := by
  induction p with
  | nil =>
      intro s h
      trivial
  | cons w rest ih =>
      intro s h
      refine ⟨?_, ?_⟩
      · have hh := h 0 w rfl
        simpa using hh
      · apply ih (s + 1)
        intro j v hv
        have hh := h (j + 1) v (by simpa using hv)
        omega

theorem list_lookup_bound {α : Type} (p : List α) :
    ∀ j v, p[j]? = some v → j < p.length := by
  induction p with
  | nil =>
      intro j v hv
      simp at hv
  | cons w rest ih =>
      intro j v hv
      cases j with
      | zero =>
          simp
      | succ j =>
          have hv' : rest[j]? = some v := by simpa using hv
          have hh := ih j v hv'
          simp only [List.length_cons]
          omega

theorem fullIncreasingPath_iff_ranks {k : Nat}
    (c : Vertex k → Fin k) (p : List (Vertex k)) :
    FullIncreasingPath k c p ↔
      p.length = k ∧ p.Nodup ∧ EdgesAlong p ∧
      RanksFrom (fun v => (c v).val) 0 p := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    apply ranksFrom_of_lookup (fun v => (c v).val) p 0
    intro j v hj
    have hlen := h.1
    have hjlt : j < k := by
      have hb := list_lookup_bound p j v hj
      omega
    have heq := h.2.2.2 ⟨j, hjlt⟩ v hj
    have hval := congrArg Fin.val heq
    simpa using hval
  · rintro ⟨hlen, hnodup, hedges, hranks⟩
    refine ⟨hlen, hnodup, hedges, ?_⟩
    intro i v hv
    apply Fin.ext
    have hh := ranksFrom_lookup
      (fun v => (c v).val) p 0 hranks i.val v hv
    simpa using hh

#print axioms ranksFrom_lookup
#print axioms fullIncreasingPath_iff_ranks

end HansonToft
