import EndpointFullPaths

namespace HansonToft

theorem split_list_at_length {α : Type} (r : Nat) :
    ∀ p : List α, r ≤ p.length →
      ∃ front rest, p = front ++ rest ∧ front.length = r := by
  induction r with
  | zero =>
      intro p hr
      exact ⟨[], p, rfl, rfl⟩
  | succ r ih =>
      intro p hr
      cases p with
      | nil =>
          simp at hr
      | cons x xs =>
          have hr' : r ≤ xs.length := by
            simp only [List.length_cons] at hr
            omega
          obtain ⟨front, rest, hp, hf⟩ := ih xs hr'
          refine ⟨x :: front, rest, ?_, ?_⟩
          · simpa only [List.cons_append] using
              congrArg (List.cons x) hp
          · simp [hf]

theorem nonempty_list_has_last {α : Type} (p : List α) :
    p ≠ [] → ∃ front u, p = front ++ [u] := by
  induction p with
  | nil =>
      intro h
      exact False.elim (h rfl)
  | cons x xs ih =>
      intro h
      cases xs with
      | nil =>
          exact ⟨[], x, rfl⟩
      | cons y ys =>
          obtain ⟨front, u, hp⟩ := ih (by simp)
          refine ⟨x :: front, u, ?_⟩
          simpa only [List.cons_append] using
            congrArg (List.cons x) hp

theorem full_path_insert_anywhere {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (color : Vertex k → Fin k)
    (ranks : Vertex k → Nat) (c : Fin k)
    (p : List (Vertex k))
    (hNonempty : p ≠ [])
    (hLength : p.length + 1 = k)
    (hEdges : EdgesAlong p)
    (hSimple : p.Nodup)
    (hKeep : ∀ w ∈ p, ∀ i, w ≠ .clique i (removed i))
    (hRanks : RanksFrom ranks 0 p)
    (hRemoved : ∀ i, color (.clique i (removed i)) = c)
    (hExpand : ∀ w ∈ p,
      (color w).val = expandRank c.val (ranks w)) :
    ∃ q, FullIncreasingPath k color q := by
  have hc : c.val ≤ p.length := by
    have hb := c.isLt
    omega
  obtain ⟨front, rest, hp, hPosition⟩ :=
    split_list_at_length c.val p hc
  subst p
  cases front with
  | nil =>
      simp only [List.nil_append] at *
      cases rest with
      | nil =>
          exact False.elim (hNonempty rfl)
      | cons u tail =>
          obtain ⟨i, hi⟩ := full_path_insert_first
            removed color ranks c u tail
            hLength hEdges hSimple hKeep hRanks
            (by simpa using hPosition.symm)
            hRemoved hExpand
          exact ⟨_, hi⟩
  | cons x xs =>
      obtain ⟨before, u, hf⟩ :=
        nonempty_list_has_last (x :: xs) (by simp)
      simp only [hf] at hLength hEdges hSimple hKeep hRanks hExpand hPosition
      cases rest with
      | nil =>
          simp only [List.append_nil] at *
          obtain ⟨i, hi⟩ := full_path_insert_last
            removed color ranks c before u
            hLength hEdges hSimple hKeep hRanks
            hPosition.symm hRemoved hExpand
          exact ⟨_, hi⟩
      | cons v tail =>
          simp only [List.append_assoc, List.cons_append,
            List.nil_append] at *
          obtain ⟨i, hi⟩ := full_path_insert_interior
            removed color ranks c before tail u v
            hLength hEdges hSimple hKeep hRanks
            hPosition.symm hRemoved hExpand
          exact ⟨_, hi⟩

#print axioms full_path_insert_anywhere

end HansonToft
