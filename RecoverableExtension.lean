import FullPathExtension

namespace HansonToft

theorem full_path_insert_anywhere_with_recovery {k : Nat}
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
    ∃ q, FullIncreasingPath k color q ∧
      q.filter (Survives removed) = p := by
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
          refine ⟨_, hi, ?_⟩
          exact recover_middle_insertion
            removed [] (u :: tail) i hKeep
  | cons x xs =>
      obtain ⟨before, u, hf⟩ :=
        nonempty_list_has_last (x :: xs) (by simp)
      simp only [hf] at hLength hEdges hSimple hKeep hRanks hExpand hPosition ⊢
      cases rest with
      | nil =>
          simp only [List.append_nil] at *
          obtain ⟨i, hi⟩ := full_path_insert_last
            removed color ranks c before u
            hLength hEdges hSimple hKeep hRanks
            hPosition.symm hRemoved hExpand
          refine ⟨_, hi, ?_⟩
          simpa [List.append_assoc] using
            (recover_middle_insertion removed (before ++ [u]) [] i
              (by simpa using hKeep))
      | cons v tail =>
          simp only [List.append_assoc, List.cons_append,
            List.nil_append] at *
          obtain ⟨i, hi⟩ := full_path_insert_interior
            removed color ranks c before tail u v
            hLength hEdges hSimple hKeep hRanks
            hPosition.symm hRemoved hExpand
          refine ⟨_, hi, ?_⟩
          simpa [List.append_assoc] using
            (recover_middle_insertion removed
              (before ++ [u]) (v :: tail) i
              (by simpa [List.append_assoc] using hKeep))

#print axioms full_path_insert_anywhere_with_recovery

end HansonToft
