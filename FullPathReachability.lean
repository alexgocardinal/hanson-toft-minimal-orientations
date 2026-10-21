import FinalEndpointSemantics
import FullPathExtension

namespace HansonToft

theorem edgesAlong_before_last {k : Nat}
    (front : List (Vertex k)) (v : Vertex k)
    (h : EdgesAlong (front ++ [v])) :
    EdgesAlong front := by
  revert h
  induction front with
  | nil =>
      intro h
      trivial
  | cons u front ih =>
      intro h
      cases front with
      | nil =>
          trivial
      | cons w rest =>
          exact ⟨h.1, ih h.2⟩

theorem ranksFrom_before_last {α : Type}
    (rank : α → Nat) (front : List α) (v : α) :
    ∀ s, RanksFrom rank s (front ++ [v]) →
      RanksFrom rank s front ∧ rank v = s + front.length := by
  induction front with
  | nil =>
      intro s h
      exact ⟨trivial, by simpa using h.1⟩
  | cons u front ih =>
      intro s h
      obtain ⟨hBefore, hLast⟩ := ih (s + 1) h.2
      refine ⟨⟨h.1, hBefore⟩, ?_⟩
      simp only [List.length_cons]
      omega

theorem ranked_append_gives_prefix {k : Nat}
    (color : Vertex k → Fin k)
    (front : List (Vertex k)) (v : Vertex k)
    (hEdges : EdgesAlong (front ++ [v]))
    (hRanks : RanksFrom (fun w => (color w).val) 0
      (front ++ [v])) :
    PrefixPathTo color front.length v (front ++ [v]) := by
  have build : ∀ n : Nat,
      ∀ front : List (Vertex k), front.length = n →
      ∀ v : Vertex k,
        EdgesAlong (front ++ [v]) →
        RanksFrom (fun w => (color w).val) 0
          (front ++ [v]) →
        PrefixPathTo color n v (front ++ [v]) := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih front hLength v hEdges hRanks
    by_cases hEmpty : front = []
    · subst front
      have hn : n = 0 := by simpa using hLength.symm
      subst n
      exact PrefixPathTo.zero v hRanks.1
    · obtain ⟨before, u, hFront⟩ :=
        nonempty_list_has_last front hEmpty
      subst front
      have hLess : before.length < n := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hLength
        omega
      have hn : n = before.length + 1 := by
        simpa using hLength.symm
      have hSplit := ranksFrom_before_last
        (fun w => (color w).val) (before ++ [u]) v 0 hRanks
      have hPreviousEdges :
          EdgesAlong (before ++ [u]) :=
        edgesAlong_before_last (before ++ [u]) v hEdges
      have hPrevious := ih before.length hLess before rfl u
        hPreviousEdges hSplit.1
      have hTail : EdgesAlong [u, v] :=
        edgesAlong_drop_prefix before [u, v]
          (by simpa [List.append_assoc] using hEdges)
      have hColor : (color v).val = before.length + 1 := by
        simpa using hSplit.2
      have hStep := PrefixPathTo.step
        hPrevious v hTail.1 hColor
      simpa [List.append_assoc, hn] using hStep
  exact build front.length front rfl v hEdges hRanks

theorem full_path_gives_final_reachability {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k)
    (p : List (Vertex k))
    (hp : FullIncreasingPath k color p) :
    ∃ v, ReachesRank color (k - 1) v := by
  have hNonempty : p ≠ [] := by
    intro hEmpty
    have hLength := hp.1
    rw [hEmpty] at hLength
    simp only [List.length_nil] at hLength
    omega
  obtain ⟨front, v, hList⟩ :=
    nonempty_list_has_last p hNonempty
  have hProperties := (fullIncreasingPath_iff_ranks color p).mp hp
  rw [hList] at hProperties
  have hLength : front.length = k - 1 := by
    have h := hProperties.1
    simp only [List.length_append, List.length_cons,
      List.length_nil] at h
    omega
  refine ⟨v, front ++ [v], ?_⟩
  have hPrefix := ranked_append_gives_prefix color front v
    hProperties.2.2.1 hProperties.2.2.2
  simpa only [hLength] using hPrefix

theorem full_path_exists_iff_final_reachability {k : Nat}
    (hk : 0 < k) (color : Vertex k → Fin k) :
    (∃ p, FullIncreasingPath k color p) ↔
      ∃ v, ReachesRank color (k - 1) v := by
  constructor
  · rintro ⟨p, hp⟩
    exact full_path_gives_final_reachability hk color p hp
  · rintro ⟨v, p, hp⟩
    exact ⟨p, prefixPathTo_full hk color v p hp⟩

#print axioms ranked_append_gives_prefix
#print axioms full_path_exists_iff_final_reachability

end HansonToft
