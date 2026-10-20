import InteriorFullPath

namespace HansonToft

theorem edgesAlong_append_vertex {k : Nat}
    (front : List (Vertex k)) (u z : Vertex k)
    (hPath : EdgesAlong (front ++ [u]))
    (huz : Adj k u z) :
    EdgesAlong (front ++ [u, z]) := by
  revert hPath
  induction front with
  | nil =>
      intro hPath
      exact ⟨huz, True.intro⟩
  | cons w front ih =>
      intro hPath
      cases front with
      | nil =>
          exact ⟨hPath.1, huz, True.intro⟩
      | cons w' front =>
          exact ⟨hPath.1, ih hPath.2⟩

theorem full_path_insert_first {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (color : Vertex k → Fin k)
    (ranks : Vertex k → Nat) (c : Fin k)
    (u : Vertex k) (rest : List (Vertex k))
    (hLength : (u :: rest).length + 1 = k)
    (hEdges : EdgesAlong (u :: rest))
    (hSimple : (u :: rest).Nodup)
    (hKeep : ∀ w ∈ u :: rest,
      ∀ i, w ≠ .clique i (removed i))
    (hRanks : RanksFrom ranks 0 (u :: rest))
    (hPosition : c.val = 0)
    (hRemoved : ∀ i, color (.clique i (removed i)) = c)
    (hExpand : ∀ w ∈ u :: rest,
      (color w).val = expandRank c.val (ranks w)) :
    ∃ i, FullIncreasingPath k color
      (.clique i (removed i) :: u :: rest) := by
  obtain ⟨i, hzu⟩ := endpoint_has_insertable_vertex
    removed u (hKeep u (by simp))
  have hFresh : .clique i (removed i) ∉ u :: rest := by
    intro h
    exact hKeep _ h i rfl
  refine ⟨i, ?_⟩
  apply (fullIncreasingPath_iff_ranks color
    (.clique i (removed i) :: u :: rest)).mpr
  refine ⟨?_, List.nodup_cons.mpr ⟨hFresh, hSimple⟩,
    ⟨hzu, hEdges⟩, ?_⟩
  · simpa only [List.length_cons] using hLength
  · exact ranksFrom_insert_missing
      ranks (fun w => (color w).val) [] (u :: rest)
      (.clique i (removed i)) 0 c.val
      (by simpa using hPosition)
      hRanks (congrArg Fin.val (hRemoved i)) hExpand

theorem full_path_insert_last {k : Nat}
    (removed : Fin 7 → Fin (k - 3))
    (color : Vertex k → Fin k)
    (ranks : Vertex k → Nat) (c : Fin k)
    (front : List (Vertex k)) (u : Vertex k)
    (hLength : (front ++ [u]).length + 1 = k)
    (hEdges : EdgesAlong (front ++ [u]))
    (hSimple : (front ++ [u]).Nodup)
    (hKeep : ∀ w ∈ front ++ [u],
      ∀ i, w ≠ .clique i (removed i))
    (hRanks : RanksFrom ranks 0 (front ++ [u]))
    (hPosition : c.val = (front ++ [u]).length)
    (hRemoved : ∀ i, color (.clique i (removed i)) = c)
    (hExpand : ∀ w ∈ front ++ [u],
      (color w).val = expandRank c.val (ranks w)) :
    ∃ i, FullIncreasingPath k color
      (front ++ [u, .clique i (removed i)]) := by
  obtain ⟨i, hzu⟩ := endpoint_has_insertable_vertex
    removed u (hKeep u (by simp))
  have huz : Adj k u (.clique i (removed i)) :=
    (adj_symmetric k u (.clique i (removed i))).mpr hzu
  have hFresh : .clique i (removed i) ∉ front ++ [u] := by
    intro h
    exact hKeep _ h i rfl
  have hNewSimple := nodup_insert_middle
    (front ++ [u]) [] (.clique i (removed i))
    (by simpa using hSimple) (by simpa using hFresh)
  have hNewRanks := ranksFrom_insert_missing
    ranks (fun w => (color w).val) (front ++ [u]) []
    (.clique i (removed i)) 0 c.val
    (by simpa using hPosition)
    (by simpa using hRanks)
    (congrArg Fin.val (hRemoved i))
    (by simpa using hExpand)
  refine ⟨i, ?_⟩
  apply (fullIncreasingPath_iff_ranks color
    (front ++ [u, .clique i (removed i)])).mpr
  refine ⟨?_, ?_, edgesAlong_append_vertex front u _ hEdges huz, ?_⟩
  · simp only [List.length_append, List.length_cons,
      List.length_nil] at hLength ⊢
    omega
  · simpa [List.append_assoc] using hNewSimple
  · simpa [List.append_assoc] using hNewRanks

#print axioms full_path_insert_first
#print axioms full_path_insert_last

end HansonToft
