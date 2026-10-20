import EmbeddedPaths

namespace HansonToft

def selectedIndex {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (i : Fin 7) : Fin ((m + 4) - 3) :=
  ⟨(removed i).val, by
    have hi := (removed i).isLt
    omega⟩

theorem selected_vertex_eq_deleted {m : Nat}
    (removed : Fin 7 → Fin (m + 1)) (i : Fin 7) :
    Vertex.clique i (selectedIndex removed i) =
      deletedVertex removed i := by
  rfl

theorem lift_full_path_after_deletion {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (d : Vertex (m + 3) → Fin (m + 3))
    (c : Fin (m + 4))
    (hColors : ∀ u,
      expandColor c (d u) = color (embedVertex removed u))
    (hRemoved : ∀ i, color (deletedVertex removed i) = c)
    (p : List (Vertex (m + 3)))
    (hp : FullIncreasingPath (m + 3) d p) :
    ∃ q, FullIncreasingPath (m + 4) color q ∧
      q.filter (Survives (selectedIndex removed)) =
        p.map (embedVertex removed) := by
  obtain ⟨hLength, hSimple, hEdges, hRanks, hKeep⟩ :=
    embedded_full_path_properties removed color d c hColors p hp
  have hNonempty : p.map (embedVertex removed) ≠ [] := by
    intro h
    have hz : (p.map (embedVertex removed)).length = 0 := by
      rw [h]
      rfl
    omega
  have hKeepSelected :
      ∀ v ∈ p.map (embedVertex removed),
        ∀ i, v ≠ .clique i (selectedIndex removed i) := by
    intro v hv i
    simpa only [selected_vertex_eq_deleted] using hKeep v hv i
  have hRemovedSelected :
      ∀ i, color (.clique i (selectedIndex removed i)) = c := by
    intro i
    simpa only [selected_vertex_eq_deleted] using hRemoved i
  have hExpand :
      ∀ v ∈ p.map (embedVertex removed),
        (color v).val =
          expandRank c.val (shrinkRank c.val (color v).val) := by
    intro v hv
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hv
    subst v
    have hc := congrArg Fin.val (hColors u)
    change expandRank c.val (d u).val =
      (color (embedVertex removed u)).val at hc
    rw [← hc, shrink_expand_rank]
  exact full_path_insert_anywhere_with_recovery
    (selectedIndex removed) color
    (fun v => shrinkRank c.val (color v).val)
    c (p.map (embedVertex removed))
    hNonempty (by omega) hEdges hSimple
    hKeepSelected hRanks hRemovedSelected hExpand

#print axioms lift_full_path_after_deletion

end HansonToft
