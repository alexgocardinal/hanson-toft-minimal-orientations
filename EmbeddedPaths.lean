import RecoverableExtension

namespace HansonToft

theorem nodup_map_of_injective {α β : Type}
    (f : α → β)
    (hf : ∀ a b, f a = f b → a = b)
    (p : List α) (hp : p.Nodup) :
    (p.map f).Nodup := by
  induction p with
  | nil =>
      simp
  | cons a rest ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hp
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        obtain ⟨b, hb, heq⟩ := List.mem_map.mp hm
        have hba := hf b a heq
        subst b
        exact ha hb
      · exact ih ht

theorem ranksFrom_map {α β : Type}
    (f : α → β) (small : α → Nat) (large : β → Nat)
    (hf : ∀ a, large (f a) = small a)
    (p : List α) :
    ∀ s, RanksFrom small s p →
      RanksFrom large s (p.map f) := by
  induction p with
  | nil =>
      intro s hp
      trivial
  | cons a rest ih =>
      intro s hp
      exact ⟨(hf a).trans hp.1, ih (s + 1) hp.2⟩

theorem edgesAlong_embed {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (p : List (Vertex (m + 3)))
    (hp : EdgesAlong p) :
    EdgesAlong (p.map (embedVertex removed)) := by
  induction p with
  | nil =>
      trivial
  | cons u rest ih =>
      cases rest with
      | nil =>
          trivial
      | cons v tail =>
          exact ⟨(embedVertex_adj_iff removed u v).mpr hp.1,
            ih hp.2⟩

theorem embedded_full_path_properties {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (d : Vertex (m + 3) → Fin (m + 3))
    (c : Fin (m + 4))
    (hColors : ∀ u,
      expandColor c (d u) = color (embedVertex removed u))
    (p : List (Vertex (m + 3)))
    (hp : FullIncreasingPath (m + 3) d p) :
    (p.map (embedVertex removed)).length = m + 3 ∧
    (p.map (embedVertex removed)).Nodup ∧
    EdgesAlong (p.map (embedVertex removed)) ∧
    RanksFrom
      (fun v => shrinkRank c.val (color v).val) 0
      (p.map (embedVertex removed)) ∧
    (∀ v ∈ p.map (embedVertex removed),
      ∀ i, v ≠ deletedVertex removed i) := by
  have hRanks :=
    ((fullIncreasingPath_iff_ranks d p).mp hp).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using hp.1
  · exact nodup_map_of_injective (embedVertex removed)
      (fun a b h => embedVertex_injective removed a b h)
      p hp.2.1
  · exact edgesAlong_embed removed p hp.2.2.1
  · apply ranksFrom_map (embedVertex removed)
      (fun u => (d u).val)
      (fun v => shrinkRank c.val (color v).val)
      ?_ p 0 hRanks
    intro u
    have hv := congrArg Fin.val (hColors u)
    change expandRank c.val (d u).val =
      (color (embedVertex removed u)).val at hv
    rw [← hv]
    exact shrink_expand_rank c.val (d u).val
  · intro v hv i
    obtain ⟨u, hu, heq⟩ := List.mem_map.mp hv
    subst v
    exact embedVertex_not_deleted removed u i

#print axioms embedded_full_path_properties

end HansonToft
