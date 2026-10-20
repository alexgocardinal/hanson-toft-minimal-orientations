import ConditionalPathLift

namespace HansonToft

theorem list_map_injective_of {α β : Type}
    (f : α → β)
    (hf : ∀ a b, f a = f b → a = b)
    (p : List α) :
    ∀ q, p.map f = q.map f → p = q := by
  induction p with
  | nil =>
      intro q h
      cases q with
      | nil => rfl
      | cons b rest => simp at h
  | cons a rest ih =>
      intro q h
      cases q with
      | nil => simp at h
      | cons b tail =>
          have hh : f a = f b ∧ rest.map f = tail.map f :=
            List.cons.inj h
          have hab := hf a b hh.1
          have htail := ih tail hh.2
          cases hab
          cases htail
          rfl

theorem lift_two_full_paths {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (d : Vertex (m + 3) → Fin (m + 3))
    (c : Fin (m + 4))
    (hColors : ∀ u,
      expandColor c (d u) = color (embedVertex removed u))
    (hRemoved : ∀ i, color (deletedVertex removed i) = c)
    (hSmall : HasTwoFullPaths (m + 3) d) :
    HasTwoFullPaths (m + 4) color := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hSmall
  obtain ⟨outP, hOutP, hRecoverP⟩ :=
    lift_full_path_after_deletion removed color d c
      hColors hRemoved p hp
  obtain ⟨outQ, hOutQ, hRecoverQ⟩ :=
    lift_full_path_after_deletion removed color d c
      hColors hRemoved q hq
  refine ⟨outP, outQ, hOutP, hOutQ, ?_⟩
  intro heq
  apply hpq
  apply list_map_injective_of (embedVertex removed)
    (fun a b h => embedVertex_injective removed a b h) p q
  calc
    p.map (embedVertex removed) =
        outP.filter (Survives (selectedIndex removed)) :=
      hRecoverP.symm
    _ = outQ.filter (Survives (selectedIndex removed)) :=
      congrArg
        (fun xs => xs.filter (Survives (selectedIndex removed))) heq
    _ = q.map (embedVertex removed) := hRecoverQ

theorem two_paths_after_common_color_deletion {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (color : Vertex (m + 4) → Fin (m + 4))
    (hProper : Proper (m + 4) (m + 4) color)
    (c : Fin (m + 4))
    (hCycle : ∀ i, color (.cycle i) ≠ c)
    (hRemoved : ∀ i, color (deletedVertex removed i) = c)
    (hSmall : ∀ d : Vertex (m + 3) → Fin (m + 3),
      Proper (m + 3) (m + 3) d →
        HasTwoFullPaths (m + 3) d) :
    HasTwoFullPaths (m + 4) color := by
  obtain ⟨d, hd, hColors⟩ :=
    proper_coloring_after_deletion
      removed color hProper c hCycle hRemoved
  exact lift_two_full_paths removed color d c
    hColors hRemoved (hSmall d hd)

#print axioms lift_two_full_paths
#print axioms two_paths_after_common_color_deletion

end HansonToft
