import EncodedGateAssignment

namespace HansonToft

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

instance vertexExistsDecidable
    (k : Nat) (p : Vertex k → Prop) [DecidablePred p] :
    Decidable (∃ v, p v) := by
  have hIff :
      ((∃ i : Fin 7, p (.cycle i)) ∨
        (∃ (i : Fin 7) (a : Fin (k - 3)), p (.clique i a))) ↔
      ∃ v, p v := by
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, a, hi⟩)
      · exact ⟨.cycle i, hi⟩
      · exact ⟨.clique i a, hi⟩
    · rintro ⟨v, hv⟩
      cases v with
      | cycle i =>
          exact Or.inl ⟨i, hv⟩
      | clique i a =>
          exact Or.inr ⟨i, a, hv⟩
  exact decidable_of_iff _ hIff

theorem finite_numbering_surjective :
    ∀ s : Fin 6,
      ∀ j : Fin (7 * ((s.val + 4) - 2)),
        ∃ v : Vertex (s.val + 4), vertexNumber v = j.val := by
  decide +native

theorem encodingR_of_vertexNumber {k : Nat}
    (v : Vertex k) (j rank : Nat)
    (hNumber : vertexNumber v = j) :
    encodingR k j rank = reachVariable v rank := by
  change registerWidth k + (j * k + rank) =
    registerWidth k + (vertexNumber v * k + rank)
  rw [hNumber]

noncomputable def finalEndpointInputs {k : Nat}
    (color : Vertex k → Fin k) (j : Nat) : Bool :=
  gateExtendedAssignment color (encodingR k j (k - 1))

theorem unique_path_numeric_endpoints_at_most_one
    (s : Fin 6)
    (color : Vertex (s.val + 4) → Fin (s.val + 4))
    (hUnique : HasUniqueFullPath (s.val + 4) color) :
    AtMostOneTrue (7 * ((s.val + 4) - 2))
      (finalEndpointInputs color) := by
  have hk4 : 4 ≤ s.val + 4 := by omega
  have hk9 : s.val + 4 ≤ 9 := by
    have hs := s.isLt
    omega
  let rank : Fin (s.val + 4) :=
    ⟨(s.val + 4) - 1, by omega⟩
  intro i j hi hj hiTrue hjTrue
  obtain ⟨u, hu⟩ := finite_numbering_surjective s ⟨i, hi⟩
  obtain ⟨v, hv⟩ := finite_numbering_surjective s ⟨j, hj⟩
  have hAddressU := encodingR_of_vertexNumber
    u i ((s.val + 4) - 1) hu
  have hAddressV := encodingR_of_vertexNumber
    v j ((s.val + 4) - 1) hv
  have hInputU :
      gateExtendedAssignment color
        (reachVariable u rank.val) = true := by
    simpa only [finalEndpointInputs, hAddressU] using hiTrue
  have hInputV :
      gateExtendedAssignment color
        (reachVariable v rank.val) = true := by
    simpa only [finalEndpointInputs, hAddressV] using hjTrue
  have hReachU :=
    ((gateExtendedAssignment_correct hk4 hk9 color u rank).2.1).mp
      hInputU
  have hReachV :=
    ((gateExtendedAssignment_correct hk4 hk9 color v rank).2.1).mp
      hInputV
  have hVertices := unique_full_path_has_one_final_endpoint
    (by omega) color hUnique u v hReachU hReachV
  calc
    i = vertexNumber u := hu.symm
    _ = vertexNumber v := congrArg
      (fun w : Vertex (s.val + 4) => vertexNumber w) hVertices
    _ = j := hv

#print axioms finite_numbering_surjective
#print axioms unique_path_numeric_endpoints_at_most_one

end HansonToft
