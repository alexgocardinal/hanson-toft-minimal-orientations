import ColorRanks

namespace HansonToft

def vertexGroup {k : Nat} : Vertex k → Fin 7
  | .cycle i => i
  | .clique i _ => i

def vertexPosition {k : Nat} : Vertex k → Nat
  | .cycle _ => 0
  | .clique _ a => a.val

def deletedVertex {m : Nat}
    (removed : Fin 7 → Fin (m + 1)) (i : Fin 7) :
    Vertex (m + 4) :=
  .clique i ⟨(removed i).val, by
    have hi := (removed i).isLt
    omega⟩

def embedVertex {m : Nat}
    (removed : Fin 7 → Fin (m + 1)) :
    Vertex (m + 3) → Vertex (m + 4)
  | .cycle i => .cycle i
  | .clique i a =>
      .clique i ⟨expandRank (removed i).val a.val, by
        have ha := a.isLt
        unfold expandRank
        split <;> omega⟩

theorem embedVertex_injective {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (u v : Vertex (m + 3))
    (h : embedVertex removed u = embedVertex removed v) :
    u = v := by
  cases u with
  | cycle i =>
      cases v with
      | cycle j =>
          have hij : i = j := congrArg vertexGroup h
          cases hij
          rfl
      | clique j b =>
          simp [embedVertex] at h
  | clique i a =>
      cases v with
      | cycle j =>
          simp [embedVertex] at h
      | clique j b =>
          have hij : i = j := congrArg vertexGroup h
          subst j
          have hval :
              expandRank (removed i).val a.val =
                expandRank (removed i).val b.val :=
            congrArg vertexPosition h
          have hab : a = b :=
            Fin.ext (expandRank_injective
              (removed i).val a.val b.val hval)
          cases hab
          rfl

theorem embedVertex_adj_iff {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (u v : Vertex (m + 3)) :
    Adj (m + 4) (embedVertex removed u) (embedVertex removed v) ↔
      Adj (m + 3) u v := by
  cases u with
  | cycle i =>
      cases v with
      | cycle j => rfl
      | clique j b => rfl
  | clique i a =>
      cases v with
      | cycle j => rfl
      | clique j b =>
          by_cases hij : i = j
          · subst j
            constructor
            · intro h
              refine ⟨rfl, ?_⟩
              intro hab
              cases hab
              exact h.2 rfl
            · intro h
              refine ⟨rfl, ?_⟩
              intro heq
              apply h.2
              apply Fin.ext
              exact expandRank_injective
                (removed i).val a.val b.val (congrArg Fin.val heq)
          · simp [embedVertex, Adj, hij]

theorem embedVertex_not_deleted {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (u : Vertex (m + 3)) :
    ∀ i, embedVertex removed u ≠ deletedVertex removed i := by
  intro i
  cases u with
  | cycle j =>
      simp [embedVertex, deletedVertex]
  | clique j a =>
      intro h
      have hji : j = i := congrArg vertexGroup h
      subst i
      have hval :
          expandRank (removed j).val a.val = (removed j).val :=
        congrArg vertexPosition h
      exact expandRank_ne (removed j).val a.val hval

theorem embedVertex_range_iff {m : Nat}
    (removed : Fin 7 → Fin (m + 1))
    (v : Vertex (m + 4)) :
    (∃ u, embedVertex removed u = v) ↔
      ∀ i, v ≠ deletedVertex removed i := by
  constructor
  · rintro ⟨u, rfl⟩
    exact embedVertex_not_deleted removed u
  · intro hv
    cases v with
    | cycle j =>
        exact ⟨.cycle j, rfl⟩
    | clique j a =>
        have hne : a.val ≠ (removed j).val := by
          intro heq
          apply hv j
          apply congrArg (Vertex.clique j)
          exact Fin.ext heq
        let b : Fin ((m + 3) - 3) :=
          ⟨shrinkRank (removed j).val a.val, by
            have ha := a.isLt
            have hc := (removed j).isLt
            unfold shrinkRank
            split <;> omega⟩
        refine ⟨.clique j b, ?_⟩
        apply congrArg (Vertex.clique j)
        apply Fin.ext
        change expandRank (removed j).val
          (shrinkRank (removed j).val a.val) = a.val
        exact expand_shrink_rank (removed j).val a.val hne

#print axioms embedVertex_injective
#print axioms embedVertex_adj_iff
#print axioms embedVertex_range_iff

end HansonToft
