import SequentialCounterSemantics

namespace HansonToft

def registerWidth (k : Nat) : Nat :=
  7 * (k - 2) * k

def reachVariable {k : Nat} (v : Vertex k) (rank : Nat) : Nat :=
  registerWidth k + colorVariable v rank

def multiplicityVariable {k : Nat}
    (v : Vertex k) (rank : Nat) : Nat :=
  registerWidth k + registerWidth k + colorVariable v rank

theorem colorVariable_bound {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (v : Vertex k) (rank : Fin k) :
    colorVariable v rank.val < registerWidth k := by
  let s : Fin 6 := ⟨k - 4, by omega⟩
  have hs : s.val + 4 = k := by
    dsimp [s]
    omega
  have hNumbers :
      ∀ u : Vertex k, vertexNumber u < 7 * (k - 2) := by
    have hType := congrArg
      (fun t : Nat =>
        ∀ u : Vertex t, vertexNumber u < 7 * (t - 2)) hs
    exact Eq.mp hType ((finite_numbering_correct s).1)
  have hNumber := hNumbers v
  have hMultiply :=
    Nat.mul_le_mul_right k (Nat.succ_le_of_lt hNumber)
  change (vertexNumber v + 1) * k ≤
    7 * (k - 2) * k at hMultiply
  have hRank := rank.isLt
  unfold colorVariable registerWidth
  rw [Nat.add_mul] at hMultiply
  simp only [Nat.one_mul] at hMultiply
  omega

theorem reachVariable_injective {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (u v : Vertex k) (a b : Fin k)
    (h : reachVariable u a.val = reachVariable v b.val) :
    u = v ∧ a = b := by
  have hColor :
      colorVariable u a.val = colorVariable v b.val := by
    unfold reachVariable at h
    omega
  exact colorVariable_injective hk4 hk9 u v a b hColor

theorem multiplicityVariable_injective {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (u v : Vertex k) (a b : Fin k)
    (h : multiplicityVariable u a.val =
      multiplicityVariable v b.val) :
    u = v ∧ a = b := by
  have hColor :
      colorVariable u a.val = colorVariable v b.val := by
    unfold multiplicityVariable at h
    omega
  exact colorVariable_injective hk4 hk9 u v a b hColor

def RegisterTruth {k : Nat}
    (color : Vertex k → Fin k) (varId : Nat) : Prop :=
  (∃ v, varId = colorVariable v (color v).val) ∨
  (∃ (v : Vertex k) (rank : Fin k),
    varId = reachVariable v rank.val ∧
      ReachesRank color rank.val v) ∨
  (∃ (v : Vertex k) (rank : Fin k),
    varId = multiplicityVariable v rank.val ∧
      MultipleRankPaths color rank.val v)

noncomputable def registerAssignment {k : Nat}
    (color : Vertex k → Fin k) (varId : Nat) : Bool := by
  classical
  exact decide (RegisterTruth color varId)

theorem registerTruth_at_color {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    RegisterTruth color (colorVariable v a.val) ↔
      color v = a := by
  have hTarget := colorVariable_bound hk4 hk9 v a
  unfold RegisterTruth
  constructor
  · rintro (⟨u, h⟩ | ⟨u, b, h, hPath⟩ |
      ⟨u, b, h, hMultiple⟩)
    · obtain ⟨hvu, ha⟩ :=
        colorVariable_injective hk4 hk9 v u a (color u) h
      simpa only [hvu] using ha.symm
    · unfold reachVariable at h
      omega
    · unfold multiplicityVariable at h
      omega
  · intro hColor
    exact Or.inl ⟨v, by rw [hColor]⟩

theorem registerTruth_at_reach {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    RegisterTruth color (reachVariable v a.val) ↔
      ReachesRank color a.val v := by
  have hTarget := colorVariable_bound hk4 hk9 v a
  unfold RegisterTruth
  constructor
  · rintro (⟨u, h⟩ | ⟨u, b, h, hPath⟩ |
      ⟨u, b, h, hMultiple⟩)
    · have hOther := colorVariable_bound hk4 hk9 u (color u)
      unfold reachVariable at h
      omega
    · obtain ⟨rfl, rfl⟩ :=
        reachVariable_injective hk4 hk9 v u a b h
      exact hPath
    · have hOther := colorVariable_bound hk4 hk9 u b
      unfold reachVariable multiplicityVariable at h
      omega
  · intro hPath
    exact Or.inr (Or.inl ⟨v, a, rfl, hPath⟩)

theorem registerTruth_at_multiplicity {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    RegisterTruth color (multiplicityVariable v a.val) ↔
      MultipleRankPaths color a.val v := by
  have hTarget := colorVariable_bound hk4 hk9 v a
  unfold RegisterTruth
  constructor
  · rintro (⟨u, h⟩ | ⟨u, b, h, hPath⟩ |
      ⟨u, b, h, hMultiple⟩)
    · have hOther := colorVariable_bound hk4 hk9 u (color u)
      unfold multiplicityVariable at h
      omega
    · have hOther := colorVariable_bound hk4 hk9 u b
      unfold reachVariable multiplicityVariable at h
      omega
    · obtain ⟨rfl, rfl⟩ :=
        multiplicityVariable_injective hk4 hk9 v u a b h
      exact hMultiple
  · intro hMultiple
    exact Or.inr (Or.inr ⟨v, a, rfl, hMultiple⟩)

theorem registerAssignment_correct {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k)
    (v : Vertex k) (a : Fin k) :
    (registerAssignment color (colorVariable v a.val) = true ↔
      color v = a) ∧
    (registerAssignment color (reachVariable v a.val) = true ↔
      ReachesRank color a.val v) ∧
    (registerAssignment color
        (multiplicityVariable v a.val) = true ↔
      MultipleRankPaths color a.val v) := by
  classical
  simp only [registerAssignment, decide_eq_true_eq]
  exact ⟨registerTruth_at_color hk4 hk9 color v a,
    registerTruth_at_reach hk4 hk9 color v a,
    registerTruth_at_multiplicity hk4 hk9 color v a⟩

#print axioms colorVariable_bound
#print axioms registerAssignment_correct

end HansonToft
