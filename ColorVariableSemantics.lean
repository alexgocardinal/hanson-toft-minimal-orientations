import CNFDisjunctionSemantics

namespace HansonToft

def colorVariable {k : Nat} (v : Vertex k) (rank : Nat) : Nat :=
  vertexNumber v * k + rank

theorem colorVariable_injective {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (u v : Vertex k) (a b : Fin k)
    (hEqual : colorVariable u a.val = colorVariable v b.val) :
    u = v ∧ a = b := by
  have hCases : k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (0 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (1 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (2 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (3 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (4 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩
  · have hNumbers : vertexNumber u = vertexNumber v := by
      have ha := a.isLt
      have hb := b.isLt
      unfold colorVariable at hEqual
      omega
    have hVertices :=
      (finite_numbering_correct (5 : Fin 6)).2.1 u v hNumbers
    have hRanks : a.val = b.val := by
      unfold colorVariable at hEqual
      rw [hNumbers] at hEqual
      omega
    exact ⟨hVertices, Fin.ext hRanks⟩

noncomputable def coloringAssignment {k : Nat}
    (color : Vertex k → Fin k) (varId : Nat) : Bool := by
  classical
  exact decide (∃ v, varId = colorVariable v (color v).val)

theorem coloringAssignment_at_color {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (v : Vertex k) (a : Fin k) :
    coloringAssignment color (colorVariable v a.val) =
      decide (color v = a) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [coloringAssignment, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hVertices, hRanks⟩ :=
      colorVariable_injective hk4 hk9 v u a (color u) hu
    subst u
    exact hRanks.symm
  · intro hColor
    refine ⟨v, ?_⟩
    rw [hColor]

theorem coloring_satisfies_at_least_one {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (v : Vertex k) :
    HoldsClause (coloringAssignment color)
      ((List.range k).map (fun rank => (colorVariable v rank, true))) := by
  apply (holdsClause_iff _ _).mpr
  refine ⟨(colorVariable v (color v).val, true), ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨(color v).val, List.mem_range.mpr (color v).isLt, rfl⟩
  · change coloringAssignment color (colorVariable v (color v).val) = true
    rw [coloringAssignment_at_color hk4 hk9 color v (color v)]
    simp

theorem coloring_satisfies_at_most_one {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (v : Vertex k)
    (a b : Fin k) (hab : a ≠ b) :
    HoldsClause (coloringAssignment color)
      [(colorVariable v a.val, false), (colorVariable v b.val, false)] := by
  rw [holdsClause_two]
  by_cases ha : color v = a
  · right
    have hb : color v ≠ b := by
      intro hb
      exact hab (ha.symm.trans hb)
    rw [coloringAssignment_at_color hk4 hk9 color v b]
    simp [hb]
  · left
    rw [coloringAssignment_at_color hk4 hk9 color v a]
    simp [ha]

theorem coloring_satisfies_edge_clause {k : Nat}
    (hk4 : 4 ≤ k) (hk9 : k ≤ 9)
    (color : Vertex k → Fin k) (hProper : Proper k k color)
    (u v : Vertex k) (hAdj : Adj k u v) (a : Fin k) :
    HoldsClause (coloringAssignment color)
      [(colorVariable u a.val, false), (colorVariable v a.val, false)] := by
  rw [holdsClause_two]
  by_cases hu : color u = a
  · right
    have hv : color v ≠ a := by
      intro hv
      exact hProper u v hAdj (hu.trans hv.symm)
    rw [coloringAssignment_at_color hk4 hk9 color v a]
    simp [hv]
  · left
    rw [coloringAssignment_at_color hk4 hk9 color u a]
    simp [hu]

#print axioms coloring_satisfies_edge_clause

end HansonToft
