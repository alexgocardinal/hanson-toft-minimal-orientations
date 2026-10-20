import PathRecovery
import Lean.Elab.Tactic.Omega

namespace HansonToft

def expandRank (c j : Nat) : Nat :=
  if j < c then j else j + 1

def shrinkRank (c j : Nat) : Nat :=
  if j < c then j else j - 1

theorem expandRank_ne (c j : Nat) :
    expandRank c j ≠ c := by
  unfold expandRank
  split <;> omega

theorem shrink_expand_rank (c j : Nat) :
    shrinkRank c (expandRank c j) = j := by
  by_cases h : j < c
  · simp [expandRank, shrinkRank, h]
  · have h' : ¬ j + 1 < c := by omega
    simp [expandRank, shrinkRank, h, h']

theorem expand_shrink_rank (c j : Nat) (hne : j ≠ c) :
    expandRank c (shrinkRank c j) = j := by
  by_cases h : j < c
  · simp [expandRank, shrinkRank, h]
  · have h' : ¬ j - 1 < c := by omega
    have hj : 1 ≤ j := by omega
    simp [expandRank, shrinkRank, h, h', Nat.sub_add_cancel hj]

theorem expandRank_injective (c a b : Nat)
    (h : expandRank c a = expandRank c b) :
    a = b := by
  have h' := congrArg (shrinkRank c) h
  simpa only [shrink_expand_rank] using h'

theorem expandRank_lt_iff (c a b : Nat) :
    expandRank c a < expandRank c b ↔ a < b := by
  unfold expandRank
  split <;> split <;> constructor <;> intro h <;> omega

theorem expandRank_bound {n : Nat}
    (c : Fin (n + 1)) (j : Fin n) :
    expandRank c.val j.val < n + 1 := by
  have hj := j.isLt
  unfold expandRank
  split <;> omega

theorem shrinkRank_bound {n : Nat}
    (c j : Fin (n + 1)) (hne : j ≠ c) :
    shrinkRank c.val j.val < n := by
  have hj := j.isLt
  have hc := c.isLt
  have hval : j.val ≠ c.val := by
    intro h
    exact hne (Fin.ext h)
  unfold shrinkRank
  split <;> omega

def expandColor {n : Nat}
    (c : Fin (n + 1)) (j : Fin n) : Fin (n + 1) :=
  ⟨expandRank c.val j.val, expandRank_bound c j⟩

def compressColor {n : Nat}
    (c j : Fin (n + 1)) (hne : j ≠ c) : Fin n :=
  ⟨shrinkRank c.val j.val, shrinkRank_bound c j hne⟩

theorem expandColor_ne {n : Nat}
    (c : Fin (n + 1)) (j : Fin n) :
    expandColor c j ≠ c := by
  intro h
  exact expandRank_ne c.val j.val (congrArg Fin.val h)

theorem compress_expand_color {n : Nat}
    (c : Fin (n + 1)) (j : Fin n) :
    compressColor c (expandColor c j) (expandColor_ne c j) = j := by
  apply Fin.ext
  exact shrink_expand_rank c.val j.val

theorem expand_compress_color {n : Nat}
    (c j : Fin (n + 1)) (hne : j ≠ c) :
    expandColor c (compressColor c j hne) = j := by
  apply Fin.ext
  apply expand_shrink_rank
  intro h
  exact hne (Fin.ext h)

#print axioms expandRank_lt_iff
#print axioms compress_expand_color
#print axioms expand_compress_color

end HansonToft
