import CycleTripleLemma

namespace HansonToft

theorem no_injection_fin_successor (n : Nat) :
    ∀ f : Fin (n + 1) → Fin n,
      (∀ a b, f a = f b → a = b) → False := by
  induction n with
  | zero =>
      intro f hf
      have h := (f ⟨0, by omega⟩).isLt
      omega
  | succ n ih =>
      intro f hf
      let last : Fin (n + 1 + 1) := ⟨n + 1, by omega⟩
      let embed : Fin (n + 1) → Fin (n + 1 + 1) :=
        fun a => ⟨a.val, by
          have ha := a.isLt
          omega⟩
      let c : Fin (n + 1) := f last
      have hAvoid : ∀ a, f (embed a) ≠ c := by
        intro a heq
        have hEq := hf (embed a) last heq
        have hv := congrArg Fin.val hEq
        change a.val = n + 1 at hv
        have ha := a.isLt
        omega
      let g : Fin (n + 1) → Fin n :=
        fun a => compressColor c (f (embed a)) (hAvoid a)
      apply ih g
      intro a b hab
      have hImage : f (embed a) = f (embed b) := by
        calc
          f (embed a) = expandColor c (g a) :=
            (expand_compress_color c _ (hAvoid a)).symm
          _ = expandColor c (g b) := congrArg (expandColor c) hab
          _ = f (embed b) :=
            expand_compress_color c _ (hAvoid b)
      have hDomain := hf (embed a) (embed b) hImage
      apply Fin.ext
      have hValues := congrArg Fin.val hDomain
      exact hValues

theorem finite_injection_bound {a b : Nat}
    (f : Fin a → Fin b)
    (hf : ∀ x y, f x = f y → x = y) :
    a ≤ b := by
  apply Classical.byContradiction
  intro hNot
  have hSize : b + 1 ≤ a := by omega
  let embed : Fin (b + 1) → Fin a :=
    fun x => ⟨x.val, by
      have hx := x.isLt
      omega⟩
  apply no_injection_fin_successor b (fun x => f (embed x))
  intro x y hxy
  have hDomain := hf (embed x) (embed y) hxy
  apply Fin.ext
  have hValues := congrArg Fin.val hDomain
  exact hValues

#print axioms no_injection_fin_successor
#print axioms finite_injection_bound

end HansonToft
