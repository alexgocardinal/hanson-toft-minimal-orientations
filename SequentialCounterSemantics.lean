import UniquePathSemantics

namespace HansonToft

def AtMostOneTrue (n : Nat) (inputs : Nat → Bool) : Prop :=
  ∀ i j, i < n → j < n →
    inputs i = true → inputs j = true → i = j

def SequentialCounter (n : Nat)
    (inputs seen : Nat → Bool) : Prop :=
  (inputs 0 = true → seen 0 = true) ∧
  (∀ j, j + 2 < n →
    (seen j = true → seen (j + 1) = true) ∧
    (inputs (j + 1) = true → seen j = false) ∧
    (inputs (j + 1) = true → seen (j + 1) = true)) ∧
  (inputs (n - 1) = true → seen (n - 2) = false)

theorem sequential_seen_forward {n : Nat}
    (inputs seen : Nat → Bool)
    (hCounter : SequentialCounter n inputs seen) :
    ∀ j, j + 1 < n →
      ∀ i, i ≤ j → seen i = true → seen j = true := by
  intro j
  induction j with
  | zero =>
      intro hj i hij hSeen
      have hi : i = 0 := by omega
      simpa only [hi] using hSeen
  | succ j ih =>
      intro hj i hij hSeen
      by_cases heq : i = j + 1
      · simpa only [heq] using hSeen
      · have hPrevious := ih (by omega) i (by omega) hSeen
        exact (hCounter.2.1 j (by omega)).1 hPrevious

theorem sequential_counter_no_ordered_pair {n : Nat}
    (inputs seen : Nat → Bool)
    (hCounter : SequentialCounter n inputs seen)
    (i j : Nat) (hij : i < j) (hj : j < n)
    (hiTrue : inputs i = true)
    (hjTrue : inputs j = true) :
    False := by
  have hSeenI : seen i = true := by
    cases i with
    | zero =>
        exact hCounter.1 hiTrue
    | succ i =>
        exact (hCounter.2.1 i (by omega)).2.2 hiTrue
  have hBefore : seen (j - 1) = true :=
    sequential_seen_forward inputs seen hCounter
      (j - 1) (by omega) i (by omega) hSeenI
  have hFalse : seen (j - 1) = false := by
    by_cases hLast : j = n - 1
    · have hLastInput : inputs (n - 1) = true := by
        simpa only [hLast] using hjTrue
      have hIndex : j - 1 = n - 2 := by omega
      simpa only [hIndex] using hCounter.2.2 hLastInput
    · have hIndex : j - 1 + 1 = j := by omega
      apply (hCounter.2.1 (j - 1) (by omega)).2.1
      simpa only [hIndex] using hjTrue
  have hBad : true = false := hBefore.symm.trans hFalse
  cases hBad

theorem sequential_counter_sound {n : Nat}
    (inputs seen : Nat → Bool)
    (hCounter : SequentialCounter n inputs seen) :
    AtMostOneTrue n inputs := by
  intro i j hi hj hiTrue hjTrue
  by_cases hij : i < j
  · exact False.elim
      (sequential_counter_no_ordered_pair
        inputs seen hCounter i j hij hj hiTrue hjTrue)
  · by_cases hji : j < i
    · exact False.elim
        (sequential_counter_no_ordered_pair
          inputs seen hCounter j i hji hi hjTrue hiTrue)
    · omega

noncomputable def counterSeen
    (inputs : Nat → Bool) (j : Nat) : Bool := by
  classical
  exact decide (∃ i, i ≤ j ∧ inputs i = true)

theorem counterSeen_true_iff (inputs : Nat → Bool) (j : Nat) :
    counterSeen inputs j = true ↔
      ∃ i, i ≤ j ∧ inputs i = true := by
  classical
  simp [counterSeen]

theorem counterSeen_false_iff (inputs : Nat → Bool) (j : Nat) :
    counterSeen inputs j = false ↔
      ¬ ∃ i, i ≤ j ∧ inputs i = true := by
  classical
  simp [counterSeen]

theorem sequential_counter_complete {n : Nat}
    (hn : 2 ≤ n) (inputs : Nat → Bool)
    (hAtMost : AtMostOneTrue n inputs) :
    SequentialCounter n inputs (counterSeen inputs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hInput
    apply (counterSeen_true_iff inputs 0).mpr
    exact ⟨0, Nat.le_refl 0, hInput⟩
  · intro j hj
    refine ⟨?_, ?_, ?_⟩
    · intro hSeen
      obtain ⟨i, hi, hInput⟩ :=
        (counterSeen_true_iff inputs j).mp hSeen
      apply (counterSeen_true_iff inputs (j + 1)).mpr
      exact ⟨i, by omega, hInput⟩
    · intro hCurrent
      apply (counterSeen_false_iff inputs j).mpr
      rintro ⟨i, hi, hInput⟩
      have hEqual := hAtMost i (j + 1)
        (by omega) (by omega) hInput hCurrent
      omega
    · intro hCurrent
      apply (counterSeen_true_iff inputs (j + 1)).mpr
      exact ⟨j + 1, Nat.le_refl _, hCurrent⟩
  · intro hLast
    apply (counterSeen_false_iff inputs (n - 2)).mpr
    rintro ⟨i, hi, hInput⟩
    have hEqual := hAtMost i (n - 1)
      (by omega) (by omega) hInput hLast
    omega

theorem sequential_counter_exists_iff {n : Nat}
    (hn : 2 ≤ n) (inputs : Nat → Bool) :
    (∃ seen, SequentialCounter n inputs seen) ↔
      AtMostOneTrue n inputs := by
  constructor
  · rintro ⟨seen, hCounter⟩
    exact sequential_counter_sound inputs seen hCounter
  · intro hAtMost
    exact ⟨counterSeen inputs,
      sequential_counter_complete hn inputs hAtMost⟩

theorem counter_positive_clause
    (assignment : Nat → Bool) (x y : Nat) :
    HoldsClause assignment [(x, false), (y, true)] ↔
      (assignment x = true → assignment y = true) := by
  rw [holdsClause_two]
  cases hx : assignment x <;>
    cases hy : assignment y <;> simp_all

theorem counter_negative_clause
    (assignment : Nat → Bool) (x y : Nat) :
    HoldsClause assignment [(x, false), (y, false)] ↔
      (assignment x = true → assignment y = false) := by
  rw [holdsClause_two]
  cases hx : assignment x <;>
    cases hy : assignment y <;> simp_all

theorem sequential_counter_clause_semantics
    (assignment : Nat → Bool)
    (inputs aux : Nat → Nat) (n : Nat) :
    (HoldsClause assignment
        [(inputs 0, false), (aux 0, true)] ∧
      (∀ j, j + 2 < n →
        HoldsClause assignment
          [(aux j, false), (aux (j + 1), true)] ∧
        HoldsClause assignment
          [(inputs (j + 1), false), (aux j, false)] ∧
        HoldsClause assignment
          [(inputs (j + 1), false), (aux (j + 1), true)]) ∧
      HoldsClause assignment
        [(inputs (n - 1), false), (aux (n - 2), false)]) ↔
    SequentialCounter n
      (fun j => assignment (inputs j))
      (fun j => assignment (aux j)) := by
  unfold SequentialCounter
  simp only [counter_positive_clause, counter_negative_clause]

#print axioms sequential_counter_sound
#print axioms sequential_counter_complete
#print axioms sequential_counter_clause_semantics

end HansonToft
