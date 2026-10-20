import RankedPaths

namespace HansonToft

theorem ranksFrom_expand_above {α : Type}
    (color lifted : α → Nat) (p : List α) :
    ∀ s c, c ≤ s →
      RanksFrom color s p →
      (∀ v ∈ p, lifted v = expandRank c (color v)) →
      RanksFrom lifted (s + 1) p := by
  induction p with
  | nil =>
      intro s c hc hr hl
      trivial
  | cons v rest ih =>
      intro s c hc hr hl
      refine ⟨?_, ?_⟩
      · rw [hl v (by simp), hr.1]
        unfold expandRank
        split <;> omega
      · have ht := ih (s + 1) c (by omega) hr.2
          (fun w hw => hl w (by simp [hw]))
        simpa [Nat.add_assoc] using ht

theorem ranksFrom_insert_missing {α : Type}
    (color lifted : α → Nat)
    (front : List α) :
    ∀ (rest : List α) (z : α) (s c : Nat),
      c = s + front.length →
      RanksFrom color s (front ++ rest) →
      lifted z = c →
      (∀ v ∈ front ++ rest,
        lifted v = expandRank c (color v)) →
      RanksFrom lifted s (front ++ z :: rest) := by
  induction front with
  | nil =>
      intro rest z s c hc hr hz hl
      have hcs : c = s := by simpa using hc
      subst c
      refine ⟨hz, ?_⟩
      exact ranksFrom_expand_above color lifted rest s s
        (Nat.le_refl s) hr hl
  | cons v front ih =>
      intro rest z s c hc hr hz hl
      have hc' : c = (s + 1) + front.length := by
        simp only [List.length_cons] at hc
        omega
      have hsc : s < c := by
        simp only [List.length_cons] at hc
        omega
      refine ⟨?_, ?_⟩
      · rw [hl v (by simp), hr.1]
        unfold expandRank
        simp [hsc]
      · exact ih rest z (s + 1) c hc' hr.2 hz
          (fun w hw => hl w (by simp [hw]))

#print axioms ranksFrom_expand_above
#print axioms ranksFrom_insert_missing

end HansonToft
