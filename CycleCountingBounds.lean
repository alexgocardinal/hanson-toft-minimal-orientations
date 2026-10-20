import FullCriticality

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace HansonToft

def colorClassCount {α : Type} [DecidableEq α] : List α → Nat
  | [] => 0
  | a :: rest =>
      if a ∈ rest then colorClassCount rest
      else colorClassCount rest + 1

def twoColorIndicator {α : Type} [DecidableEq α]
    (a b c : α) : Nat :=
  if c = a ∨ c = b then 1 else 0

theorem seven_cycle_counting_bounds {α : Type} [DecidableEq α]
    (x0 x1 x2 x3 x4 x5 x6 : α)
    (hEdge0 : x0 ≠ x1)
    (hEdge1 : x1 ≠ x2)
    (hEdge2 : x2 ≠ x3)
    (hEdge3 : x3 ≠ x4)
    (hEdge4 : x4 ≠ x5)
    (hEdge5 : x5 ≠ x6)
    (hEdge6 : x6 ≠ x0)
    : (twoColorIndicator x0 x1 x3 + twoColorIndicator x1 x2 x4 + twoColorIndicator x2 x3 x5 + twoColorIndicator x3 x4 x6 + twoColorIndicator x4 x5 x0 + twoColorIndicator x5 x6 x1 + twoColorIndicator x6 x0 x2) ≤ 6 ∧
      colorClassCount [x0, x1, x2, x3, x4, x5, x6] + (twoColorIndicator x0 x1 x3 + twoColorIndicator x1 x2 x4 + twoColorIndicator x2 x3 x5 + twoColorIndicator x3 x4 x6 + twoColorIndicator x4 x5 x0 + twoColorIndicator x5 x6 x1 + twoColorIndicator x6 x0 x2) ≤ 9 := by
  by_cases h1_0 : x1 = x0
  · exact False.elim (hEdge0 (Eq.trans (rfl) (Eq.symm (h1_0))))
  · by_cases h2_0 : x2 = x0
    · by_cases h3_0 : x3 = x0
      · exact False.elim (hEdge2 (Eq.trans (h2_0) (Eq.symm (h3_0))))
      · by_cases h3_1 : x3 = x1
        · by_cases h4_0 : x4 = x0
          · by_cases h5_0 : x5 = x0
            · exact False.elim (hEdge4 (Eq.trans (h4_0) (Eq.symm (h5_0))))
            · by_cases h5_1 : x5 = x1
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                · by_cases h6_1 : x6 = x1
                  · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1]
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                · by_cases h6_1 : x6 = x1
                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h6_0, Ne.symm h6_0, h6_1]
                  · by_cases h6_5 : x6 = x5
                    · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_5, Ne.symm h6_5]
          · by_cases h4_1 : x4 = x1
            · exact False.elim (hEdge3 (Eq.trans (h3_1) (Eq.symm (h4_1))))
            · by_cases h5_0 : x5 = x0
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                · by_cases h6_1 : x6 = x1
                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1]
                  · by_cases h6_4 : x6 = x4
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4]
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4, Ne.symm h6_4]
              · by_cases h5_1 : x5 = x1
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                  · by_cases h6_1 : x6 = x1
                    · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                    · by_cases h6_4 : x6 = x4
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4]
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4, Ne.symm h6_4]
                · by_cases h5_4 : x5 = x4
                  · exact False.elim (hEdge4 (Eq.trans (rfl) (Eq.symm (h5_4))))
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_4 : x6 = x4
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4]
                        · by_cases h6_5 : x6 = x5
                          · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_4, Ne.symm h6_4, h6_5, Ne.symm h6_5]
        · by_cases h4_0 : x4 = x0
          · by_cases h5_0 : x5 = x0
            · exact False.elim (hEdge4 (Eq.trans (h4_0) (Eq.symm (h5_0))))
            · by_cases h5_1 : x5 = x1
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                · by_cases h6_1 : x6 = x1
                  · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                  · by_cases h6_3 : x6 = x3
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3]
              · by_cases h5_3 : x5 = x3
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                  · by_cases h6_1 : x6 = x1
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1]
                    · by_cases h6_3 : x6 = x3
                      · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3]
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                  · by_cases h6_1 : x6 = x1
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1]
                    · by_cases h6_3 : x6 = x3
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                      · by_cases h6_5 : x6 = x5
                        · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_5, Ne.symm h6_5]
          · by_cases h4_1 : x4 = x1
            · by_cases h5_0 : x5 = x0
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                · by_cases h6_1 : x6 = x1
                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1]
                  · by_cases h6_3 : x6 = x3
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3]
              · by_cases h5_1 : x5 = x1
                · exact False.elim (hEdge4 (Eq.trans (h4_1) (Eq.symm (h5_1))))
                · by_cases h5_3 : x5 = x3
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_3 : x6 = x3
                        · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3]
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_3 : x6 = x3
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                        · by_cases h6_5 : x6 = x5
                          · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_5, Ne.symm h6_5]
            · by_cases h4_3 : x4 = x3
              · exact False.elim (hEdge3 (Eq.trans (rfl) (Eq.symm (h4_3))))
              · by_cases h5_0 : x5 = x0
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                  · by_cases h6_1 : x6 = x1
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1]
                    · by_cases h6_3 : x6 = x3
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                      · by_cases h6_4 : x6 = x4
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4]
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                · by_cases h5_1 : x5 = x1
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                      · by_cases h6_3 : x6 = x3
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                        · by_cases h6_4 : x6 = x4
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                  · by_cases h5_3 : x5 = x3
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1]
                        · by_cases h6_3 : x6 = x3
                          · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                          · by_cases h6_4 : x6 = x4
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4]
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                    · by_cases h5_4 : x5 = x4
                      · exact False.elim (hEdge4 (Eq.trans (rfl) (Eq.symm (h5_4))))
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_3 : x6 = x3
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3]
                            · by_cases h6_4 : x6 = x4
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4]
                              · by_cases h6_5 : x6 = x5
                                · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4, h6_5, Ne.symm h6_5]
    · by_cases h2_1 : x2 = x1
      · exact False.elim (hEdge1 (Eq.trans (rfl) (Eq.symm (h2_1))))
      · by_cases h3_0 : x3 = x0
        · by_cases h4_0 : x4 = x0
          · exact False.elim (hEdge3 (Eq.trans (h3_0) (Eq.symm (h4_0))))
          · by_cases h4_1 : x4 = x1
            · by_cases h5_0 : x5 = x0
              · by_cases h6_0 : x6 = x0
                · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                · by_cases h6_1 : x6 = x1
                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1]
                  · by_cases h6_2 : x6 = x2
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
              · by_cases h5_1 : x5 = x1
                · exact False.elim (hEdge4 (Eq.trans (h4_1) (Eq.symm (h5_1))))
                · by_cases h5_2 : x5 = x2
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_5 : x6 = x5
                          · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_5, Ne.symm h6_5]
            · by_cases h4_2 : x4 = x2
              · by_cases h5_0 : x5 = x0
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                  · by_cases h6_1 : x6 = x1
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1]
                    · by_cases h6_2 : x6 = x2
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                · by_cases h5_1 : x5 = x1
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                  · by_cases h5_2 : x5 = x2
                    · exact False.elim (hEdge4 (Eq.trans (h4_2) (Eq.symm (h5_2))))
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1]
                        · by_cases h6_2 : x6 = x2
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                          · by_cases h6_5 : x6 = x5
                            · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_5, Ne.symm h6_5]
              · by_cases h5_0 : x5 = x0
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                  · by_cases h6_1 : x6 = x1
                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1]
                    · by_cases h6_2 : x6 = x2
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                      · by_cases h6_4 : x6 = x4
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                · by_cases h5_1 : x5 = x1
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_4 : x6 = x4
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                  · by_cases h5_2 : x5 = x2
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                        · by_cases h6_2 : x6 = x2
                          · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                          · by_cases h6_4 : x6 = x4
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                    · by_cases h5_4 : x5 = x4
                      · exact False.elim (hEdge4 (Eq.trans (rfl) (Eq.symm (h5_4))))
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_4 : x6 = x4
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                              · by_cases h6_5 : x6 = x5
                                · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4, h6_5, Ne.symm h6_5]
        · by_cases h3_1 : x3 = x1
          · by_cases h4_0 : x4 = x0
            · by_cases h5_0 : x5 = x0
              · exact False.elim (hEdge4 (Eq.trans (h4_0) (Eq.symm (h5_0))))
              · by_cases h5_1 : x5 = x1
                · by_cases h6_0 : x6 = x0
                  · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                  · by_cases h6_1 : x6 = x1
                    · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                    · by_cases h6_2 : x6 = x2
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                · by_cases h5_2 : x5 = x2
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_5 : x6 = x5
                          · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_5, Ne.symm h6_5]
            · by_cases h4_1 : x4 = x1
              · exact False.elim (hEdge3 (Eq.trans (h3_1) (Eq.symm (h4_1))))
              · by_cases h4_2 : x4 = x2
                · by_cases h5_0 : x5 = x0
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                  · by_cases h5_1 : x5 = x1
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                        · by_cases h6_2 : x6 = x2
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2]
                    · by_cases h5_2 : x5 = x2
                      · exact False.elim (hEdge4 (Eq.trans (h4_2) (Eq.symm (h5_2))))
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_5 : x6 = x5
                              · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_5, Ne.symm h6_5]
                · by_cases h5_0 : x5 = x0
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_4 : x6 = x4
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                  · by_cases h5_1 : x5 = x1
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                        · by_cases h6_2 : x6 = x2
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                          · by_cases h6_4 : x6 = x4
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                    · by_cases h5_2 : x5 = x2
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                            · by_cases h6_4 : x6 = x4
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4]
                      · by_cases h5_4 : x5 = x4
                        · exact False.elim (hEdge4 (Eq.trans (rfl) (Eq.symm (h5_4))))
                        · by_cases h6_0 : x6 = x0
                          · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                          · by_cases h6_1 : x6 = x1
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1]
                            · by_cases h6_2 : x6 = x2
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                              · by_cases h6_4 : x6 = x4
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4]
                                · by_cases h6_5 : x6 = x5
                                  · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_4, Ne.symm h6_4, h6_5, Ne.symm h6_5]
          · by_cases h3_2 : x3 = x2
            · exact False.elim (hEdge2 (Eq.trans (rfl) (Eq.symm (h3_2))))
            · by_cases h4_0 : x4 = x0
              · by_cases h5_0 : x5 = x0
                · exact False.elim (hEdge4 (Eq.trans (h4_0) (Eq.symm (h5_0))))
                · by_cases h5_1 : x5 = x1
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                    · by_cases h6_1 : x6 = x1
                      · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_3 : x6 = x3
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                  · by_cases h5_2 : x5 = x2
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                      · by_cases h6_1 : x6 = x1
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                        · by_cases h6_2 : x6 = x2
                          · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                          · by_cases h6_3 : x6 = x3
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                    · by_cases h5_3 : x5 = x3
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_3 : x6 = x3
                              · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_3 : x6 = x3
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                              · by_cases h6_5 : x6 = x5
                                · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_5, Ne.symm h6_5]
              · by_cases h4_1 : x4 = x1
                · by_cases h5_0 : x5 = x0
                  · by_cases h6_0 : x6 = x0
                    · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                    · by_cases h6_1 : x6 = x1
                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1]
                      · by_cases h6_2 : x6 = x2
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                        · by_cases h6_3 : x6 = x3
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                  · by_cases h5_1 : x5 = x1
                    · exact False.elim (hEdge4 (Eq.trans (h4_1) (Eq.symm (h5_1))))
                    · by_cases h5_2 : x5 = x2
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                            · by_cases h6_3 : x6 = x3
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                      · by_cases h5_3 : x5 = x3
                        · by_cases h6_0 : x6 = x0
                          · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                          · by_cases h6_1 : x6 = x1
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1]
                            · by_cases h6_2 : x6 = x2
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                              · by_cases h6_3 : x6 = x3
                                · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                        · by_cases h6_0 : x6 = x0
                          · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                          · by_cases h6_1 : x6 = x1
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1]
                            · by_cases h6_2 : x6 = x2
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                              · by_cases h6_3 : x6 = x3
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                                · by_cases h6_5 : x6 = x5
                                  · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_5, Ne.symm h6_5]
                · by_cases h4_2 : x4 = x2
                  · by_cases h5_0 : x5 = x0
                    · by_cases h6_0 : x6 = x0
                      · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                      · by_cases h6_1 : x6 = x1
                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1]
                        · by_cases h6_2 : x6 = x2
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                          · by_cases h6_3 : x6 = x3
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                    · by_cases h5_1 : x5 = x1
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                        · by_cases h6_1 : x6 = x1
                          · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_3 : x6 = x3
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                      · by_cases h5_2 : x5 = x2
                        · exact False.elim (hEdge4 (Eq.trans (h4_2) (Eq.symm (h5_2))))
                        · by_cases h5_3 : x5 = x3
                          · by_cases h6_0 : x6 = x0
                            · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                            · by_cases h6_1 : x6 = x1
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1]
                              · by_cases h6_2 : x6 = x2
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                                · by_cases h6_3 : x6 = x3
                                  · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3]
                          · by_cases h6_0 : x6 = x0
                            · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                            · by_cases h6_1 : x6 = x1
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1]
                              · by_cases h6_2 : x6 = x2
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                                · by_cases h6_3 : x6 = x3
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                                  · by_cases h6_5 : x6 = x5
                                    · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_5, Ne.symm h6_5]
                  · by_cases h4_3 : x4 = x3
                    · exact False.elim (hEdge3 (Eq.trans (rfl) (Eq.symm (h4_3))))
                    · by_cases h5_0 : x5 = x0
                      · by_cases h6_0 : x6 = x0
                        · exact False.elim (hEdge5 (Eq.trans (h5_0) (Eq.symm (h6_0))))
                        · by_cases h6_1 : x6 = x1
                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1]
                          · by_cases h6_2 : x6 = x2
                            · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                            · by_cases h6_3 : x6 = x3
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                              · by_cases h6_4 : x6 = x4
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4]
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                      · by_cases h5_1 : x5 = x1
                        · by_cases h6_0 : x6 = x0
                          · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                          · by_cases h6_1 : x6 = x1
                            · exact False.elim (hEdge5 (Eq.trans (h5_1) (Eq.symm (h6_1))))
                            · by_cases h6_2 : x6 = x2
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                              · by_cases h6_3 : x6 = x3
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                                · by_cases h6_4 : x6 = x4
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4]
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                        · by_cases h5_2 : x5 = x2
                          · by_cases h6_0 : x6 = x0
                            · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                            · by_cases h6_1 : x6 = x1
                              · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1]
                              · by_cases h6_2 : x6 = x2
                                · exact False.elim (hEdge5 (Eq.trans (h5_2) (Eq.symm (h6_2))))
                                · by_cases h6_3 : x6 = x3
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                                  · by_cases h6_4 : x6 = x4
                                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4]
                                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                          · by_cases h5_3 : x5 = x3
                            · by_cases h6_0 : x6 = x0
                              · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                              · by_cases h6_1 : x6 = x1
                                · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1]
                                · by_cases h6_2 : x6 = x2
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                                  · by_cases h6_3 : x6 = x3
                                    · exact False.elim (hEdge5 (Eq.trans (h5_3) (Eq.symm (h6_3))))
                                    · by_cases h6_4 : x6 = x4
                                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4]
                                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4]
                            · by_cases h5_4 : x5 = x4
                              · exact False.elim (hEdge4 (Eq.trans (rfl) (Eq.symm (h5_4))))
                              · by_cases h6_0 : x6 = x0
                                · exact False.elim (hEdge6 (Eq.trans (h6_0) (Eq.symm (rfl))))
                                · by_cases h6_1 : x6 = x1
                                  · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1]
                                  · by_cases h6_2 : x6 = x2
                                    · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2]
                                    · by_cases h6_3 : x6 = x3
                                      · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3]
                                      · by_cases h6_4 : x6 = x4
                                        · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4]
                                        · by_cases h6_5 : x6 = x5
                                          · exact False.elim (hEdge5 (Eq.trans (rfl) (Eq.symm (h6_5))))
                                          · simp [colorClassCount, twoColorIndicator, h1_0, Ne.symm h1_0, h2_0, Ne.symm h2_0, h2_1, Ne.symm h2_1, h3_0, Ne.symm h3_0, h3_1, Ne.symm h3_1, h3_2, Ne.symm h3_2, h4_0, Ne.symm h4_0, h4_1, Ne.symm h4_1, h4_2, Ne.symm h4_2, h4_3, Ne.symm h4_3, h5_0, Ne.symm h5_0, h5_1, Ne.symm h5_1, h5_2, Ne.symm h5_2, h5_3, Ne.symm h5_3, h5_4, Ne.symm h5_4, h6_0, Ne.symm h6_0, h6_1, Ne.symm h6_1, h6_2, Ne.symm h6_2, h6_3, Ne.symm h6_3, h6_4, Ne.symm h6_4, h6_5, Ne.symm h6_5]

def cycleClassCount {α : Type} [DecidableEq α]
    (color : Fin 7 → α) : Nat :=
  colorClassCount [color 0, color 1, color 2, color 3,
    color 4, color 5, color 6]

def cycleTwoColorCount {α : Type} [DecidableEq α]
    (color : Fin 7 → α) : Nat :=
  twoColorIndicator (color 0) (color 1) (color 3) +
  twoColorIndicator (color 1) (color 2) (color 4) +
  twoColorIndicator (color 2) (color 3) (color 5) +
  twoColorIndicator (color 3) (color 4) (color 6) +
  twoColorIndicator (color 4) (color 5) (color 0) +
  twoColorIndicator (color 5) (color 6) (color 1) +
  twoColorIndicator (color 6) (color 0) (color 2)

theorem cycle_counting_bounds {α : Type} [DecidableEq α]
    (color : Fin 7 → α)
    (hCycle : ∀ i, color i ≠ color (cycleStep i 1)) :
    cycleTwoColorCount color ≤ 6 ∧
      cycleClassCount color + cycleTwoColorCount color ≤ 9 := by
  unfold cycleTwoColorCount cycleClassCount
  exact seven_cycle_counting_bounds
    (color 0) (color 1) (color 2) (color 3)
    (color 4) (color 5) (color 6)
    (hCycle 0) (hCycle 1) (hCycle 2) (hCycle 3)
    (hCycle 4) (hCycle 5) (hCycle 6)

#print axioms cycle_counting_bounds

end HansonToft
