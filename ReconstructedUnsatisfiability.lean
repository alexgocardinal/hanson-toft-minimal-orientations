import ExactCNFReconstruction

namespace HansonToft

def archivedFormula (s : Fin 6) : Std.Sat.CNF Nat :=
  match s.val with
  | 0 => CertificateK4.formula
  | 1 => CertificateK5.formula
  | 2 => CertificateK6.formula
  | 3 => CertificateK7.formula
  | 4 => CertificateK8.formula
  | _ => CertificateK9.formula

theorem archivedFormula_unsat (s : Fin 6) :
    (archivedFormula s).Unsat := by
  have hCases :
      s.val = 0 ∨ s.val = 1 ∨ s.val = 2 ∨
      s.val = 3 ∨ s.val = 4 ∨ s.val = 5 := by
    have h := s.isLt
    omega
  rcases hCases with h | h | h | h | h | h
  · simpa only [archivedFormula, h] using CertificateK4.formula_unsat
  · simpa only [archivedFormula, h] using CertificateK5.formula_unsat
  · simpa only [archivedFormula, h] using CertificateK6.formula_unsat
  · simpa only [archivedFormula, h] using CertificateK7.formula_unsat
  · simpa only [archivedFormula, h] using CertificateK8.formula_unsat
  · simpa only [archivedFormula, h] using CertificateK9.formula_unsat

theorem holdsClause_literals_iff
    (assignment : Nat → Bool)
    (clause : Std.Sat.CNF.Clause Nat) :
    HoldsClause assignment clause.literals ↔
      Std.Sat.CNF.Clause.Sat assignment clause := by
  rw [holdsClause_iff, Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  rfl

theorem unsat_excludes_literal_assignment
    (formula : Std.Sat.CNF Nat)
    (hUnsat : formula.Unsat)
    (assignment : Nat → Bool) :
    ¬ (∀ clause ∈ formula.clauses.toList.map
        (fun c => c.literals),
      HoldsClause assignment clause) := by
  intro hAll
  have hSat : Std.Sat.CNF.Sat assignment formula := by
    apply Std.Sat.CNF.sat_of_all_mem_sat
    intro clause hMem
    apply (holdsClause_literals_iff assignment clause).mp
    apply hAll clause.literals
    apply List.mem_map.mpr
    refine ⟨clause, ?_, rfl⟩
    have hArray : clause ∈ formula.clauses := hMem
    simpa using hArray
  exact (Std.Sat.CNF.unsat_iff_not_sat.mp hUnsat) assignment hSat

theorem reconstructed_encoding_has_no_assignment
    (s : Fin 6) (assignment : Nat → Bool) :
    ¬ (∀ clause ∈
        (reconstructEncoding (s.val + 4)).clauses.toList,
      HoldsClause assignment clause) := by
  intro hAll
  rw [reconstruction_matches_archives s] at hAll
  change (∀ clause ∈ (archivedFormula s).clauses.toList.map
      (fun c => c.literals),
    HoldsClause assignment clause) at hAll
  exact unsat_excludes_literal_assignment
    (archivedFormula s) (archivedFormula_unsat s) assignment hAll

#print axioms reconstructed_encoding_has_no_assignment

end HansonToft
