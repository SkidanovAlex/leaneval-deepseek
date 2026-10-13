import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Omega

/-- The set where a polynomial does not vanish is the complement of its zero set; the zero set
is in `Ω n (totalDegree)` by `hyp`, and taking complements raises the format index by one. -/
theorem omega_poly_ne (S : WilkiesDesign.SOMin) (n : ℕ) (P : MvPolynomial (Fin n) ℝ) : {x : Fin n → ℝ | P.eval x ≠ 0} ∈ S.Ω (n + 1) P.totalDegree n := by
  have h := S.compl (S.hyp n P)
  convert h using 1
  ext x
  simp only [Set.mem_compl_iff, ne_eq, Set.mem_ofPred_eq]

end Work.WilkiesH.Omega
