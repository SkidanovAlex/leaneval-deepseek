import Mathlib
import Submission.Work.WilG4a.CD.Defs

namespace Work.WilG4a.CD

open WilkiesDesign

/-- `inflCell p = {(z, δ, y) ∈ ℝ^{p+3} | (y - z(last))² < δ²}` is the positivity set of the
degree-`2` polynomial `P = X_δ² - (X_y - X_z(last))²`.  Hence `Work.WilG1.Calc.pos_mem`
yields it as an `Ω`-set of format `(p+3)+2 = p+5` and degree `P.totalDegree + 2 ≤ 4`. -/
theorem inflCell_mem (S : WilkiesDesign.SOMin) (p D : ℕ) :
    inflCell p ∈ S.Ω (p + 5) ((Polynomial.C 4).eval D) (p + 3) := by
  -- The defining polynomial of `inflCell p`.
  set P : MvPolynomial (Fin (p + 3)) ℝ :=
    MvPolynomial.X (cdl p) ^ 2 -
      (MvPolynomial.X (cyl p) - MvPolynomial.X (czt p)) ^ 2 with hP
  -- Its total degree is at most `2`.
  have htd : P.totalDegree ≤ 2 := by
    rw [hP]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · simp
    · have h1 : (MvPolynomial.X (cyl p) - MvPolynomial.X (czt p) :
          MvPolynomial (Fin (p + 3)) ℝ).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        rw [max_le_iff]
        exact ⟨by simp, by simp⟩
      have h2 := MvPolynomial.totalDegree_pow
        (MvPolynomial.X (cyl p) - MvPolynomial.X (czt p) : MvPolynomial (Fin (p + 3)) ℝ) 2
      omega
  -- `pos_mem` gives the positivity set of `P` as an `Ω`-set of format `(p+3)+2` and
  -- degree `P.totalDegree + 2`.
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 3) D P
  -- The positivity set of `P` is exactly `inflCell p`.
  have hset : {x : Fin (p + 3) → ℝ | 0 < MvPolynomial.eval x P} = inflCell p := by
    ext x
    simp only [hP, Set.mem_ofPred_eq, inflCell, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, sub_pos]
  rw [hset] at h
  -- Weaken the format `(p+3)+2 = p+5` and the degree `P.totalDegree + 2 ≤ 4`.
  refine Work.WilG1.Omega.mono h (by omega) ?_
  simp only [Polynomial.eval_C]
  omega

end Work.WilG4a.CD
