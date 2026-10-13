import Mathlib
import Submission.Work.WilG4c.FDerivDirDefs

namespace Work.WilG4c

theorem BadGraphSetMem (S : WilkiesDesign.SOMin) (N : ℕ) :
    ∃ K : ℕ, ∀ (A : ℕ) (b : Polynomial ℕ) (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
      Work.WilG4c.epsFDerivSet N φ ∈ S.Ω A (b.eval D) (N + N) →
      Work.WilG4c.badGraphSet N φ ∈
        S.Ω (A + K) ((b + Polynomial.C 1).eval D) (N + 1) := by
  refine ⟨N + N + 3, fun A b D φ hφ => ?_⟩
  -- 1. project the derivative-relation set along the coefficient block:
  --    the differentiability locus of `φ`.
  have hproj : Work.WilG0.projLastIter N N (epsFDerivSet N φ) ∈
      S.Ω (A + N + N) (b.eval D) N :=
    Work.WilG0.projLastIter_mem S N N A (b.eval D) (epsFDerivSet N φ) hφ
  -- 2. complement: the *non*-differentiability locus.
  have hcompl : (Work.WilG0.projLastIter N N (epsFDerivSet N φ))ᶜ ∈
      S.Ω (A + N + N + 1) (b.eval D) N :=
    Work.WilG1.Omega.compl_mem (S := S) hproj
  -- 3. pull back along `Fin.init` (dummy last coordinate).
  have hprod : {z : Fin (N + 1) → ℝ | Fin.init z ∈
      (Work.WilG0.projLastIter N N (epsFDerivSet N φ))ᶜ} ∈
      S.Ω ((A + N + N + 1) + 1) (b.eval D) (N + 1) :=
    Work.WilG1.Omega.prodRight_mem (S := S) hcompl
  -- 4. the coordinate hyperplane `x (last N) = 0`.
  have hhyp : {x : Fin (N + 1) → ℝ | x (Fin.last N) = 0} ∈
      S.Ω (N + 1) ((Polynomial.C 1 : Polynomial ℕ).eval D) (N + 1) := by
    have h := Work.WilG1.Omega.hyp_mem (S := S) (n := N + 1) D
      (MvPolynomial.X (Fin.last N) : MvPolynomial (Fin (N + 1)) ℝ)
    have hset : {x : Fin (N + 1) → ℝ |
          MvPolynomial.eval x (MvPolynomial.X (Fin.last N) : MvPolynomial (Fin (N + 1)) ℝ) = 0}
        = {x : Fin (N + 1) → ℝ | x (Fin.last N) = 0} := by
      ext x
      simp [MvPolynomial.eval_X]
    rw [hset] at h
    simpa [MvPolynomial.totalDegree_X] using h
  have hhyp' : {x : Fin (N + 1) → ℝ | x (Fin.last N) = 0} ∈
      S.Ω ((A + N + N + 1) + 1) ((Polynomial.C 1 : Polynomial ℕ).eval D) (N + 1) :=
    Work.WilG1.Omega.mono (S := S) hhyp (by omega) le_rfl
  have hint := Work.WilG1.Omega.inter₂ (S := S) hprod hhyp'
  have hfmt : max ((A + N + N + 1) + 1) ((A + N + N + 1) + 1) + 1 = A + (N + N + 3) := by
    rw [max_self]; omega
  rw [hfmt] at hint
  rw [badGraphSet_eq N φ]
  exact hint

end Work.WilG4c
