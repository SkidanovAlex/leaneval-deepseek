import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open Complex

/-- The real Fréchet derivative of an antipolynomial `z ↦ P(z̄)`: it is the composition of
`conj` with (real scalar restriction of) multiplication by `P'(z̄)`. -/
private lemma fderiv_antipoly (P : Polynomial ℂ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => P.eval (star z)) z
      = (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval (star z)))
          ∘SL (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := by
  have hstar_eq : (star : ℂ → ℂ) = ⇑(Complex.conjCLE) := by
    ext x; rw [Complex.star_def]; rfl
  have hA : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => P.eval w)
      (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval (star z)))) (star z) :=
    (P.hasFDerivAt (star z)).restrictScalars ℝ
  have hconj : HasFDerivAt (𝕜 := ℝ) (star : ℂ → ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    rw [hstar_eq]; exact Complex.conjCLE.hasFDerivAt
  have hfd : fderiv ℝ ((fun w : ℂ => P.eval w) ∘ star) z
      = (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval (star z)))
          ∘SL (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := (hA.comp z hconj).fderiv
  exact hfd

/-- The Wirtinger derivative `∂/∂z` of an antipolynomial vanishes: antipolynomials are
antiholomorphic. -/
private lemma dz_antipoly (P : Polynomial ℂ) (z : ℂ) :
    Work.MRMT.dz (fun z : ℂ => P.eval (star z)) z = 0 := by
  have hfd : fderiv ℝ (fun z : ℂ => P.eval (star z)) z
      = (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval (star z)))
          ∘SL (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := fderiv_antipoly P z
  have h1 : fderiv ℝ (fun z : ℂ => P.eval (star z)) z 1 = P.derivative.eval (star z) := by
    rw [hfd]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : fderiv ℝ (fun z : ℂ => P.eval (star z)) z Complex.I
      = - Complex.I * P.derivative.eval (star z) := by
    rw [hfd]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  rw [Work.MRMT.dz, h1, h2]
  have h : Complex.I * (-Complex.I * P.derivative.eval (star z)) = P.derivative.eval (star z) := by
    rw [neg_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring
  rw [h]; ring

/-- The Wirtinger derivative `∂/∂z̄` of the antipolynomial `z ↦ P(z̄)` is `P'(z̄)`. -/
private lemma dzbar_antipoly (P : Polynomial ℂ) (z : ℂ) :
    Work.MRMT.dzbar (fun z : ℂ => P.eval (star z)) z = P.derivative.eval (star z) := by
  have hfd : fderiv ℝ (fun z : ℂ => P.eval (star z)) z
      = (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval (star z)))
          ∘SL (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := fderiv_antipoly P z
  have h1 : fderiv ℝ (fun z : ℂ => P.eval (star z)) z 1 = P.derivative.eval (star z) := by
    rw [hfd]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : fderiv ℝ (fun z : ℂ => P.eval (star z)) z Complex.I
      = - Complex.I * P.derivative.eval (star z) := by
    rw [hfd]; simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  rw [Work.MRMT.dzbar, h1, h2]
  have h : Complex.I * (-Complex.I * P.derivative.eval (star z)) = P.derivative.eval (star z) := by
    rw [neg_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring
  rw [h]; ring

theorem antipoly_wirtinger {q : ℂ → ℂ} {P : Polynomial ℂ}
    (hP : ∀ z : ℂ, q z = P.eval (star z)) :
    ContDiff ℝ 1 q ∧ (∀ z : ℂ, Work.MRMT.dz q z = 0) ∧
      (∀ z : ℂ, Work.MRMT.dzbar q z = P.derivative.eval (star z)) := by
  have hq : q = fun z => P.eval (star z) := funext hP
  have hstar_eq : (star : ℂ → ℂ) = ⇑(Complex.conjCLE) := by
    ext x; rw [Complex.star_def]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hq]
    have hpe : ContDiff ℝ 1 (fun w : ℂ => P.eval w) := by
      have h : ContDiff ℝ 1 (fun x : ℂ => (Polynomial.aeval x) P) :=
        (Polynomial.contDiff_aeval P (1 : WithTop ℕ∞)).restrict_scalars ℝ
      rw [show (fun x : ℂ => (Polynomial.aeval x) P) = (fun w : ℂ => P.eval w) from by
        funext x; simp [Polynomial.aeval_def]] at h
      exact h
    have hcj : ContDiff ℝ 1 (star : ℂ → ℂ) := by
      rw [hstar_eq]
      exact Complex.conjCLE.contDiff (n := (1 : WithTop ℕ∞))
    exact hpe.comp hcj
  · intro z; rw [hq]; exact dz_antipoly P z
  · intro z; rw [hq]; exact dzbar_antipoly P z

end Work.FBif
