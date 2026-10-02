import Mathlib
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.ecalPt_im_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

noncomputable section

/-- Pointwise upper bound for the "growth coefficient" `C'_j = c.re·λ²ψ_j/D_j`
of the imaginary-part recurrence, using `ψ_j/D_j ≤ 1 + 1/D_j`. -/
def oidCg (lam cr : ℝ) (x y : ℕ → ℝ) (j : ℕ) : ℝ :=
  cr * (lam ^ 2 + lam ^ 2 / ocDen lam x y j)

theorem oidCg_nonneg (lam cr : ℝ) (x y : ℕ → ℝ) (hcr : 0 ≤ cr) (j : ℕ)
    (hD : 0 < ocDen lam x y j) : 0 ≤ oidCg lam cr x y j := by
  rw [oidCg]
  apply mul_nonneg hcr
  have h1 : 0 ≤ lam ^ 2 := sq_nonneg lam
  have h2 : 0 ≤ lam ^ 2 / ocDen lam x y j := div_nonneg h1 hD.le
  linarith

/-- `‖sin (λu)‖² = sin²(λ Re u) + sinh²(λ Im u)`. -/
theorem normSq_sin_eq_ocDen (lam : ℝ) (u : ℂ) :
    ‖Complex.sin ((lam : ℂ) * u)‖ ^ 2
      = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, inbound_sin_re, inbound_sin_im]
  have h1 : Real.cosh (lam * u.im) ^ 2 = Real.sinh (lam * u.im) ^ 2 + 1 := Real.cosh_sq _
  have h2 : Real.sin (lam * u.re) ^ 2 + Real.cos (lam * u.re) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  nlinarith [h1, h2]

end

end Work.PARIMPL2.Direct
