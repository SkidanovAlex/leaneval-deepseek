import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonestBddOfSecondSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

open MeasureTheory

/-- **Integrability of the angular slice of `Ψ` against `sinθcos²θ`.**

The hypothesis `HkMem α k (∂_θ²Ψ)` (for any `k ≥ 0`) contains, as the `D_z^0`-summand of its
integrand, the integrability of `θ ↦ (∂_θ²Ψ z θ · w z / sin(2θ)^{η/2})²`, i.e. of
`θ ↦ (∂_θ²Ψ z θ)² · sin(2θ)^{-η}` up to the constant `w z ²`.  Since `η > -1`, the weight
`sin(2θ)^{-η}` forces the slice `θ ↦ Ψ z θ` of the `C^∞`-function `Ψ` to be *bounded* on
`(0, π/2)` (Cauchy–Schwarz against `sin(2θ)^{η}` plus the fundamental theorem of calculus from
the interior point `π/4` — nothing is known at the endpoints), and `sinθcos²θ` is bounded by
`1`; this is exactly `HonestBddOfSecondSq`, whose last conjunct is the claim. -/
theorem integrableOn_slice_mul_sinCos2 {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  intro z hz
  -- `∂_θ²Ψ` is again `C^∞` on the open quadrant
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hsm.pth.pth
  -- the `D_z^0`-summand of the `ℋ^k`-integrand of `∂_θ²Ψ` is integrable on the slice
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 0 (Work.Spaces.pthIter 2 Ψ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      ((Work.FTS.EllipticEst.SmoothOpen.aesm_slice_summand hsm2 0 hz).pow 2) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 Ψ) z θ 0 (Nat.zero_le k)
  -- divide by the constant `w z ² ≠ 0`: `(∂_θ²Ψ)² · sin(2θ)^{-η}` is integrable as well
  have hconv : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hwz : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    refine MeasureTheory.IntegrableOn.congr_fun (hslice.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · intro θ hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      show ((Work.Spaces.w z) ^ 2)⁻¹
          * (Work.Spaces.DzIter 0 (Work.Spaces.pthIter 2 Ψ) z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = Work.Spaces.pthIter 2 Ψ z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [Work.Spaces.DzIter_zero, Work.FTS.EllipticEst.sEta]
      rw [show (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
          = Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2)) by
        rw [div_eq_mul_inv, ← Real.rpow_neg hs0]]
      have hsq : (Real.sin (2 * θ) ^ (-(Work.Spaces.eta / 2))) ^ 2
          = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hs0]
        congr 1
        ring
      rw [mul_pow, mul_pow, hsq]
      rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
              ((Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))))
          = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) *
            ((Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) by ring,
        inv_mul_cancel₀ (pow_ne_zero 2 hwz), one_mul]
    · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- `θ ↦ ∂_θ²Ψ z θ` is literally the second derivative of the slice `θ ↦ Ψ z θ`
  have hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv (fun θ' : ℝ => Ψ z θ') t) θ ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hconv
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hz).of_le (by norm_num)
  exact (Work.FTS.EllipticEst.Honest.HonestBddOfSecondSq hf2 hint).2.2.2.2.2

end Work.FTS.PhiStar.Honesty.EllWeakAux
