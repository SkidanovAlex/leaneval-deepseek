import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux

/-!
# `Work.LinnikAreas.ownRepelNW.xiECofactorAuxP0`

Bound for the logarithm of the modulus of the "cofactor" product
`∏ᶠ u, (0 - u) ^ (divisor Ξ (closedBall 0 T)) u` attached to the entire completion `Ξ` of
the Riemann zeta function.

The generic form of the estimate is proved first
(`xiE_divisorProd_log_bound`): for *any* integer-valued divisor-like function `d` of finite
support which is nonnegative, vanishes outside the closed ball of radius `T`, and only
vanishes at points where `d` is nonzero, one has

`|log ‖∏ᶠ u, (0 - u) ^ d u‖| ≤ (∑ᶠ u, d u) * (log T + |log δ₀|)`,

provided every zero of `Ξ` has modulus at least `δ₀ > 0`.  The point is that every point of the
support of `d` is a zero of `Ξ` inside the ball, hence has modulus in `[δ₀, T]`, so that each
`|log ‖u‖|` is at most `log T + |log δ₀|`.

The final theorem `xiECofactorAuxP0` instantiates this with the actual ball divisor of `Ξ`,
using the elementary divisor API of `DhK.XiAux`.
-/

open scoped Classical BigOperators
open Filter Metric

namespace Work.LinnikAreas.ownRepelNW

/-- **Generic cofactor bound.**  Let `d : ℂ → ℤ` be an integer-valued function with finite
support, nonnegative on the ball of radius `T`, supported in `Metric.closedBall 0 T` and
nonzero only at zeros of `Ξ`, and suppose every zero of `Ξ` has modulus at least `δ₀ > 0`
with `T ≥ 1`.  Then

`|log ‖∏ᶠ u, (0 - u) ^ d u‖| ≤ (∑ᶠ u, (d u : ℝ)) * (log T + |log δ₀|)`. -/
theorem xiE_divisorProd_log_bound {T : ℝ} (hT : 1 ≤ T) (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → δ₀ ≤ ‖u‖)
    (d : ℂ → ℤ) (hdfin : (Function.support d).Finite) (hdnn : ∀ u : ℂ, 0 ≤ d u)
    (hdz : ∀ u : ℂ, d u ≠ 0 → Work.LinnikAreas.DhK.Xi u = 0)
    (hdout : ∀ u : ℂ, u ∉ Metric.closedBall (0 : ℂ) T → d u = 0) :
    |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ d u)‖| ≤
      (∑ᶠ u : ℂ, (d u : ℝ)) * (Real.log T + |Real.log δ₀|) := by
  classical
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  -- `d` is supported inside the closed ball of radius `T`
  have hsupp : Function.support d ⊆ Metric.closedBall (0 : ℂ) T := by
    intro u hu
    by_contra h
    exact (Function.mem_support.mp hu) (hdout u h)
  -- every point of the support is a zero of `Ξ`: its modulus is at least `δ₀ > 0` ...
  have hp : ∀ u ∈ hdfin.toFinset, 0 < ‖u‖ := by
    intro u hu
    have hdu : d u ≠ 0 := Function.mem_support.mp (by rw [← hdfin.coe_toFinset]; exact hu)
    have := hδ₀ u (hdz u hdu)
    linarith
  -- ... and at most `T`
  have hleT : ∀ u ∈ hdfin.toFinset, ‖u‖ ≤ T := by
    intro u hu
    have hmem : u ∈ Metric.closedBall (0 : ℂ) T :=
      hsupp (by rw [← hdfin.coe_toFinset]; exact hu)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
  -- rewrite the finitely supported product as a finite product over the support of `d`
  have hprod : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ d u)
      = ∏ u ∈ hdfin.toFinset, ((0 : ℂ) - u) ^ d u := by
    rw [finprod_eq_prod_of_mulSupport_subset]
    intro u hu
    rw [hdfin.coe_toFinset, Function.mem_support]
    intro hdu
    exact hu (by show ((0 : ℂ) - u) ^ d u = 1; rw [hdu, zpow_zero])
  -- same for the finitely supported sum
  have hsum : (∑ᶠ u : ℂ, (d u : ℝ)) = ∑ u ∈ hdfin.toFinset, (d u : ℝ) := by
    rw [finsum_eq_sum_of_support_subset]
    intro u hu
    rw [hdfin.coe_toFinset, Function.mem_support]
    intro hdu
    exact hu (by show ((d u : ℤ) : ℝ) = 0; rw [hdu]; norm_num)
  have hnorm_each : ∀ u : ℂ, ‖((0 : ℂ) - u) ^ d u‖ = ‖u‖ ^ d u := by
    intro u
    rw [norm_zpow, zero_sub, norm_neg]
  -- take logarithms of the modulus
  have hlog : Real.log ‖∏ u ∈ hdfin.toFinset, ((0 : ℂ) - u) ^ d u‖
      = ∑ u ∈ hdfin.toFinset, (d u : ℝ) * Real.log ‖u‖ := by
    rw [norm_prod]
    rw [Real.log_prod (fun u hu => by rw [hnorm_each]; exact zpow_ne_zero _ (ne_of_gt (hp u hu)))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hnorm_each, Real.log_zpow]
  -- each `|log ‖u‖|` is at most `log T + |log δ₀|`
  have hlogu : ∀ u ∈ hdfin.toFinset, |Real.log ‖u‖| ≤ Real.log T + |Real.log δ₀| := by
    intro u hu
    have hdu : d u ≠ 0 := Function.mem_support.mp (by rw [← hdfin.coe_toFinset]; exact hu)
    have hge : δ₀ ≤ ‖u‖ := hδ₀ u (hdz u hdu)
    have hle := hleT u hu
    rw [abs_le]
    constructor
    · have h1 : -(Real.log T + |Real.log δ₀|) ≤ Real.log δ₀ := by
        have := neg_abs_le (Real.log δ₀); linarith
      exact le_trans h1 (Real.log_le_log hδ₀pos hge)
    · exact le_trans (Real.log_le_log (hp u hu) hle) (le_add_of_nonneg_right (abs_nonneg _))
  have hbound : |∑ u ∈ hdfin.toFinset, (d u : ℝ) * Real.log ‖u‖|
      ≤ (∑ u ∈ hdfin.toFinset, (d u : ℝ)) * (Real.log T + |Real.log δ₀|) := by
    calc |∑ u ∈ hdfin.toFinset, (d u : ℝ) * Real.log ‖u‖|
        ≤ ∑ u ∈ hdfin.toFinset, |(d u : ℝ) * Real.log ‖u‖| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u ∈ hdfin.toFinset, (d u : ℝ) * |Real.log ‖u‖| := by
          apply Finset.sum_congr rfl
          intro u _
          rw [abs_mul, abs_of_nonneg (by exact_mod_cast hdnn u : (0 : ℝ) ≤ (d u : ℝ))]
      _ ≤ ∑ u ∈ hdfin.toFinset, (d u : ℝ) * (Real.log T + |Real.log δ₀|) := by
          apply Finset.sum_le_sum
          intro u hu
          exact mul_le_mul_of_nonneg_left (hlogu u hu)
            (by exact_mod_cast hdnn u : (0 : ℝ) ≤ (d u : ℝ))
      _ = (∑ u ∈ hdfin.toFinset, (d u : ℝ)) * (Real.log T + |Real.log δ₀|) :=
          (Finset.sum_mul _ _ _).symm
  calc |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ d u)‖|
      = |∑ u ∈ hdfin.toFinset, (d u : ℝ) * Real.log ‖u‖| := by rw [hprod, hlog]
    _ ≤ (∑ u ∈ hdfin.toFinset, (d u : ℝ)) * (Real.log T + |Real.log δ₀|) := hbound
    _ = (∑ᶠ u : ℂ, (d u : ℝ)) * (Real.log T + |Real.log δ₀|) := by rw [hsum]

theorem xiECofactorAuxP0 {T : ℝ} (hT : 1 ≤ T) (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → δ₀ ≤ ‖u‖) :
    |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
      (Metric.closedBall 0 T) u))‖| ≤
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 T)) u : ℝ))
        * (Real.log T + |Real.log δ₀|) := by
  exact xiE_divisorProd_log_bound hT δ₀ hδ₀pos hδ₀
    (fun u => MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 T) u)
    (Work.LinnikAreas.DhK.Xi_divisor_support_finite T)
    (fun u => Work.LinnikAreas.DhK.Xi_divisor_nonneg T u)
    (fun u h => Work.LinnikAreas.DhK.Xi_divisor_ne_zero_is_zero h)
    (fun u hu => Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem hu)

end Work.LinnikAreas.ownRepelNW
