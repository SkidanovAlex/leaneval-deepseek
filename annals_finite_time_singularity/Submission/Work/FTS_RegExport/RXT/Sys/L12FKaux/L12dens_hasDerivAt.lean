import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `∂_z (L₁₂dens f) = (Qang f 1 - Qang f 0)/z²`

This module proves

  `Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_hasDerivAt`,

the `z`-derivative of the `L₁₂`-density of a datum of the standing class
(`C⁴` on the open quadrant, `|D_z^k f| ≤ C₀ z^{3/2}/(1+z)²` for `k ≤ 2`).

Writing `A(x) = ∫_θ K(θ) f(x,θ) dθ` (so that `Qang f 0 = A` and `Qang f 1 z = z·A'(z)`,
and `L₁₂dens f = A(x)/x`), the claim is the quotient rule for `x ↦ A(x)/x`:

  `(A'(z)·z - A(z))/z² = (Qang f 1 z - Qang f 0 z)/z²`.

The differentiation under the angular integral is `hasDerivAt_integral_Itheta_K`
(sibling module), which needs bounds for `f` and `∂_z f` on the open strip
`(z/2, 2z) × (0, π/2)`; those come from the standing bound at `k = 0, 1` together with
`‖∂_z f‖ = ‖D_z f‖/x` and `x^{3/2}/(1+x)² ≤ (2z)^{3/2}`, `x^{1/2}/(1+x)² ≤ (2z)^{1/2}`
on the strip.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option maxHeartbeats 800000

/-! ## Two elementary bounds on the strip `(z/2, 2z)` -/

/-- For `0 < x ≤ 2z`, `x^{3/2}/(1+x)² ≤ (2z)^{3/2}`. -/
private theorem rpow_three_halves_div_sq_le {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (hxle : x ≤ 2 * z) :
    x ^ ((3 : ℝ) / 2) / (1 + x) ^ 2 ≤ (2 * z) ^ ((3 : ℝ) / 2) := by
  have h2z : 0 < 2 * z := by linarith
  have h1 : x ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hx.le hxle (by norm_num)
  have h3 : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg h2z.le _
  have h4 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have hbc : (2 * z) ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) * (1 + x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left h4 h3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + x) ^ 2)]
  linarith

/-- For `0 < x ≤ 2z`, `x^{1/2}/(1+x)² ≤ (2z)^{1/2}`. -/
private theorem rpow_half_div_sq_le' {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (hxle : x ≤ 2 * z) :
    x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ (2 * z) ^ ((1 : ℝ) / 2) := by
  have h2z : 0 < 2 * z := by linarith
  have h1 : x ^ ((1 : ℝ) / 2) ≤ (2 * z) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hx.le hxle (by norm_num)
  have h3 : (0 : ℝ) ≤ (2 * z) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h2z.le _
  have h4 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have hbc : (2 * z) ^ ((1 : ℝ) / 2) ≤ (2 * z) ^ ((1 : ℝ) / 2) * (1 + x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left h4 h3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + x) ^ 2)]
  linarith

/-! ## The main statement -/

theorem L12dens_hasDerivAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.FM.L12dens Work.Spaces.K f x)
      ((Work.Elliptic.Qang f 1 z - Work.Elliptic.Qang f 0 z) / z ^ 2) z := by
  have hz2 : 0 < 2 * z := by linarith
  have hp : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz2.le _
  have hq : (0 : ℝ) ≤ (2 * z) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hz2.le _
  have hC : (0 : ℝ) ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) :=
    mul_nonneg hC0 (by linarith)
  -- the two bounds on the open strip `(z/2, 2z) × (0, π/2)`
  have hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |f x θ| ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) := by
    intro x hx θ hθ
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have h := hbd 0 (by norm_num) x θ hxpos hθ.1 hθ.2
    simp only [Work.Spaces.DzIter_zero] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [rpow_three_halves_div_sq_le hz hxpos hx.2.le, hq]
  have hb1 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz f x θ| ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) := by
    intro x hx θ hθ
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hstep : |Work.Spaces.pz f x θ| ≤ C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by
      have hkey : Work.Spaces.pz f x θ = Work.Spaces.DzIter 1 f x θ / x := by
        show Work.Spaces.pz f x θ = x * Work.Spaces.pz f x θ / x
        rw [mul_div_cancel_left₀ _ (ne_of_gt hxpos)]
      rw [hkey, abs_div, abs_of_pos hxpos]
      have h2 := hbd 1 (by norm_num) x θ hxpos hθ.1 hθ.2
      rw [Work.FTS_RegExport.RXT.Slots.rpow_three_halves hxpos] at h2
      calc |Work.Spaces.DzIter 1 f x θ| / x
          ≤ C0 * (x * x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) / x :=
            div_le_div_of_nonneg_right h2 hxpos.le
        _ = C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by field_simp
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [rpow_half_div_sq_le' hz hxpos hx.2.le, hp]
  -- differentiation under the angular integral (the sibling lemma)
  have h2' : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (Nat.cast_le.mpr (by omega : 2 ≤ 4))
  have hd : HasDerivAt (Work.Elliptic.Qang f 0)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ) z :=
    hasDerivAt_integral_Itheta_K (f := f) (z := z)
      (C := C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1))
      h2' hz hC hb1 hb0
  -- `Qang f 1 z = z · (∫_θ K ∂_z f)`, hence the integral is `Qang f 1 z / z`
  have hQ1z : Work.Elliptic.Qang f 1 z
      = z * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ := by
    have h1 : Work.Elliptic.Qang f 1 z
        = ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.K θ * (z * Work.Spaces.pz f z θ) := rfl
    rw [h1, show (fun θ => Work.Spaces.K θ * (z * Work.Spaces.pz f z θ))
        = fun θ => z * (Work.Spaces.K θ * Work.Spaces.pz f z θ) from by
          funext θ; ring,
      MeasureTheory.integral_const_mul]
  have hQ1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ)
      = Work.Elliptic.Qang f 1 z / z := by
    rw [hQ1z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rw [hQ1] at hd
  -- the quotient rule at the base point
  have hq : HasDerivAt (fun y => Work.Elliptic.Qang f 0 y / y)
      ((Work.Elliptic.Qang f 1 z / z * z - Work.Elliptic.Qang f 0 z * 1) / z ^ 2) z :=
    hd.div (hasDerivAt_id z) (ne_of_gt hz)
  have hder : (Work.Elliptic.Qang f 1 z / z * z - Work.Elliptic.Qang f 0 z * 1) / z ^ 2
      = (Work.Elliptic.Qang f 1 z - Work.Elliptic.Qang f 0 z) / z ^ 2 := by
    rw [div_mul_cancel₀ _ (ne_of_gt hz), mul_one]
  rw [hder] at hq
  -- the density is `Qang f 0 x / x`
  have hfun : (fun x => Work.FM.L12dens Work.Spaces.K f x)
      = fun x => Work.Elliptic.Qang f 0 x / x := by
    funext x
    exact Work.FTS_RegExport.RXT.L12Iter.L12dens_eq_Qang_zero f x
  rw [hfun]
  exact hq

end Work.FTS_RegExport.RXT.Sys.L12FKaux
