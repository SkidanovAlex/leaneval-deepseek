import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.RadialDefs
import Submission.Work.BoseB6Est.lhyRadBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the tail bound for the `I₁`-error integrand

This module proves `Work.BoseB6Est.tailIntegralBound`, the estimate of the
`(K.T, ∞)` part of the `I₁`-error integral used in FS `lem:BogIntegral`
(FS's `eq:LebesgueError-Total`, the "tail" term beyond the kernel's momentum
cutoff):

  `∫_{r > T} r² (G(r) − G₀(r)) dr ≤ (8π)³/(2T)`.

The mathematics has three steps.

* **The radial integrand vanishes beyond the cutoff.**  For `r > K.T` the
  kernel satisfies `β(r) = 0` (`FsKernel.support`), and the truncated kinetic
  symbol `τ̃(r) = (1−ε_T)max(|r|−c₁,0)² + ε_T max(|r|−c₂,0)²` is nonnegative for
  `0 ≤ ε_T ≤ 1` (`fsTau_nonneg`).  Hence

    `G(r) = τ̃(r) − √(τ̃(r)²) − 0 = τ̃(r) − |τ̃(r)| = 0`,

  so the tail integrand is `r² (G − G₀) = −r² G₀(r)`.

* **The pointwise bound.**  Since `G₀ = lhyRad (8π)` (`RadialDefs.fsG0R_eq_lhyRad`,
  definitionally), the sharp small-distance estimate `lhyRad_neg_le`
  (`−(lhyRad c r) ≤ c³/(2r⁴)`, `r > 0`, `c > 0`) gives

    `−r² G₀(r) ≤ r² · (8π)³/(2r⁴) = (8π)³/(2r²)`,

  so the tail is dominated by the model tail `r ↦ (8π)³/(2r²)`.

* **The model tail integral.**  `∫_{r > T} r^{-2} dr = 1/T` (the `rpow` integral
  `integral_Ioi_rpow_of_lt` at exponent `−2`), whence

    `∫_{r > T} (8π)³/(2r²) dr = (8π)³/(2T)`.

No integrability of the difference `r²(G − G₀)` is required: the comparison is
made by `MeasureTheory.integral_mono_of_nonneg`, which needs only that the
dominating function be integrable and that the dominated one be nonnegative.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## 1. The radial integrand beyond the cutoff -/

/-- **The radial `I₁`-integrand vanishes beyond the kernel's cutoff.**  For
`r > K.T` one has `β(r) = 0`, and `τ̃(r) ≥ 0` for `0 ≤ ε_T ≤ 1`, so
`G(r) = τ̃(r) − √(τ̃(r)²) − 0 = τ̃(r) − |τ̃(r)| = 0`. -/
lemma tail_fsGR_eq_zero (K : FsKernel) {εT c1 c2 r : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hr : K.T < r) : fsGR K εT c1 c2 r = 0 := by
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt K.Tnn hr)
  have hτ : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r := fsTau_nonneg hε0 hε1 hr0
  simp only [fsGR, K.support r hr, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, zero_div]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hτ, sub_self]

/-! ## 2. Pointwise estimates for the model bracket `G₀ = lhyRad (8π)` -/

/-- **`G₀(r) < 0`** for `r > 0` (the model bracket is negative). -/
lemma tail_fsG0R_neg {r : ℝ} (hr : 0 < r) : fsG0R r < 0 :=
  lhyRad_neg hr (by positivity)

/-- **The tail bound `−r² G₀(r) ≤ (8π)³/(2r²)`**, the pointwise form of the
sharp small-distance estimate for the model bracket. -/
lemma tail_fsG0R_le {r : ℝ} (hr : 0 < r) :
    -(r ^ 2 * fsG0R r) ≤ (8 * Real.pi) ^ 3 / (2 * r ^ 2) := by
  have h := lhyRad_neg_le hr (show (0 : ℝ) < 8 * Real.pi by positivity)
  rw [fsG0R_eq_lhyRad]
  calc -(r ^ 2 * Work.BoseB6.lhyRad (8 * Real.pi) r)
      = r ^ 2 * (-(Work.BoseB6.lhyRad (8 * Real.pi) r)) := by ring
    _ ≤ r ^ 2 * ((8 * Real.pi) ^ 3 / (2 * r ^ 4)) := mul_le_mul_of_nonneg_left h (sq_nonneg r)
    _ = (8 * Real.pi) ^ 3 / (2 * r ^ 2) := by field_simp

/-! ## 3. The model tail integral -/

/-- `(r²)⁻¹ = r^{-2}` for `r > 0` (matching a natural power with an `rpow`). -/
lemma tail_inv_sq_eq_rpow (r : ℝ) (hr : 0 < r) : (r ^ 2)⁻¹ = r ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]

/-- `r ↦ (8π)³/(2r²)` is integrable on `(T, ∞)` for `T > 0`. -/
lemma tail_integrable_inv_sq {T : ℝ} (hT : 0 < T) :
    Integrable (fun r : ℝ => (8 * Real.pi) ^ 3 / (2 * r ^ 2))
      (volume.restrict (Set.Ioi T)) := by
  have hbase : IntegrableOn (fun r : ℝ => (r ^ 2)⁻¹) (Set.Ioi T) := by
    have h0 : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi T) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hT
    refine h0.congr_fun (fun r hr => ?_) measurableSet_Ioi
    exact (tail_inv_sq_eq_rpow r (lt_trans hT hr)).symm
  have h2 : Integrable (fun r : ℝ => ((8 * Real.pi) ^ 3 / 2) * (r ^ 2)⁻¹)
      (volume.restrict (Set.Ioi T)) := hbase.const_mul _
  refine h2.congr ?_
  filter_upwards with r
  show ((8 * Real.pi) ^ 3 / 2) * (r ^ 2)⁻¹ = (8 * Real.pi) ^ 3 / (2 * r ^ 2)
  ring

/-- **The model tail integral.**  `∫_{r > T} (8π)³/(2r²) dr = (8π)³/(2T)` for
`T > 0`. -/
lemma tail_integral_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ r in Set.Ioi T, (8 * Real.pi) ^ 3 / (2 * r ^ 2) = (8 * Real.pi) ^ 3 / (2 * T) := by
  have hinv : ∫ r in Set.Ioi T, (r ^ 2)⁻¹ = T⁻¹ := by
    have hbase : ∫ r in Set.Ioi T, r ^ (-2 : ℝ) = T⁻¹ := by
      have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at h
      rw [show -T⁻¹ / (-1 : ℝ) = T⁻¹ by ring] at h
      exact h
    rw [← hbase]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    exact tail_inv_sq_eq_rpow r (lt_trans hT hr)
  have hfun : (fun r : ℝ => (8 * Real.pi) ^ 3 / (2 * r ^ 2))
      = fun r => ((8 * Real.pi) ^ 3 / 2) * (r ^ 2)⁻¹ := by
    funext r; ring
  rw [hfun, MeasureTheory.integral_const_mul, hinv]
  ring

/-! ## 4. The tail integral bound -/

/-- **The tail of the `I₁`-error integral.**  Beyond the kernel's momentum
cutoff `K.T` the radial integrand `fsGR` vanishes and only the model bracket
`fsG0R = lhyRad (8π)` contributes; the sharp estimate `lhyRad_neg_le` and the
model tail integral `∫_{r>T} r^{-2} = 1/T` give

  `∫_{r > K.T} r² (fsGR K ε_T c₁ c₂ r − fsG0R r) ≤ (8π)³/(2 K.T)`. -/
theorem tailIntegralBound (K : FsKernel) {εT c1 c2 : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hT : 0 < K.T) :
    ∫ r in Set.Ioi K.T, (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ (8 * Real.pi) ^ 3 / (2 * K.T) := by
  -- beyond the cutoff the integrand is `−r² G₀(r)`
  have hcongr : ∫ r in Set.Ioi K.T, (r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      = ∫ r in Set.Ioi K.T, -(r ^ 2 * fsG0R r) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [tail_fsGR_eq_zero K hε0 hε1 hr]
    ring
  -- it is dominated by `(8π)³/(2r²)`, which is integrable
  have hbdd : ∀ᵐ r ∂(volume.restrict (Set.Ioi K.T)),
      -(r ^ 2 * fsG0R r) ≤ (8 * Real.pi) ^ 3 / (2 * r ^ 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    exact tail_fsG0R_le (lt_trans hT hr)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi K.T)] (fun r => -(r ^ 2 * fsG0R r)) := by
    show ∀ᵐ r ∂(volume.restrict (Set.Ioi K.T)), (0 : ℝ) ≤ -(r ^ 2 * fsG0R r)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have h := tail_fsG0R_neg (lt_trans hT hr)
    nlinarith [sq_nonneg r]
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn (tail_integrable_inv_sq hT) hbdd
  rw [hcongr]
  calc ∫ r in Set.Ioi K.T, -(r ^ 2 * fsG0R r)
      ≤ ∫ r in Set.Ioi K.T, (8 * Real.pi) ^ 3 / (2 * r ^ 2) := hmono
    _ = (8 * Real.pi) ^ 3 / (2 * K.T) := tail_integral_inv_sq hT

end Work.BoseB6Est
