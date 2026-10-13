import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel
import Submission.Work.FTS.PressureOn.Auxiliary.ihak_GaussFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shear-average (interval mean) lemma

For a continuous, Gaussian-decaying function `g` on `ℝ³` and any shift vector `h`, the *sliding
average* `z ↦ ∫₀¹ g (z - s h) ds` is integrable and has the same total integral as `g`:

`∫_z ∫₀¹ g (z - s h) ds dz = ∫_z g z dz`.

This is the (very special case of the) `L¹`-invariance of Lebesgue measure under the shear
`z ↦ z - s h` averaged over `s ∈ [0,1]`.  It is the analytic input of the shear-averaging step in
the reconstruction of the Biot–Savart field (the averaged field is the Biot–Savart field of the
averaged vorticity, and the two have a common mean).

The proof is Fubini on the product `(0,1] × ℝ³` together with translation invariance of the
Lebesgue integral (`MeasureTheory.integral_sub_right_eq_self`).  The only analytic input is the
integrability of `(s, z) ↦ g (z - s h)` on `(0,1] × ℝ³`, which follows from the elementary
exponential bound

`exp (-(a ‖z - s h‖²)) ≤ exp (-(a/2 ‖z‖²)) · exp (a ‖h‖² s²)`

(`neg_sq_sub_smul_le` below) and the integrability of the Gaussian `exp (-(a/2 ‖z‖²))`
(`ihak_integrable_rexp_normSq`).
-/

open MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The elementary exponential bound for the shear.**  For `a > 0`, `z, h` in a real normed
space and `s : ℝ`,

`-(a ‖z - s • h‖²) ≤ -(a/2 ‖z‖²) + a ‖h‖² s²`,

i.e. sliding `z` by `s h` costs only a factor `exp (a ‖h‖² s²)` in the Gaussian weight.  It is the
arithmetic mean–geometric mean inequality applied to `‖z‖ ≤ ‖z - s•h‖ + ‖s•h‖`. -/
lemma neg_sq_sub_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (ha : 0 < a) (z h : E) (s : ℝ) :
    -(a * ‖z - s • h‖ ^ 2) ≤ -(a / 2 * ‖z‖ ^ 2) + a * ‖h‖ ^ 2 * s ^ 2 := by
  have h1 : ‖z‖ ≤ ‖z - s • h‖ + ‖s • h‖ := by
    calc ‖z‖ = ‖(z - s • h) + s • h‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - s • h‖ + ‖s • h‖ := norm_add_le _ _
  have h2 : ‖z‖ ^ 2 ≤ (‖z - s • h‖ + ‖s • h‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) h1 2
  have h3 : (‖z - s • h‖ + ‖s • h‖) ^ 2 ≤ 2 * ‖z - s • h‖ ^ 2 + 2 * ‖s • h‖ ^ 2 := by
    nlinarith [two_mul_le_add_sq ‖z - s • h‖ ‖s • h‖]
  have h4 : ‖s • h‖ ^ 2 = s ^ 2 * ‖h‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h5 : ‖z‖ ^ 2 ≤ 2 * ‖z - s • h‖ ^ 2 + 2 * (s ^ 2 * ‖h‖ ^ 2) := by linarith
  have h6 : (a / 2) * ‖z‖ ^ 2 ≤ (a / 2) * (2 * ‖z - s • h‖ ^ 2 + 2 * (s ^ 2 * ‖h‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ a / 2)
  nlinarith [h6]

/-- **The interval mean of the shear translates has the same integral as `g`.**

If `g : ℝ³ → ℝ` is continuous and Gaussian-decaying, `|g w| ≤ C exp (-(a ‖w‖²))` with `a > 0` and
`C ≥ 0`, then for every `h : ℝ³` the averaged translate `z ↦ ∫₀¹ g (z - s h) ds` is integrable and

`∫_z (∫₀¹ g (z - s h) ds) = ∫_z g z`.

(Equivalently: the shear `z ↦ z - s h`, averaged over `s ∈ [0,1]`, preserves the total mass.) -/
theorem ihak_interval_shift_mean {g : Work.FTS.PressureOn.R3 → ℝ} (hg : Continuous g) (C a : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hb : ∀ w, |g w| ≤ C * Real.exp (-(a * ‖w‖ ^ 2)))
    (h : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 => ∫ s in (0 : ℝ)..1, g (z - s • h))
        MeasureTheory.volume
      ∧ (∫ z : Work.FTS.PressureOn.R3, (∫ s in (0 : ℝ)..1, g (z - s • h))) =
          ∫ z : Work.FTS.PressureOn.R3, g z := by
  -- `(0,1]` (equivalently `[0,1]`) carries a finite measure.
  have hfin : volume (Set.uIoc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Real.volume_Ioc]
    simp
  have hI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr hfin
  -- the `s`-factor `exp (a ‖h‖² s²)` is integrable on `(0,1]` (it is bounded there).
  have hf : Integrable (fun s : ℝ => Real.exp (a * ‖h‖ ^ 2 * s ^ 2))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine Integrable.mono' (integrable_const (Real.exp (a * ‖h‖ ^ 2))) ?_ ?_
    · exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (a * ‖h‖ ^ 2 * s ^ 2))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      have hs3 : a * ‖h‖ ^ 2 * s ^ 2 ≤ a * ‖h‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      simpa using hs3
  -- the Gaussian `z`-factor is integrable on `ℝ³`.
  have hgauss : Integrable (fun z : R3 => C * Real.exp (-(a / 2 * ‖z‖ ^ 2))) volume :=
    (ihak_integrable_rexp_normSq (a / 2) (by linarith)).const_mul C
  -- hence the dominating product function is integrable.
  have hBint : Integrable
      (fun p : ℝ × R3 =>
        Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2) * (C * Real.exp (-(a / 2 * ‖p.2‖ ^ 2))))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) :=
    Integrable.mul_prod hf hgauss
  -- and so is `(s,z) ↦ g (z - s h)`.
  have hInt : Integrable (fun p : ℝ × R3 => g (p.2 - p.1 • h))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.mono' hBint ?_ ?_
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      calc |g (p.2 - p.1 • h)| ≤ C * Real.exp (-(a * ‖p.2 - p.1 • h‖ ^ 2)) := hb _
        _ ≤ C * (Real.exp (-(a / 2 * ‖p.2‖ ^ 2)) * Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (neg_sq_sub_smul_le a ha p.2 h p.1)
        _ = Real.exp (a * ‖h‖ ^ 2 * p.1 ^ 2) * (C * Real.exp (-(a / 2 * ‖p.2‖ ^ 2))) := by ring
  refine ⟨?_, ?_⟩
  · -- integrability of `z ↦ ∫₀¹ g (z - s h) ds`, by Fubini (`Integrable.integral_prod_right`).
    have h1 := hInt.integral_prod_right
    refine h1.congr (Eventually.of_forall fun z => ?_)
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  · -- the identity of integrals, by Fubini + translation invariance.
    have hswap := intervalIntegral_integral_swap (f := fun s z => g (z - s • h)) hInt
    calc ∫ z : R3, (∫ s in (0 : ℝ)..1, g (z - s • h))
        = ∫ s in (0 : ℝ)..1, ∫ z : R3, g (z - s • h) := hswap.symm
      _ = ∫ s in (0 : ℝ)..1, ∫ z : R3, g z := by
          apply intervalIntegral.integral_congr
          intro s _
          exact integral_sub_right_eq_self (fun w : R3 => g w) (s • h)
      _ = ∫ z : R3, g z := by
          rw [intervalIntegral.integral_const, sub_zero, one_smul]

end

end Work.FTS.PressureOn.Auxiliary
