/-
# The angular slice pairing bound with the *numerical* constant `3√(π/2)` (`E5Aux3`)

This is the `α`-free angular Cauchy–Schwarz estimate of `GalBasis.cc.abs_integral_K_S_Gaz_le`
with the abstract constant `BK = √(∫_θ (K·Sw)²)` replaced by the explicit value `3√(π/2)`.

```
∫_θ |K θ · Sw θ · Gaz F s θ| ≤ 3√(π/2) · √(∫_θ HkIntegrand α 4 F s θ)
```

The exchange is cheap: on the angular interval `Iθ = [0, π/2]`

* `0 ≤ K θ ≤ 3` (`K = 3 sin θ cos²θ`), and
* `0 ≤ Sw θ ≤ 1` (`Sw = sin(2θ)^{η/2}` with `0 < η/2` and `0 ≤ sin(2θ) ≤ 1`),

so `(K θ · Sw θ)² ≤ 9` and `∫_θ (K·Sw)² ≤ 9 · vol(Iθ) = 9·(π/2)`, whence
`√(∫_θ (K·Sw)²) ≤ 3√(π/2)`.

The proof is otherwise verbatim the one of `abs_integral_K_S_Gaz_le`:

1. `∫ |u·v| ≤ ∫ |u|·w` where `w = √(HkIntegrand α 4 F s θ)` and `|v| = |Gaz| ≤ w`
   (`abs_Gaz_le_sqrt_HkIntegrand`), by monotonicity of the integral;
2. `∫ |u|·w ≤ √(∫|u|²)·√(∫w²)` — Cauchy–Schwarz `abs_integral_mul_le_sqrt` for the two
   measurable functions `|u| = |K·Sw|` (continuous) and `w` (measurable because the
   majorant is integrable);
3. `∫|u|² = ∫(K·Sw)² ≤ 9π/2` and `∫w² = ∫HkIntegrand α 4 F s θ`.

Note that no measurability of `F` (nor of `Gaz F s`) is used: the only functions whose
measurability enters are the continuous angular profile `K·Sw` and the square root of the
majorant, which is measurable because its square is the assumed-integrable majorant.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option maxHeartbeats 800000

theorem AngSlicePairLe {α s : ℝ} {F : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 F s θ)
      Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ
        * Work.FTS.GalBasis.cc.Gaz F s θ|
      ≤ 3 * Real.sqrt (π / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) := by
  -- the angular profile, the weighted datum and the square root of the majorant
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ with hu
  set v : ℝ → ℝ := fun θ => Work.FTS.GalBasis.cc.Gaz F s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 F s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 F s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by intro θ; rw [hw]; exact Real.sqrt_nonneg _
  -- the pointwise domination of the weighted datum by `w`
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact Work.FTS.GalBasis.cc.abs_Gaz_le_sqrt_HkIntegrand α F s θ
  -- continuity/measurability
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul Work.FTS.GalBasis.cc.continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  -- integrability of `u²` and of `w²`
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  -- integrability of the majorant `|u|·w`
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  -- `L²`-membership of the two measurable factors
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  -- step 1: the pointwise domination, integrated
  have h1 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  -- step 2: the majorant is nonnegative, so its integral is its absolute value
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  have hsqrt_u2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
    congr 1
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (u θ))
  have hsqrt_w2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  -- step 3a: the numerical bound `(K·Sw)² ≤ 9` on the angular interval
  have hu_le : ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 ≤ 9 := by
    intro θ hθ
    have hK0 := Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ
    have hK3 := Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hθ
    have hS0 := Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθ
    have hS1 : Work.FTS.GalBasis.cc.Sw θ ≤ 1 := by
      rw [Work.FTS.GalBasis.cc.Sw]
      refine Real.rpow_le_one (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)
        (Real.sin_le_one _) ?_
      norm_num [Work.Spaces.eta]
    rw [hu]
    have h3 : Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ ≤ 3 := by nlinarith
    have h0 : 0 ≤ Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ := mul_nonneg hK0 hS0
    nlinarith
  have hconst_int : IntegrableOn (fun _ : ℝ => (9:ℝ)) Work.Spaces.Iθ :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hu2_le : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (9:ℝ) :=
    MeasureTheory.setIntegral_mono_on hu2_int hconst_int hIθ hu_le
  -- step 3b: `∫_θ 9 = 9·(π/2)` because `Iθ` has length `π/2`
  have hconst_val : ∫ θ in Work.Spaces.Iθ, (9:ℝ) = 9 * (π / 2) := by
    rw [MeasureTheory.setIntegral_const]
    change (MeasureTheory.volume.real (Set.Icc 0 (π / 2))) • (9:ℝ) = 9 * (π / 2)
    rw [Real.volume_real_Icc, max_eq_left (by linarith [Real.pi_pos])]
    ring
  -- step 3c: `√(∫ u²) ≤ 3√(π/2)`
  have hsqrt_u_le : Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) ≤ 3 * Real.sqrt (π / 2) := by
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ Real.sqrt (9 * (π / 2)) := by
          refine Real.sqrt_le_sqrt ?_
          calc ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, (9:ℝ) := hu2_le
            _ = 9 * (π / 2) := hconst_val
      _ = 3 * Real.sqrt (π / 2) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9),
            show Real.sqrt (9:ℝ) = 3 by
              rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  calc ∫ θ in Work.Spaces.Iθ, |u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h1
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h2
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) := by
        rw [hsqrt_u2, hsqrt_w2]
    _ ≤ (3 * Real.sqrt (π / 2))
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ) :=
        mul_le_mul_of_nonneg_right hsqrt_u_le (Real.sqrt_nonneg _)

end Work.FTS.StrongEps.E5Aux3
