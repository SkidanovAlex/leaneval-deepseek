/-
# The angular Cauchy–Schwarz step for the `L₁₂`-bound (`.cc`), general order `k`

This is the order-`k` version of `Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le` (`k = 4`),
for the same reason: the weighted angular profile `K · Sw` is paired against the weighted
datum `Gaz h s = h s · w s / Sw` and the pairing is estimated by Cauchy–Schwarz against the
`ℋ^k`-integrand.

```
|∫_θ K θ · Sw θ · Gaz h s θ| ≤ BK · √(∫_θ HkIntegrand α k h s θ)
```

## Route

The only hypothesis is integrability of the slice of the `ℋ^k`-integrand; in particular **no
measurability of `h`** (or of `Gaz h s`) is assumed, so the Cauchy–Schwarz estimate has to be
arranged so that the *only* functions whose measurability is used are the angular profile
`u θ = K θ · Sw θ` (which is continuous) and the square root `w θ = √(HkIntegrand α k h s θ)`
of the majorant (measurable, since the majorant is integrable).

The three inequalities are

1. `|∫ u·v| ≤ ∫ |u·v|` — `MeasureTheory.norm_integral_le_integral_norm`, which holds with no
   hypotheses at all (in particular neither function need be measurable);
2. `∫ |u·v| ≤ ∫ |u|·w` — pointwise `|v| ≤ w` — by the monotonicity of the integral for
   nonnegative functions (`integral_mono_of_nonneg`, the integrability hypothesis being that
   of the measurable majorant `|u|·w ≤ (u² + w²)/2`);
3. `∫ |u|·w ≤ √(∫u²)·√(∫w²)` — the honest Cauchy–Schwarz inequality
   (`abs_integral_mul_le_sqrt`) for the two *measurable* functions `|u|` and `w`.

Finally `∫_θ u θ² = ∫_θ (K θ · Sw θ)² = BK²` and `∫_θ w θ² = ∫_θ HkIntegrand α k h s θ`
(using `√x ^ 2 = x` for `x ≥ 0`).

The pointwise domination `|Gaz h s θ| ≤ √(HkIntegrand α k h s θ)` is the `i = 0` instance of
`Work.Spaces.sq_le_HkIntegrand_z`, which holds for **every** `k` (`0 ≤ k` is automatic over
`ℕ`), so the argument is independent of the order `k`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option maxHeartbeats 800000

/-- The square of the weighted datum is the `D_z^0`-summand of the `ℋ^k`-integrand, at every
order `k`. -/
lemma Gaz_sq_le_HkIntegrand_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Gaz h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k h z θ := by
  simpa only [Gaz, Sw, Work.Spaces.DzIter_zero] using
    Work.Spaces.sq_le_HkIntegrand_z α k h z θ 0 (Nat.zero_le k)

/-- At every order `k`, `|Gaz|` is dominated by the square root of the `ℋ^k`-integrand. -/
lemma abs_Gaz_le_sqrt_HkIntegrand_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    |Gaz h z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k h z θ) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Gaz_sq_le_HkIntegrand_gen α k h z θ)

theorem abs_integral_K_S_Gaz_le_gen (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ) {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k h s θ)
      Work.Spaces.Iθ) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ
        * Work.FTS.GalBasis.cc.Gaz h s θ|
      ≤ Work.FTS.GalBasis.cc.BK
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
  -- the angular profile, the weighted datum and the square root of the majorant
  set u : ℝ → ℝ := fun θ => Work.Spaces.K θ * Sw θ with hu
  set v : ℝ → ℝ := fun θ => Gaz h s θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k h s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k h s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k h s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  -- the pointwise domination of the weighted datum by `w`
  have hvw : ∀ θ : ℝ, |v θ| ≤ w θ := by
    intro θ; rw [hv, hw]; exact abs_Gaz_le_sqrt_HkIntegrand_gen α k h s θ
  -- continuity/measurability
  have hcont_K : Continuous Work.Spaces.K := by
    change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hcont_u : Continuous u := by
    rw [hu]; exact hcont_K.mul continuous_sw
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
  -- the two square roots of the integrals
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = BK := by
    rw [BK]
    congr 1
    simp only [hu]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => sq_abs (Work.Spaces.K θ * Sw θ))
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  -- the three steps
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int
      (Filter.Eventually.of_forall fun θ => ?_)
    show |u θ * v θ| ≤ |u θ| * w θ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvw θ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = BK * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ) := by
        rw [hsqrt_u, hsqrt_w]

end Work.FTS.GalBasis.cc
