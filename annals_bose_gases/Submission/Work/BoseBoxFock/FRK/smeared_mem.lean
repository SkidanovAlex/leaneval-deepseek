import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.smeared_mem` — the smearing operator preserves `L¹ ∩ L²`

The smearing (convolution) operator of the FRK window chapter is

  `(K ⋆ u)(z) = ∫ y, K y * u (z - y) dy`,

the Mathlib convolution `MeasureTheory.convolution K u (ContinuousLinearMap.mul ℂ ℂ) volume`.
This file proves that it sends `L¹ ∩ L^∞` to `L¹` and `L¹ ∩ L²` to `L²` in the *integrable
function* (not `MemLp`) spelling needed downstream:

* `K ∈ L¹`, `‖K‖ ≤ M`, `u ∈ L¹`, `‖u‖² ∈ L¹` ⟹ `K ⋆ u ∈ L¹` and `‖K ⋆ u‖² ∈ L¹`.

The first part is Mathlib's `Integrable.integrable_convolution` (an `L¹ ∗ L¹ ⊆ L¹` statement,
which needs no boundedness of `K`).  The second part is **Young's inequality** at `(p,q,r) = (1,2,2)`,
`‖K ⋆ u‖₂ ≤ ‖K‖₁ ‖u‖₂`, which Mathlib does not have for functions; it is proved here from
Mathlib's Hölder inequality `integral_mul_norm_le_Lp_mul_Lq`:

* for each `z`, Cauchy–Schwarz *with the weight* `‖K‖` gives
  `‖(K ⋆ u) z‖² ≤ (∫ y, ‖K y‖) * ∫ y, ‖K y‖ * ‖u (z - y)‖²`
  (`‖F z‖ ≤ ∫ y, ‖K y‖ ‖u (z-y)‖` via `norm_integral_le_integral_norm`, then the weighted
  Cauchy–Schwarz `sq_integral_mul_le_weight` with `f = ‖K ·‖`, `g = ‖u (z - ·)‖`);
* the right-hand side is an *integrable* function of `z`: the weight factor `∫ y, ‖K y‖` is a
  constant and `z ↦ ∫ y, ‖K y‖ ‖u (z - y)‖²` is the convolution `‖K‖ ⋆ ‖u‖² ∈ L¹`
  (`Integrable.integrable_convolution` again, here for real-valued functions);
* `Integrable.mono'` concludes.

The per-`z` integrability of `y ↦ ‖K y‖ ‖u (z - y)‖²` (needed for the weighted Cauchy–Schwarz)
is obtained by domination with `max M 0 * ‖u (z - ·)‖²`, using the translation invariance of
Lebesgue measure (`Integrable.comp_neg`, `Integrable.comp_add_right`).
-/

namespace Work.BoseBoxFock.FRK

open MeasureTheory Filter
open scoped ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Weighted Cauchy–Schwarz.**  For a pointwise nonnegative weight `f` that is integrable and
a function `g` with `f * g ^ 2` integrable (both a.e. strongly measurable),

  `(∫ y, f y * |g y|)² ≤ (∫ y, f y) * (∫ y, f y * g y ^ 2)`.

This is Hölder's inequality with exponents `p = q = 2` applied to the pair
`(√f, √f * g)` (whose `L²` norms are `(∫ f)^{1/2}` and `(∫ f g²)^{1/2}`), followed by squaring. -/
theorem sq_integral_mul_le_weight {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y)
    (hfa : AEStronglyMeasurable f μ) (hga : AEStronglyMeasurable g μ)
    (hf : Integrable f μ) (hfg2 : Integrable (fun y => f y * g y ^ 2) μ) :
    (∫ y, f y * g y ∂μ) ^ 2 ≤ (∫ y, f y ∂μ) * (∫ y, f y * g y ^ 2 ∂μ) := by
  have hsa : AEStronglyMeasurable (fun y => Real.sqrt (f y)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hfa
  have hsb : AEStronglyMeasurable (fun y => Real.sqrt (f y) * g y) μ := hsa.mul hga
  have hinta : Integrable (fun y => Real.sqrt (f y) ^ 2) μ :=
    hf.congr (Eventually.of_forall fun y => (Real.sq_sqrt (hf0 y)).symm)
  have hintb : Integrable (fun y => (Real.sqrt (f y) * g y) ^ 2) μ :=
    hfg2.congr (Eventually.of_forall fun y => by simp only [mul_pow, Real.sq_sqrt (hf0 y)])
  have hma : MemLp (fun y => Real.sqrt (f y)) (ENNReal.ofReal 2) μ := by
    have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [h2, memLp_two_iff_integrable_sq hsa]
    exact hinta
  have hmb : MemLp (fun y => Real.sqrt (f y) * g y) (ENNReal.ofReal 2) μ := by
    have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [h2, memLp_two_iff_integrable_sq hsb]
    exact hintb
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun y => Real.sqrt (f y))
    (g := fun y => Real.sqrt (f y) * g y) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) hma hmb
  -- rewrite the Hölder inequality in the notation of the statement
  have hCSy : (∫ y, ‖Real.sqrt (f y)‖ * ‖Real.sqrt (f y) * g y‖ ∂μ)
      ≤ (∫ y, ‖Real.sqrt (f y)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        * (∫ y, ‖Real.sqrt (f y) * g y‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hCS
  have hL : (∫ y, f y * g y ∂μ) = ∫ y, ‖Real.sqrt (f y)‖ * ‖Real.sqrt (f y) * g y‖ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show f y * g y = ‖Real.sqrt (f y)‖ * ‖Real.sqrt (f y) * g y‖
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hg0 y))]
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hf0 y)]
  have hA : (∫ y, ‖Real.sqrt (f y)‖ ^ (2 : ℝ) ∂μ) = ∫ y, f y ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ‖Real.sqrt (f y)‖ ^ (2 : ℝ) = f y
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hf0 y)]
  have hB : (∫ y, ‖Real.sqrt (f y) * g y‖ ^ (2 : ℝ) ∂μ) = ∫ y, f y * g y ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ‖Real.sqrt (f y) * g y‖ ^ (2 : ℝ) = f y * g y ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hg0 y)), Real.rpow_two, mul_pow,
        Real.sq_sqrt (hf0 y)]
  rw [← hL, hA, hB] at hCSy
  have hA0 : 0 ≤ (∫ y, f y ∂μ) := integral_nonneg hf0
  have hB0 : 0 ≤ (∫ y, f y * g y ^ 2 ∂μ) := integral_nonneg fun y => mul_nonneg (hf0 y) (sq_nonneg _)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCSy
  have hsq : (Real.sqrt (∫ y, f y ∂μ) * Real.sqrt (∫ y, f y * g y ^ 2 ∂μ)) ^ 2
      = (∫ y, f y ∂μ) * (∫ y, f y * g y ^ 2 ∂μ) := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  calc (∫ y, f y * g y ∂μ) ^ 2
      ≤ (Real.sqrt (∫ y, f y ∂μ) * Real.sqrt (∫ y, f y * g y ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun y => mul_nonneg (hf0 y) (hg0 y)) hCSy 2
    _ = (∫ y, f y ∂μ) * (∫ y, f y * g y ^ 2 ∂μ) := hsq

theorem smeared_mem {K u : EuclideanSpace ℝ (Fin 3) → ℂ} {M : ℝ}
    (hK1 : MeasureTheory.Integrable K) (hKb : ∀ y : EuclideanSpace ℝ (Fin 3), ‖K y‖ ≤ M)
    (hu1 : MeasureTheory.Integrable u)
    (hu2 : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => ‖u z‖ ^ 2)) :
    (MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        MeasureTheory.integral MeasureTheory.volume
          (fun y : EuclideanSpace ℝ (Fin 3) => K y * u (z - y))))
      ∧ (MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        ‖MeasureTheory.integral MeasureTheory.volume
          (fun y : EuclideanSpace ℝ (Fin 3) => K y * u (z - y))‖ ^ 2)) := by
  -- `K ⋆ u` is the Mathlib convolution, hence `L¹ ∗ L¹ ⊆ L¹`
  have hF : Integrable (fun z : E3 => ∫ y : E3, K y * u (z - y)) := by
    have h := Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
      (μ := volume) hK1 hu1
    have h2 : convolution K u (ContinuousLinearMap.mul ℂ ℂ) volume
        = fun z : E3 => ∫ y : E3, K y * u (z - y) := by
      funext z
      rw [MeasureTheory.convolution_mul]
    rwa [h2] at h
  refine ⟨hF, ?_⟩
  -- the `L²` half: Young's inequality, by pointwise weighted Cauchy–Schwarz
  have hKm : Integrable (fun y : E3 => ‖K y‖) := hK1.norm
  -- the majorant `z ↦ ‖K‖₁ * ∫ y, ‖K y‖ * ‖u (z - y)‖²` is integrable
  have hI : Integrable (fun z : E3 => ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ ^ 2) := by
    have h := Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := volume) hKm hu2
    have h2 : convolution (fun y : E3 => ‖K y‖) (fun y : E3 => ‖u y‖ ^ 2)
          (ContinuousLinearMap.mul ℝ ℝ) volume
        = fun z : E3 => ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ ^ 2 := by
      funext z
      rw [MeasureTheory.convolution_mul]
    rwa [h2] at h
  have hI' : Integrable (fun z : E3 => (∫ y : E3, ‖K y‖) * ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ ^ 2) :=
    hI.const_mul _
  refine Integrable.mono' hI' ?_ ?_
  · exact (hF.aestronglyMeasurable.norm).pow 2
  · refine Eventually.of_forall fun z => ?_
    show ‖‖∫ y : E3, K y * u (z - y)‖ ^ 2‖
        ≤ (∫ y : E3, ‖K y‖) * ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ ^ 2
    -- per-`z` integrability of `y ↦ ‖u (z - y)‖²` by translation invariance
    have hsubz : Integrable (fun y : E3 => ‖u (z - y)‖ ^ 2) := by
      have h : Integrable (fun t : E3 => ‖u (-t)‖ ^ 2) := hu2.comp_neg
      have h2 := h.comp_add_right (-z)
      refine h2.congr (Eventually.of_forall fun y => ?_)
      show ‖u (-(y + -z))‖ ^ 2 = ‖u (z - y)‖ ^ 2
      rw [show -(y + -z) = z - y by abel]
    have hgu : AEStronglyMeasurable (fun y : E3 => ‖u (z - y)‖) volume := by
      have h := Real.continuous_sqrt.comp_aestronglyMeasurable hsubz.aestronglyMeasurable
      refine h.congr ?_
      filter_upwards with y
      show Real.sqrt (‖u (z - y)‖ ^ 2) = ‖u (z - y)‖
      rw [Real.sqrt_sq (norm_nonneg _)]
    -- the weight `‖K ·‖ * ‖u (z - ·)‖²` is integrable (bounded weight, `‖u‖²` integrable)
    have hperz : Integrable (fun y : E3 => ‖K y‖ * ‖u (z - y)‖ ^ 2) := by
      have hb : Integrable (fun y : E3 => max M 0 * ‖u (z - y)‖ ^ 2) := hsubz.const_mul _
      refine Integrable.mono' hb ?_ ?_
      · exact hKm.aestronglyMeasurable.mul hsubz.aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        show ‖‖K y‖ * ‖u (z - y)‖ ^ 2‖ ≤ max M 0 * ‖u (z - y)‖ ^ 2
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (le_trans (hKb y) (le_max_left M 0)) (sq_nonneg _)
    have hstep1 : ‖∫ y : E3, K y * u (z - y)‖ ≤ ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ := by
      calc ‖∫ y : E3, K y * u (z - y)‖ ≤ ∫ y : E3, ‖K y * u (z - y)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show ‖K y * u (z - y)‖ = ‖K y‖ * ‖u (z - y)‖
          rw [norm_mul]
    have hcs := sq_integral_mul_le_weight (μ := volume) (f := fun y : E3 => ‖K y‖)
      (g := fun y : E3 => ‖u (z - y)‖) (fun y => norm_nonneg _) (fun y => norm_nonneg _)
      hKm.aestronglyMeasurable hgu hKm hperz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖∫ y : E3, K y * u (z - y)‖ ^ 2
        ≤ (∫ y : E3, ‖K y‖ * ‖u (z - y)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstep1 2
      _ ≤ (∫ y : E3, ‖K y‖) * ∫ y : E3, ‖K y‖ * ‖u (z - y)‖ ^ 2 := hcs

end Work.BoseBoxFock.FRK
