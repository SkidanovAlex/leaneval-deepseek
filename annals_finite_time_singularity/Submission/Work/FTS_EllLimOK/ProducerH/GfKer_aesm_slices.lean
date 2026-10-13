import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_EllLimOK.ProducerH.Gf_le_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Measurability and slice integrability of the Tonelli kernel `GfKer`

The joint kernel of the Tonelli step in `Gf_le` is

  `GfKer α U t z = 1_{t<z} · ζ(z) · φ(t)`,  `ζ = GfZeta α`,  `φ = GfPhi α U`

(see `Gf_le_defs`).  This file proves the two measure-theoretic prerequisites of that step:

* `Function.uncurry (GfKer α U)` is a.e. strongly measurable for the product of the two restricted
  measures on `(0,∞)`;
* for every `t > 0` the `z`-slice `z ↦ GfKer α U t z` is integrable on `(0,∞)`.

The first is measurability bookkeeping (`mass_aesm` for the `t`-factor, continuity of `ζ` on
`(0,∞)` for the `z`-factor and the Borel set `{t < z}`); the second uses that the slice is
supported on `(t,∞)`, where `ζ(z) = w(z)²z^{-(β+1)}` is dominated by `(1+1/t)⁴ z^{-(β+1)}`,
an integrable power since `β > 0` for `0 < α ≤ 1`.
-/

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The `z`-factor `ζ = GfZeta` -/

/-- The `z`-factor `ζ(z) = w(z)²|z|^{-(β+1)}` of the kernel is continuous on `(0,∞)`. -/
theorem continuousOn_GfZeta (α : ℝ) :
    ContinuousOn (fun z : ℝ => GfZeta α z) (Set.Ioi 0) := by
  have hbase : ContinuousOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z ^ (-(beta α + 1))) (Set.Ioi 0) := by
    refine continuousOn_w_sq.mul ?_
    exact (continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx))
  refine hbase.congr (fun z hz => ?_)
  unfold GfZeta
  rw [abs_of_pos (show (0 : ℝ) < z from hz)]

/-- **`ζ` is integrable on `(t,∞)` for `t > 0`** (with `β > 0`): on that half-line
`ζ(z) = w(z)²z^{-(β+1)}` is dominated by the integrable power `(1+1/t)⁴ z^{-(β+1)}`, because
`w(z) = (1+1/z)² ≤ (1+1/t)²` for `z ≥ t`. -/
theorem integrableOn_GfZeta (α : ℝ) (hβ : 0 < beta α) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) := by
  have href : IntegrableOn (fun z : ℝ => z ^ (-(beta α + 1))) (Set.Ioi t) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ht
  have hg : Integrable (fun z : ℝ => (1 + 1 / t) ^ 4 * z ^ (-(beta α + 1)))
      (volume.restrict (Set.Ioi t)) := href.const_mul ((1 + 1 / t) ^ 4)
  have hf : AEStronglyMeasurable (fun z : ℝ => GfZeta α z) (volume.restrict (Set.Ioi t)) :=
    ((continuousOn_GfZeta α).mono (Set.Ioi_subset_Ioi (le_of_lt ht))).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' hg hf ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hzt : t < z := hz
  have hz0 : 0 < z := lt_trans ht hzt
  have h1 : (1 : ℝ) + 1 / z ≤ 1 + 1 / t := by
    have h := one_div_le_one_div_of_le ht (le_of_lt hzt)
    linarith
  have h2 : 0 ≤ (1 : ℝ) + 1 / z := by positivity
  have hwz : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w, ← div_pow]
    congr 1
    rw [add_div, div_self (ne_of_gt hz0)]
    ring
  have hw2 : (Work.Spaces.w z) ^ 2 ≤ (1 + 1 / t) ^ 4 := by
    have h3 : ((1 + 1 / z) ^ 2) ^ 2 ≤ ((1 + 1 / t) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ h2 h1 2) 2
    calc (Work.Spaces.w z) ^ 2 = ((1 + 1 / z) ^ 2) ^ 2 := by rw [hwz]
      _ ≤ ((1 + 1 / t) ^ 2) ^ 2 := h3
      _ = (1 + 1 / t) ^ 4 := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (GfZeta_nonneg α z)]
  unfold GfZeta
  rw [abs_of_pos hz0]
  exact mul_le_mul_of_nonneg_right hw2 (Real.rpow_nonneg (le_of_lt hz0) (-(beta α + 1)))

/-! ## Joint a.e. strong measurability -/

/-- **Joint a.e. strong measurability of the kernel.**  For `U ∈ ℋ⁰` the function
`(t,z) ↦ GfKer α U t z` is a.e. strongly measurable for the product of the restricted measures
on `(0,∞)`. -/
theorem GfKer_uncurry_aesm (α : ℝ) {U : ℝ → ℝ → ℝ} (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (GfKer α U))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := by
  have hζ : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => GfZeta α z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (continuousOn_GfZeta α).aestronglyMeasurable measurableSet_Ioi
  have hmass : MeasureTheory.AEStronglyMeasurable (mass α U)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := mass_aesm α U hU
  have habs : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => |t| ^ (beta α + 4))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun t : ℝ => t ^ (beta α + 4)) (Set.Ioi 0) :=
      (continuous_id.continuousOn).rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    refine (hcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    show t ^ (beta α + 4) = |t| ^ (beta α + 4)
    rw [abs_of_pos (show (0 : ℝ) < t from ht)]
  have hden : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ((1 + t) ^ 4)⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun t : ℝ => (1 + t) ^ 4) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).pow 4).continuousOn
    exact (hc.inv₀ (fun t ht => pow_ne_zero 4 (by linarith [show (0 : ℝ) < t from ht]))).aestronglyMeasurable
      measurableSet_Ioi
  have hφ : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => GfPhi α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => |t| ^ (beta α + 4) * mass α U t * ((1 + t) ^ 4)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := (habs.mul hmass).mul hden
    refine hprod.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t _ => ?_)
    show |t| ^ (beta α + 4) * mass α U t * ((1 + t) ^ 4)⁻¹
        = |t| ^ (beta α + 4) * mass α U t / (1 + t) ^ 4
    rw [div_eq_mul_inv]
  have hζ2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => GfZeta α p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := hζ.comp_snd
  have hφ2 : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => GfPhi α U p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := hφ.comp_fst
  have hind : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if p.1 < p.2 then (1 : ℝ) else 0)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    exact (Measurable.ite hset measurable_const measurable_const).aestronglyMeasurable
  show MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((if p.1 < p.2 then 1 else 0) * GfZeta α p.2) * GfPhi α U p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0)))
  exact (hind.mul hζ2).mul hφ2

/-! ## Integrability of the `z`-slices -/

/-- **The `z`-slices of the kernel are integrable.**  For `0 < α ≤ 1` and every `t > 0` the
function `z ↦ GfKer α U t z` is integrable on `(0,∞)`: it is supported on `(t,∞)` — where `ζ` is
integrable — and equals `ζ` there up to the multiplicative constant `φ(t)`. -/
theorem GfKer_slice_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (U : ℝ → ℝ → ℝ)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable (GfKer α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hZetat : IntegrableOn (fun z : ℝ => GfZeta α z) (Set.Ioi t) :=
    integrableOn_GfZeta α (beta_pos hα hα1) ht
  have hOn_t : IntegrableOn (fun z : ℝ => (if t < z then 1 else 0) * GfZeta α z)
      (Set.Ioi t) := by
    refine hZetat.congr_fun ?_ measurableSet_Ioi
    intro z hz
    show GfZeta α z = (if t < z then 1 else 0) * GfZeta α z
    rw [ite_eq_left (show t < z from hz), one_mul]
  have hmain : Integrable (fun z : ℝ => (if t < z then 1 else 0) * GfZeta α z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hOn_t.of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => by
      have hx2 : ¬ (t < x) := hx.2
      rw [ite_eq_right hx2, zero_mul])
  have hfin : Integrable (fun z : ℝ => ((if t < z then 1 else 0) * GfZeta α z)
      * GfPhi α U t) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hmain.mul_const (GfPhi α U t)
  show Integrable (fun z : ℝ => ((if t < z then 1 else 0) * GfZeta α z) * GfPhi α U t)
      (MeasureTheory.volume.restrict (Set.Ioi 0))
  exact hfin

/-! ## The requested lemma -/

theorem GfKer_aesm_slices {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (GfKer α U))
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioi 0))) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ), MeasureTheory.Integrable (GfKer α U t)
        (MeasureTheory.volume.restrict (Set.Ioi 0))) :=
  ⟨GfKer_uncurry_aesm α hU, fun _ ht => GfKer_slice_integrable hα hα1 U ht⟩

end Work.FTS_EllLimOK.ProducerH
