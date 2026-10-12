import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.OneBodyKin.bsKern_eq_conv
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.integrable_bsKern`

The position-space kernel `Work.OneBodyKin.bsKern ℓ F` of the cross term (defined in
`Submission/Work/OneBodyKin/CrossKern.lean`) is **integrable** on `ℝ³` as soon as the symbol
`F` is radial-`L¹`, i.e. `∫_p ‖F ‖p‖‖ dp < ∞`.

Since `χ` is a compactly supported bump (`chi_hasCompactSupport`) and
`profHat q = ∫_z χ z cos⟪q,z⟫ dz` is bounded by `∫_z ‖χ z‖ dz`, the inner `p`-integral

  `K t = ∫_p F ‖p‖ · profHat (ℓ·p) · χ t · cos⟪ℓ·p, t⟫ dp`

is a bounded function of `t` times `χ t`, hence integrable (`integrable_chiMul_integral`).  The
substitution `t = s + ℓ⁻¹·d` in the `s`-integral turns `bsKern ℓ F` into the convolution of `K`
with the indicator of the unit cube, evaluated at `ℓ⁻¹·d` (`bsKern_eq_conv`); a convolution of
two `L¹` functions is `L¹` (`Integrable.integrable_convolution`) and `L¹` is preserved by the
dilation `d ↦ ℓ⁻¹·d` (`Integrable.comp_smul`).
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## Elementary API of the bump profile `profHat` -/

/-- **The bump profile is bounded by the total mass of the bump**:
`|profHat p| ≤ ∫_z |χ z| dz`.  This is the elementary `L¹ → L^∞` bound for the cosine transform
of the compactly supported bump `χ` (`‖cos‖ ≤ 1`); no decay of `profHat` is needed. -/
lemma abs_profHat_le (p : ℝ³) : |profHat p| ≤ ∫ z : ℝ³, |chi z| := by
  have hchi : Integrable (fun z : ℝ³ => chi z) :=
    chi_continuous.integrable_of_hasCompactSupport chi_hasCompactSupport
  have hcos : Continuous (fun z : ℝ³ => Real.cos (inner ℝ p z)) :=
    Real.continuous_cos.comp (continuous_const.inner continuous_id)
  have hcont : Continuous (fun z : ℝ³ => chi z * Real.cos (inner ℝ p z)) :=
    chi_continuous.mul hcos
  have hb : ∀ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ ≤ ‖chi z‖ := by
    intro z
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z))
  have hg : Integrable (fun z : ℝ³ => ‖chi z * Real.cos (inner ℝ p z)‖) := by
    refine Integrable.mono' hchi.norm hcont.norm.aestronglyMeasurable ?_
    filter_upwards with z
    simpa using hb z
  have hm : ‖∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)‖
      ≤ ∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ :=
    norm_integral_le_integral_norm _
  have h2 : (∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖) ≤ ∫ z : ℝ³, ‖chi z‖ :=
    integral_mono hg hchi.norm hb
  rw [profHat]
  calc |∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)|
      = ‖∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ z : ℝ³, ‖chi z * Real.cos (inner ℝ p z)‖ := hm
    _ ≤ ∫ z : ℝ³, ‖chi z‖ := h2
    _ = ∫ z : ℝ³, |chi z| := by simp [Real.norm_eq_abs]

/-- The bump profile `profHat` is strongly measurable: it is the `p`-parametric integral of the
jointly continuous function `(p, z) ↦ χ z · cos⟪p, z⟫` (`StronglyMeasurable.integral_prod_right`). -/
lemma stronglyMeasurable_profHat : StronglyMeasurable (profHat : ℝ³ → ℝ) := by
  have hc : Continuous
      (Function.uncurry (fun (p : ℝ³) (z : ℝ³) => chi z * Real.cos (inner ℝ p z))) := by
    rw [continuous_iff_continuousAt]
    intro w
    exact ((chi_continuous.comp continuous_snd).continuousAt).mul
      ((Real.continuous_cos.comp (continuous_fst.inner continuous_snd)).continuousAt)
  have h : StronglyMeasurable
      (Function.uncurry (fun (p : ℝ³) (z : ℝ³) => chi z * Real.cos (inner ℝ p z))) :=
    hc.stronglyMeasurable
  have := StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ³)) h
  change StronglyMeasurable (fun x : ℝ³ => ∫ y : ℝ³, chi y * Real.cos (inner ℝ x y))
  exact this

/-! ## The indicator of the unit cube -/

/-- The indicator of the unit cube `acube 1` is integrable (`acube 1` has finite volume). -/
lemma integrable_indicator_acube_one :
    Integrable ((acube 1).indicator (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff (acube_measurable 1)]
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top 1 (by norm_num)⟩
  exact integrable_const (1 : ℝ)

/-! ## The main theorem -/

theorem integrable_bsKern {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖)) :
    MeasureTheory.Integrable (Work.OneBodyKin.bsKern ℓ F) := by
  -- the `t`-kernel of the cross term is `L¹`
  have hK : Integrable
      (fun t : ℝ³ => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * chi t * Real.cos (inner ℝ (ℓ • p) t)) :=
    integrable_chiMul_integral hFi
  -- the unit-cube indicator is `L¹`
  have hg : Integrable ((acube 1).indicator (fun _ => (1 : ℝ))) :=
    integrable_indicator_acube_one
  -- the convolution of two `L¹` functions is `L¹`
  have hconv : Integrable (MeasureTheory.convolution
      (fun t : ℝ³ => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * chi t * Real.cos (inner ℝ (ℓ • p) t))
      ((acube 1).indicator (fun _ => (1 : ℝ)))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    Integrable.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hK hg
  -- dilation preserves `L¹`
  have hcomp : Integrable (fun d : ℝ³ => MeasureTheory.convolution
      (fun t : ℝ³ => ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * chi t * Real.cos (inner ℝ (ℓ • p) t))
      ((acube 1).indicator (fun _ => (1 : ℝ)))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume (ℓ⁻¹ • d)) :=
    hconv.comp_smul (inv_ne_zero (ne_of_gt hℓ))
  -- and `bsKern ℓ F d` is that convolution evaluated at `ℓ⁻¹ • d`
  refine hcomp.congr ?_
  filter_upwards with d
  exact (bsKern_eq_conv hℓ F d).symm

end Work.OneBodyKin
