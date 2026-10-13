import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.sin_l2_weight_bound
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Auxiliary lemmas for `DivSinL2Est`

`DivSinL2Est` bounds the weighted `L²`-norm `∫_{Iθ} h² sin(2θ)^{2-γ}` of a smooth slice
`h` vanishing at `θ = 0` and `θ = π/2` by the *more* singular quantity
`∫_{Iθ} (deriv h)² / sin(2θ)^η`, with `η = 99/100 < 1` and `γ = 1 + α/10 ≤ 11/10`.

The three ingredients (all one-dimensional, all elementary):

* `smoothSlice_contDiffOn_one` — a `SmoothSlice` is `C¹` on the closed interval `Iθ`;
* `integral_sq_mul_rpow_le` — on `Iθ` the base `sin(2θ)` lies in `[0,1]` and the exponent
  `2 - γ` is nonnegative, so the weight `sin(2θ)^{2-γ}` is `≤ 1` and may be dropped;
* `integrableOn_deriv_sq_div_sin` and `integral_deriv_sq_le_div_sin` — the weighted
  derivative integral is honest (`η < 1`) and dominates the unweighted one.

The Poincaré step `∫_{Iθ} h² ≤ K ∫_{Iθ} (deriv h)²` is the already-proved
`Work.Elliptic.sin_l2_weight_bound` at `η = 0`. -/

/-- A `SmoothSlice` is of class `C¹` on the closed interval `Iθ = [0, π/2]`. -/
private lemma smoothSlice_contDiffOn_one {h : ℝ → ℝ} (hsm : SmoothSlice h) :
    ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact (hsm.mono hsub).of_le le_top

/-- On `Iθ`, `sin (2 * θ)` lies in `[0,1]`. -/
private lemma sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- Dropping the weight `sin(2θ)^{2-γ}` from the integrand: for `2 - γ ≥ 0` the weight is
at most `1` on `Iθ`, where `sin(2θ) ∈ [0,1]`. -/
private lemma integral_sq_mul_rpow_le {γ : ℝ} (hγ : 0 ≤ 2 - γ) {h : ℝ → ℝ}
    (hcont : ContinuousOn h Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
  have hInt : IntegrableOn (fun θ : ℝ => (h θ) ^ 2) Work.Spaces.Iθ :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  refine MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_
  · filter_upwards [ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem hθ) _)
  · filter_upwards [ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    exact Real.rpow_le_one (sin_two_nonneg_of_mem hθ) (Real.sin_le_one _) hγ

/-- The weighted derivative integrand `(deriv h θ)^2 / sin(2θ)^η` is integrable on `Iθ`
for `0 ≤ η < 1`: `deriv h` is bounded there and `sin(2θ)^{-η}` has integrable
singularities at the two endpoints. -/
private lemma integrableOn_deriv_sq_div_sin {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {h : ℝ → ℝ} (hsm : SmoothSlice h) (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    IntegrableOn (fun θ : ℝ => (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      Work.Spaces.Iθ := by
  obtain ⟨A, hA0, -, hAb⟩ := contDiffOn_one_bounds (smoothSlice_contDiffOn_one hsm) h0 hp
  have hsin_int : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-η) (by linarith) (by linarith)).1
  have hg_int : Integrable (fun θ : ℝ => A ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.const_mul hsin_int (A ^ 2)
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      (volume.restrict Work.Spaces.Iθ) :=
    (((measurable_deriv h).pow_const 2).div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const η)).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hg_int hmeas ?_
  have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
  have hmem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [hμ]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with θ hθ
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hq : (deriv h θ) ^ 2 ≤ A ^ 2 := by
    have hb := hAb θ hθ
    rw [Real.norm_eq_abs] at hb
    rw [sq_le_sq, abs_of_nonneg hA0]
    exact hb
  have hval : (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ η
      = (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hs.le η]
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hs η).le), hval]
  exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hs.le (-η))

/-- On `Iθ` the weighted derivative integral dominates the unweighted one, because
`sin(2θ)^η ≤ 1` there (so `1/sin(2θ)^η ≥ 1`). -/
private lemma integral_deriv_sq_le_div_sin {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {h : ℝ → ℝ} (hsm : SmoothSlice h) (h0 : h 0 = 0) (hp : h (Real.pi / 2) = 0) :
    ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ η := by
  have hInt := integrableOn_deriv_sq_div_sin hη0 hη1 hsm h0 hp
  refine MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_
  · exact Filter.Eventually.of_forall (fun θ => sq_nonneg _)
  · have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ]
      exact (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
    have hmem : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      rw [hμ]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with θ hθ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : (Real.sin (2 * θ)) ^ η ≤ 1 :=
      Real.rpow_le_one hs.le (Real.sin_le_one _) hη0
    have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ η)⁻¹ :=
      (one_le_inv₀ (Real.rpow_pos_of_pos hs η)).mpr hs1
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_right (sq_nonneg _) hinv

theorem DivSinL2Est (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ), Work.Elliptic.SmoothSlice h → h 0 = 0 →
      h (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ C * ∫ θ in Work.Spaces.Iθ,
            (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  obtain ⟨K, hKpos, hK⟩ := sin_l2_weight_bound (η := 0) le_rfl zero_lt_one
  refine ⟨K, hKpos, fun h hsm h0 hp => ?_⟩
  have hCD1 : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := smoothSlice_contDiffOn_one hsm
  have hγ : 0 ≤ 2 - Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hdrop : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 :=
    integral_sq_mul_rpow_le hγ hCD1.continuousOn
  have hpoin : (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2)
      ≤ K * ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 := by
    have h := hK h hCD1 h0
    simpa [Work.Spaces.Iθ] using h
  have hwt := integral_deriv_sq_le_div_sin Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one hsm h0 hp
  calc (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := hdrop
    _ ≤ K * ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 := hpoin
    _ ≤ K * (∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left hwt hKpos.le

end Work.Elliptic
