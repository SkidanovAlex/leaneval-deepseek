import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.cs_integral

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

/-- **Pointwise Hardy-type bound.**  For `f : ℝ → ℝ` of class `C¹` on `[0, π/2]` with
`f 0 = 0` and every `θ ∈ [0, π/2]`,

`f θ ^ 2 ≤ θ * ∫_0^{π/2} (deriv f)²`.

This is the elementary step `f θ = ∫_0^θ deriv f` (fundamental theorem of calculus,
`intervalIntegral.integral_deriv_of_contDiffOn_Icc`) followed by Cauchy–Schwarz
(`Work.Spaces.cs_integral`) applied to `deriv f` and the constant function `1` on the
interval `(0, θ)`. -/
theorem hardy_pointwise_bound (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      f θ ^ 2 ≤ θ * ∫ s in Set.Icc 0 (Real.pi / 2), (deriv f s) ^ 2 := by
  intro θ hθ
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have huniq : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hpi
  have hcont : ContinuousOn (fun x => derivWithin f (Set.Icc 0 (Real.pi / 2)) x)
      (Set.Icc 0 (Real.pi / 2)) :=
    (hf.derivWithin (m := 0) huniq (by simp)).continuousOn
  have hint1 : IntegrableOn (fun x => (derivWithin f (Set.Icc 0 (Real.pi / 2)) x) ^ 2)
      (Set.Icc 0 (Real.pi / 2)) :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  have haeI : (fun x => deriv f x) =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))]
      (fun x => derivWithin f (Set.Icc 0 (Real.pi / 2)) x) := by
    have hmeas_eq : volume.restrict (Set.Icc 0 (Real.pi / 2))
        = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Measure.restrict_congr_set Ioo_ae_eq_Icc).symm
    rw [hmeas_eq]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr ?_
    exact Filter.Eventually.of_forall
      (fun x hx => (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm)
  have hIntI : IntegrableOn (fun x => (deriv f x) ^ 2) (Set.Icc 0 (Real.pi / 2)) := by
    refine hint1.congr_fun_ae ?_
    filter_upwards [haeI.symm] with x hx
    rw [hx]
  have hsub : Set.Icc (0 : ℝ) θ ⊆ Set.Icc 0 (Real.pi / 2) := fun x hx => ⟨hx.1, le_trans hx.2 hθ2⟩
  have hFTC : ∫ s in (0 : ℝ)..θ, deriv f s = f θ := by
    rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc (hf.mono hsub) hθ0, h0, sub_zero]
  have hsubIoc : Set.Ioc (0 : ℝ) θ ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun x hx => ⟨le_of_lt hx.1, le_trans hx.2 hθ2⟩
  have hIntIoc : IntegrableOn (fun x => (deriv f x) ^ 2) (Set.Ioc (0 : ℝ) θ) :=
    hIntI.mono_set hsubIoc
  have haeθ : (fun x => deriv f x) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) θ)]
      (fun x => derivWithin f (Set.Icc 0 (Real.pi / 2)) x) := by
    have hmeas_eq : volume.restrict (Set.Ioc (0 : ℝ) θ)
        = volume.restrict (Set.Ioo (0 : ℝ) θ) :=
      (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
    rw [hmeas_eq]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr ?_
    exact Filter.Eventually.of_forall (fun x hx =>
      (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hθ2))).symm)
  have hmeasθ : AEStronglyMeasurable (fun x => deriv f x) (volume.restrict (Set.Ioc (0 : ℝ) θ)) :=
    ((hcont.mono hsubIoc).aestronglyMeasurable measurableSet_Ioc).congr haeθ.symm
  have hu : MemLp (fun x => deriv f x) 2 (volume.restrict (Set.Ioc (0 : ℝ) θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hmeasθ).mpr hIntIoc
  have hv : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) θ)) := by
    rw [MeasureTheory.memLp_const_iff (by norm_num) (by norm_num)]
    right
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hleft : (∫ x in Set.Ioc (0 : ℝ) θ, deriv f x * (1 : ℝ)) = f θ := by
    rw [← intervalIntegral.integral_of_le hθ0]
    simp only [mul_one]
    rw [hFTC]
  have hright : (∫ x in Set.Ioc (0 : ℝ) θ, (1 : ℝ) ^ 2) = θ := by
    rw [← intervalIntegral.integral_of_le hθ0, intervalIntegral.integral_const]
    simp
  have hcs := Work.Spaces.cs_integral hu hv
  rw [hleft, hright] at hcs
  have hmono : (∫ x in Set.Ioc (0 : ℝ) θ, (deriv f x) ^ 2)
      ≤ ∫ x in Set.Icc 0 (Real.pi / 2), (deriv f x) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hIntI (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hsubIoc hx))
  calc f θ ^ 2 ≤ (∫ x in Set.Ioc (0 : ℝ) θ, (deriv f x) ^ 2) * θ := hcs
    _ ≤ (∫ x in Set.Icc 0 (Real.pi / 2), (deriv f x) ^ 2) * θ := mul_le_mul_of_nonneg_right hmono hθ0
    _ = θ * ∫ s in Set.Icc 0 (Real.pi / 2), (deriv f s) ^ 2 := by ring

/-- **Weighted `L²` Hardy inequality with the singular weight `sin(2θ)^{-η}`.**

For `0 ≤ η < 1` there is `K > 0` such that every `C¹` function `f` on `[0, π/2]` with
`f 0 = 0` satisfies

`∫_0^{π/2} f(θ)² sin(2θ)^{-η} dθ ≤ K ∫_0^{π/2} f'(θ)² dθ`.

The weight has integrable singularities at both endpoints (`η < 1`), and the constant may
be taken to be `K = 50 π / (1 - η)`: combining `hardy_pointwise_bound` with
`sin(2θ)^{-η} ≥ 0` and `θ ≤ π/2` reduces the left hand side to
`(π/2) (∫ (deriv f)²) (∫ sin(2θ)^{-η})`, and `Work.Spaces.sin_two_rpow` bounds the last
factor by `100 / (1 - η)`. -/
theorem sin_l2_weight_bound {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 →
      (∫ θ in Set.Icc 0 (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        ≤ K * ∫ θ in Set.Icc 0 (Real.pi / 2), (deriv f θ) ^ 2 := by
  have hKpos : 0 < 50 * Real.pi / (1 - η) := by
    have h1 : (0 : ℝ) < 1 - η := by linarith
    positivity
  refine ⟨50 * Real.pi / (1 - η), hKpos, fun f hf h0 => ?_⟩
  obtain ⟨hIntW, hBndW⟩ := Work.Spaces.sin_two_rpow (-η) (by linarith) (by linarith)
  have hWb : ∫ θ in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) ≤ 100 / (1 - η) := by
    have h := hBndW
    simp only [Work.Spaces.Iθ] at h
    rwa [show -η + 1 = 1 - η by ring] at h
  have hsin_nn : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  set A : ℝ := ∫ s in Set.Icc 0 (Real.pi / 2), (deriv f s) ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun s => sq_nonneg _)
  have hpt : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), f θ ^ 2 ≤ θ * A := by
    intro θ hθ
    rw [hA]
    exact hardy_pointwise_bound f hf h0 θ hθ
  have hle1 : (∫ θ in Set.Icc 0 (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      ≤ ∫ θ in Set.Icc 0 (Real.pi / 2),
          ((Real.pi / 2) * A) * (Real.sin (2 * θ)) ^ (-η) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn θ hθ) _)
    · exact hIntW.const_mul ((Real.pi / 2) * A)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h1 : f θ ^ 2 ≤ θ * A := hpt θ hθ
      have h2 : θ * A ≤ (Real.pi / 2) * A := mul_le_mul_of_nonneg_right hθ.2 hA0
      have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg (hsin_nn θ hθ) _
      exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hw
  have hle2 : (∫ θ in Set.Icc 0 (Real.pi / 2),
          ((Real.pi / 2) * A) * (Real.sin (2 * θ)) ^ (-η))
      = ((Real.pi / 2) * A) * ∫ θ in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) :=
    MeasureTheory.integral_const_mul _ _
  have hnn : 0 ≤ (Real.pi / 2) * A := mul_nonneg (by positivity) hA0
  calc ∫ θ in Set.Icc 0 (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)
      ≤ ∫ θ in Set.Icc 0 (Real.pi / 2),
          ((Real.pi / 2) * A) * (Real.sin (2 * θ)) ^ (-η) := hle1
    _ = ((Real.pi / 2) * A) * ∫ θ in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * θ)) ^ (-η) := hle2
    _ ≤ ((Real.pi / 2) * A) * (100 / (1 - η)) := mul_le_mul_of_nonneg_left hWb hnn
    _ = A * (50 * Real.pi / (1 - η)) := by ring
    _ = (50 * Real.pi / (1 - η)) * ∫ θ in Set.Icc 0 (Real.pi / 2), (deriv f θ) ^ 2 := by
          rw [hA]; ring

end Work.Elliptic
