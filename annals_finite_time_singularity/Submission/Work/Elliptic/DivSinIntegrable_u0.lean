import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.SliceBddBounds

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

/-- The angular interval `[0, π/2]` is contained in the open neighbourhood of smoothness. -/
private lemma Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hx
  exact ⟨by linarith [hx'.1], by linarith [hx'.2, Real.pi_pos]⟩

private lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

private lemma contOn_h (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    ContinuousOn h Work.Spaces.Iθ :=
  hh.continuousOn.mono Iθ_subset_Ioo

private lemma contOn_deriv_deriv (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    ContinuousOn (deriv (deriv h)) Work.Spaces.Iθ := by
  have hU : IsOpen (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := isOpen_Ioo
  have h3 : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) h (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    hh.of_le (by norm_num)
  have h2 : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (deriv h)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    h3.deriv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (deriv (deriv h))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    h2.deriv_of_isOpen hU (by norm_num)
  exact h1.continuousOn.mono Iθ_subset_Ioo

private lemma aemeasurable_h (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    AEMeasurable h (volume.restrict Work.Spaces.Iθ) :=
  (contOn_h h hh).aemeasurable measurableSet_Iθ

private lemma aemeasurable_deriv_deriv (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    AEMeasurable (fun θ => deriv (deriv h) θ) (volume.restrict Work.Spaces.Iθ) :=
  (contOn_deriv_deriv h hh).aemeasurable measurableSet_Iθ

private lemma aemeasurable_SinQ (h : ℝ → ℝ) (hh : Work.Elliptic.SmoothSlice h) :
    AEMeasurable (SinQ h) (volume.restrict Work.Spaces.Iθ) := by
  have hsin : AEMeasurable (fun θ : ℝ => Real.sin (2 * θ)) (volume.restrict Work.Spaces.Iθ) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).aemeasurable
  have hdiv : AEMeasurable (fun θ : ℝ => h θ / Real.sin (2 * θ)) (volume.restrict Work.Spaces.Iθ) :=
    (aemeasurable_h h hh).div hsin
  exact hdiv

private lemma aemeasurable_sin_two_rpow (p : ℝ) (hp : 0 ≤ p) :
    AEMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (volume.restrict Work.Spaces.Iθ) :=
  ((Real.continuous_rpow_const hp).comp
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ))).aemeasurable

private lemma aemeasurable_cos_two_sq :
    AEMeasurable (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
  ((by fun_prop : Continuous fun θ : ℝ => Real.cos (2 * θ)).aemeasurable).pow_const 2

/-- For `θ ∈ [0, π/2]` and `p ≥ 0`, `sin(2θ)^p ∈ [0,1]`. -/
private lemma sin_two_rpow_abs_le_one (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) {p : ℝ}
    (hp : 0 ≤ p) : |(Real.sin (2 * θ)) ^ p| ≤ 1 := by
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := hθ
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1]) (by linarith [hθ'.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h2 : (Real.sin (2 * θ)) ^ p ≤ 1 := Real.rpow_le_one h0 h1 hp
  have h3 : 0 ≤ (Real.sin (2 * θ)) ^ p := Real.rpow_nonneg h0 p
  rw [abs_le]; exact ⟨by linarith, h2⟩

private lemma cos_two_sq_le_one (θ : ℝ) : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg (Real.cos (2 * θ))) (Real.abs_cos_le_one (2 * θ)) 2
  rwa [sq_abs, one_pow] at h

theorem DivSinIntegrable_u0 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ)
    (hh : Work.Elliptic.SmoothSlice h) (hb : Work.Elliptic.SliceBdd h) :
    MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α) * (Work.Elliptic.SinQ h θ) ^ 2)
        Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn
        (fun θ => (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          * (Work.Elliptic.SinQ h θ) ^ 2)
        Work.Spaces.Iθ MeasureTheory.volume
      ∧ MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        Work.Spaces.Iθ MeasureTheory.volume := by
  obtain ⟨C, hC0, hbd⟩ := SliceBdd_ae_bounds h hh hb
  have hp1 : 0 ≤ 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 0 ≤ 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hfin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ]; exact isCompact_Icc.measure_lt_top
  have sq_le (θ : ℝ) (hbθ : |SinQ h θ| ≤ C) : (SinQ h θ) ^ 2 ≤ C ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (SinQ h θ)) hbθ 2
    rwa [sq_abs] at h
  refine ⟨?_, ?_, ?_⟩
  · apply IntegrableOn.of_bound hfin ?_ (C ^ 2) ?_
    · exact ((aemeasurable_sin_two_rpow (4 - Work.Spaces.gam α) hp1).mul
        ((aemeasurable_SinQ h hh).pow_const 2)).aestronglyMeasurable
    · filter_upwards [hbd, ae_restrict_mem measurableSet_Iθ] with θ hbθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_sq]
      have hsin := sin_two_rpow_abs_le_one θ hθmem hp1
      calc |(Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)| * (SinQ h θ) ^ 2
          ≤ 1 * (SinQ h θ) ^ 2 := mul_le_mul_of_nonneg_right hsin (sq_nonneg _)
        _ = (SinQ h θ) ^ 2 := one_mul _
        _ ≤ C ^ 2 := sq_le θ hbθ.2.2.1
  · apply IntegrableOn.of_bound hfin ?_ (C ^ 2) ?_
    · exact (((aemeasurable_cos_two_sq).mul (aemeasurable_sin_two_rpow (2 - Work.Spaces.gam α) hp2)).mul
        ((aemeasurable_SinQ h hh).pow_const 2)).aestronglyMeasurable
    · filter_upwards [hbd, ae_restrict_mem measurableSet_Iθ] with θ hbθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_sq, abs_sq]
      have hsin := sin_two_rpow_abs_le_one θ hθmem hp2
      have hcos := cos_two_sq_le_one θ
      calc (Real.cos (2 * θ)) ^ 2 * |(Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)|
            * (SinQ h θ) ^ 2
          ≤ 1 * 1 * (SinQ h θ) ^ 2 := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul hcos hsin (abs_nonneg _) (by norm_num)
            · exact sq_nonneg _
        _ = (SinQ h θ) ^ 2 := by ring
        _ ≤ C ^ 2 := sq_le θ hbθ.2.2.1
  · apply IntegrableOn.of_bound hfin ?_ (C ^ 2) ?_
    · exact (((aemeasurable_deriv_deriv h hh).pow_const 2).mul
        (aemeasurable_sin_two_rpow (2 - Work.Spaces.gam α) hp2)).aestronglyMeasurable
    · filter_upwards [hbd, ae_restrict_mem measurableSet_Iθ] with θ hbθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_sq]
      have hsin := sin_two_rpow_abs_le_one θ hθmem hp2
      have hd : (deriv (deriv h) θ) ^ 2 ≤ C ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg (deriv (deriv h) θ)) hbθ.2.1 2
        rwa [sq_abs] at h
      calc (deriv (deriv h) θ) ^ 2 * |(Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)|
          ≤ C ^ 2 * 1 := mul_le_mul hd hsin (abs_nonneg _) (by positivity)
        _ = C ^ 2 := by ring

end Work.Elliptic
