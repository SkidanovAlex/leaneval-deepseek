/-
Copyright: work module for the Elgindi finite-time singularity project.

# The mean-zero Poincaré inequality on the angular slice, for `C¹` functions on `(0, π/2)`

This file proves the one-dimensional Poincaré (Wirtinger) estimate with mean zero used by the
angular analysis of Elgindi's paper, in the *weak* regularity class in which it is consumed:

> if `f` is `C¹` on the open interval `(0, π/2)`, its derivative is square-integrable on
> `Iθ = [0, π/2]` and `∫₀^{π/2} f = 0`, then `f²` is integrable on `Iθ` and
> `∫_{Iθ} f² ≤ C ∫_{Iθ} (f')²`

with the explicit (non-sharp) constant `C = (π/2)²`.

Nothing is assumed at the endpoints `0`, `π/2` (no continuity, not even finiteness of the
extension): the standing hypothesis `(f')² ∈ L¹(Iθ)` forces `f' ∈ L¹(Iθ)`, and the fundamental
theorem of calculus between interior points then bounds `f` on `(0,π/2)`, which is what makes
`f` (and the mean-zero condition `∫₀^{π/2} f = 0`) a genuine, non-vacuous hypothesis.

The proof is the classical chain, all of whose ingredients already exist in the workspace
(`Submission/Work/FTS/EllipticEst/remov/coerc/weak_poincare_second.lean`):

* `f' ∈ L¹(Iθ)` from `(f')² ∈ L¹(Iθ)`  (`integrableOn_of_integrableOn_sq`);
* `|f x| ≤ |f (π/4)| + ∫_{Iθ} |f'|` on `(0,π/2)` by the FTC between interior points
  (`sub_eq_intervalIntegral`), whence `f` is bounded, hence integrable, on the slice;
* the mean-zero representation of a point value as a difference of integrals
  (`abs_le_integral_abs_deriv_of_mean_zero`) gives `|f x| ≤ ∫_{Iθ} |f'|` for `x ∈ (0,π/2)`;
  no zero of `f` has to be located, which is exactly what allows the weak endpoint behaviour;
* Cauchy–Schwarz (`sq_intervalIntegral_le`) turns that into the pointwise bound
  `(f x)² ≤ (π/2) ∫_{Iθ} (f')²`, and integrating over the slice of length `π/2` gives the
  constant `(π/2)²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W

theorem zeroMeanPoincare : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2) Work.Spaces.Iθ →
    (MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        ≤ C * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)) := by
  refine ⟨(Real.pi / 2) ^ 2, by positivity, fun f hf hmean hf2 => ?_⟩
  have hL : (0 : ℝ) < Real.pi / 2 := by positivity
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  -- ## `∂f` is continuous on `(0, π/2)`, hence integrable on the slice
  have hcw : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hg' : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.coerc.integrableOn_of_integrableOn_sq hL hcw hf2
  have hd : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.differentiableOn (by norm_num)
  have hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f x) x :=
    fun x hx => (hd.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  set K : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), |deriv f θ| with hK
  have hAbsInt : IntervalIntegrable (fun t => |deriv f t|) volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr (hg'.abs)
  have hp : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- ## Step 1: the fundamental-theorem bound `|f x| ≤ |f (π/4)| + K`
  have hfbound : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f x| ≤ |f (Real.pi / 4)| + K := by
    intro x hx
    have h2 : |f x - f (Real.pi / 4)| ≤ K := by
      rcases le_total (Real.pi / 4) x with h | h
      · have hsub : f x - f (Real.pi / 4) = ∫ t in (Real.pi / 4)..x, deriv f t :=
          Work.FTS.EllipticEst.remov.coerc.sub_eq_intervalIntegral hdiff hg' hp hx
        rw [hsub, hK]
        calc |∫ t in (Real.pi / 4)..x, deriv f t| ≤ ∫ t in (Real.pi / 4)..x, |deriv f t| :=
              intervalIntegral.abs_integral_le_integral_abs h
          _ ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), |deriv f t| :=
              intervalIntegral.integral_mono_interval hp.1.le h hx.2.le
                (Eventually.of_forall fun t => abs_nonneg _) hAbsInt
      · have hsub : f (Real.pi / 4) - f x = ∫ t in x..(Real.pi / 4), deriv f t :=
          Work.FTS.EllipticEst.remov.coerc.sub_eq_intervalIntegral hdiff hg' hx hp
        have he : f x - f (Real.pi / 4) = -(∫ t in x..(Real.pi / 4), deriv f t) := by linarith
        rw [he, abs_neg, hK]
        calc |∫ t in x..(Real.pi / 4), deriv f t| ≤ ∫ t in x..(Real.pi / 4), |deriv f t| :=
              intervalIntegral.abs_integral_le_integral_abs h
          _ ≤ ∫ t in (0 : ℝ)..(Real.pi / 2), |deriv f t| :=
              intervalIntegral.integral_mono_interval hx.1.le h hp.2.le
                (Eventually.of_forall fun t => abs_nonneg _) hAbsInt
    calc |f x| = |(f x - f (Real.pi / 4)) + f (Real.pi / 4)| := by ring_nf
      _ ≤ |f x - f (Real.pi / 4)| + |f (Real.pi / 4)| := abs_add_le _ _
      _ ≤ K + |f (Real.pi / 4)| := add_le_add_left h2 _
      _ = |f (Real.pi / 4)| + K := by ring
  -- ## Step 2: `f` is bounded on `(0, π/2)`, hence integrable on the slice
  have hfIoo_int : Integrable f (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hconstint : Integrable (fun _ : ℝ => |f (Real.pi / 4)| + K)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (μ := volume)
        (C := |f (Real.pi / 4)| + K) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine Integrable.mono' hconstint
      ((hf.continuousOn).aestronglyMeasurable measurableSet_Ioo) ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]
        exact hfbound x hx)
  have hg : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    show Integrable f (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2) (μ := volume))]
    exact hfIoo_int
  -- ## Step 3: the mean-zero bound `|f x| ≤ K`
  have haux := Work.FTS.EllipticEst.remov.coerc.abs_le_integral_abs_deriv_of_mean_zero
    (L := Real.pi / 2) hL hdiff hg hg' hmean
  have hpt1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f x) ^ 2 ≤ K ^ 2 := by
    intro x hx
    have h1 := haux x hx
    rw [← hK] at h1
    calc (f x) ^ 2 = |f x| ^ 2 := (sq_abs (f x)).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- ## Step 4: Cauchy–Schwarz, `K ^ 2 ≤ (π/2) * ∫_{Iθ} (f')²`
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 with hB
  have hsq : K ^ 2 ≤ (Real.pi / 2) * B := by
    have hLI2 : IntervalIntegrable (fun t => (|deriv f t|) ^ 2) volume (0 : ℝ) (Real.pi / 2) := by
      have h : (fun t => (|deriv f t|) ^ 2) = (fun t => (deriv f t) ^ 2) := by
        funext t
        rw [sq_abs]
      rw [h]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).mpr hf2
    have hcs := Work.FTS.EllipticEst.remov.coerc.sq_intervalIntegral_le hL.le hAbsInt hLI2
    have h2 : (∫ t in (0 : ℝ)..(Real.pi / 2), (|deriv f t|) ^ 2) = B := by
      rw [show (fun t => (|deriv f t|) ^ 2) = (fun t => (deriv f t) ^ 2) from by
            funext t; rw [sq_abs],
        intervalIntegral.integral_of_le hL.le, hB, hIθ,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [h2, sub_zero] at hcs
    rwa [← hK] at hcs
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f x) ^ 2 ≤ (Real.pi / 2) * B :=
    fun x hx => (hpt1 x hx).trans hsq
  -- ## Step 5: integrate the pointwise bound over the slice
  have hIntf : Integrable (fun x => (f x) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        (f x) ^ 2 ≤ (Real.pi / 2) * B :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hpt)
    have hIntconst : Integrable (fun _ : ℝ => (Real.pi / 2) * B)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (μ := volume)
        (C := (Real.pi / 2) * B) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine Integrable.mono' hIntconst
      (((hf.continuousOn).pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    exact hae.mono (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f x))]
      exact hx)
  have hmain : ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (f x) ^ 2 ≤ (Real.pi / 2) ^ 2 * B := by
    have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        (f x) ^ 2 ≤ (Real.pi / 2) * B :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hpt)
    have hIntconst : Integrable (fun _ : ℝ => (Real.pi / 2) * B)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (μ := volume)
        (C := (Real.pi / 2) * B) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hmono := MeasureTheory.integral_mono_ae hIntf hIntconst hae
    have hval : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * B))
        = (Real.pi / 2) * ((Real.pi / 2) * B) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le hL.le, sub_zero]
    calc ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (f x) ^ 2
        ≤ ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * B) := hmono
      _ = (Real.pi / 2) * ((Real.pi / 2) * B) := hval
      _ = (Real.pi / 2) ^ 2 * B := by ring
  -- ## Step 6: transfer from `(0, π/2)` back to the slice `Iθ = [0, π/2]`
  constructor
  · rw [hIθ]
    show Integrable (fun θ => f θ ^ 2) (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
    rw [← Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2) (μ := volume))]
    exact hIntf
  · rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact hmain

end Work.H2W
