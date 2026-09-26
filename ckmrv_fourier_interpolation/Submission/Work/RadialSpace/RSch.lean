import Mathlib
import Submission.Work.RadialSpace.Profile
import Submission.Work.RadialSpace.RadialDeriv
import Submission.Work.RadialSpace.radialSeminorm_le_seminorm
import Submission.Work.Sampling.coeffs_continuous_linear

/-!
# Radial Schwartz functions and their profiles

This file collects the interface between the challenge's own vocabulary
(`RadialSchwartz`, `coeffs`, `Work.Core.RSch`) and the profile map: the profile of
a radial Schwartz function is an even Schwartz function of one variable, the
radial samples of `coeffs` are samples of the profile, and the radial seminorms
of a Schwartz function are bounded by its Schwartz seminorms.

## Main results

* `Work.RadialSpace.rschProfile`: the profile of a radial Schwartz function.
* `Work.RadialSpace.coeffs_zero`, `Work.RadialSpace.coeffs_two`: the value and
  radial-derivative samples of `coeffs` are samples of the profile.
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal FourierTransform

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core

variable {n : ℕ} [NeZero n]

/-- The profile of a radial Schwartz function: an even Schwartz function of one
variable. -/
noncomputable def rschProfile (f : RSch n) : 𝓢(ℝ, ℂ) := profileCLM f.1

lemma rschProfile_apply (f : RSch n) (r : ℝ) : rschProfile f r = f.1 (realIncl r) := by
  simp [rschProfile]

lemma rschProfile_coe (f : RSch n) : ⇑(rschProfile f) = profile f.1 := by
  simp [rschProfile]

lemma rschProfile_even (f : RSch n) (t : ℝ) : rschProfile f (-t) = rschProfile f t :=
  profile_even f.2 t

lemma rschProfile_eq (f : RSch n) (x : EuclideanSpace ℝ (Fin n)) :
    f.1 x = rschProfile f ‖x‖ := by
  rw [rschProfile_coe]
  exact profile_eq_of_radial f.2 x

/-- Odd iterated derivatives of the profile of a radial Schwartz function vanish
at the origin. -/
lemma iteratedDeriv_rschProfile_odd_zero (f : RSch n) {m : ℕ} (hm : Odd m) :
    iteratedDeriv m (rschProfile f) 0 = 0 := by
  rw [rschProfile_coe]
  exact iteratedDeriv_profile_odd_zero f.2 hm

/-- The value samples of `coeffs` are samples of the profile. -/
lemma coeffs_zero (k₀ : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 0) = profile f (Real.sqrt (2 * (k : ℝ))) := rfl

/-- The radial-derivative samples of `coeffs` are derivatives of the profile. -/
lemma coeffs_two (k₀ : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 2) = deriv (profile f) (Real.sqrt (2 * (k : ℝ))) := rfl

/-- The radial-derivative samples of `coeffs`, as the first radial derivative of
`f` at the axis point. -/
lemma coeffs_two_radialDeriv (k₀ : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 2) = radialDeriv f (realIncl (Real.sqrt (2 * (k : ℝ)))) := by
  rw [coeffs_two, radialDeriv_apply, Work.Sampling.realIncl_norm,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The Fourier samples of `coeffs` are samples of the profile of the Fourier
transform, once radiality is known for the latter. -/
lemma coeffs_one (k₀ : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 1) =
      profile (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
        (Real.sqrt (2 * (k : ℝ))) := rfl

/-- For an even function `g` of one variable, the radial seminorms of
`x ↦ g ‖x‖` are the one-variable seminorms `sup_r |r| ^ k ‖g^{(l)}(r)‖`. -/
lemma radialSeminorm_comp_norm {g : ℝ → ℂ} (he : Function.Even g) (k l : ℕ) :
    radialSeminorm (n := n) k l (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) =
      ⨆ r : ℝ, ENNReal.ofReal (|r| ^ k * ‖iteratedDeriv l g r‖) := by
  have hprof : profile (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) = g := by
    funext r
    rw [profile_comp_norm]
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr]
      exact he r
  have hnorm : ∀ r : ℝ, ‖iteratedDeriv l g (-r)‖ = ‖iteratedDeriv l g r‖ := by
    intro r
    have h1 : iteratedDeriv l g r = (-1 : ℝ) ^ l • iteratedDeriv l g (-r) := by
      have h := iteratedDeriv_comp_neg l g r
      rw [show (fun x : ℝ => g (-x)) = g from funext he] at h
      exact h
    rw [h1, norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [radialSeminorm, hprof]
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun r => ?_)
  · refine le_iSup_of_le ‖x‖ ?_
    simp only [abs_of_nonneg (norm_nonneg x), le_refl]
  · rcases le_total 0 r with hr | hr
    · refine le_iSup_of_le (realIncl (n := n) r) ?_
      simp only [Work.Sampling.realIncl_norm, abs_of_nonneg hr, le_refl]
    · have hr' : (0 : ℝ) ≤ -r := by linarith
      refine le_iSup_of_le (realIncl (n := n) (-r)) ?_
      simp only [Work.Sampling.realIncl_norm, abs_of_nonneg hr', abs_of_nonpos hr, hnorm r,
        le_refl]

/-- The third sample sequence of `coeffs` (the radial derivative of the Fourier
transform) is the derivative of the profile of the Fourier transform. -/
lemma coeffs_three (k₀ : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k : Set.Ici k₀) :
    coeffs n k₀ f (k, 3) = deriv (profile (⇑(FourierTransform.fourierCLM ℂ
      (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))) (Real.sqrt (2 * (k : ℝ))) := rfl

/-- The radial seminorms of a Schwartz function are bounded by its Schwartz
seminorms, so they are finite. -/
lemma radialSeminorm_lt_top (G : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (k l : ℕ) :
    radialSeminorm k l (⇑G) < ⊤ :=
  lt_of_le_of_lt (radialSeminorm_le_seminorm G k l) ENNReal.ofReal_lt_top

end Work.RadialSpace
