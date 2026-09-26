import Mathlib
import Submission.Work.RadialSpace.Basic

/-!
# Radiality via the profile: CKMRV Lemma 2.6

The main result of this file is the equivalence (Lemma 2.6 of CKMRV) identifying
radial Schwartz functions on `R^n` with the even Schwartz functions of one
variable, by composition with the norm:

`Radial f ↔ ∃ g : 𝓢(ℝ, ℂ), (∀ t, g (-t) = g t) ∧ ∀ x, f x = g ‖x‖`.

The forward direction is the profile map `f ↦ f ∘ realIncl` (which is a
continuous linear map on Schwartz spaces, `profileCLM`).  The backward direction
only needs the elementary observation that `x ↦ g ‖x‖` is radial when `g` is
even; the additional fact that `x ↦ g ‖x‖` is *Schwartz* when `g` is even
Schwartz (equivalently: an even smooth function of one variable is a smooth
function of the square) is proved separately, see
`Work.RadialSpace.exists_schwartz_comp_norm`.

## Main results

* `Work.RadialSpace.radial_iff_exists_even_profile`
-/

open Filter Topology
open scoped SchwartzMap Topology ContDiff ENNReal

namespace Work.RadialSpace

open LeanEval.Analysis.CKMRVInterpolation

variable {n : ℕ} [NeZero n]

/-- The profile of a function of the norm: `profile (g ∘ ‖·‖) r = g |r|`. -/
lemma profile_comp_norm {n : ℕ} [NeZero n] {g : ℝ → ℂ} (r : ℝ) :
    profile (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) r = g |r| := by
  rw [profile_apply, Work.Sampling.realIncl_norm]

/-- A function of the norm is radial. -/
lemma radial_comp_norm {n : ℕ} {g : ℝ → ℂ} :
    Radial (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) :=
  fun _ _ h => by simp only [h]

/-- **CKMRV Lemma 2.6.** A complex Schwartz function on `R^n` is radial iff it is
the composition of an even Schwartz function of one variable with the norm. -/
theorem radial_iff_exists_even_profile (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Radial f ↔ ∃ g : 𝓢(ℝ, ℂ), (∀ t, g (-t) = g t) ∧ ∀ x, f x = g ‖x‖ := by
  constructor
  · intro hf
    exact ⟨profileCLM f, profile_even hf, fun x => (profile_eq_of_radial hf x).trans
      (by rw [profileCLM_apply])⟩
  · rintro ⟨g, hg, hfg⟩
    rw [show (⇑f : EuclideanSpace ℝ (Fin n) → ℂ) = fun x => g ‖x‖ from funext hfg]
    exact radial_comp_norm

end Work.RadialSpace
