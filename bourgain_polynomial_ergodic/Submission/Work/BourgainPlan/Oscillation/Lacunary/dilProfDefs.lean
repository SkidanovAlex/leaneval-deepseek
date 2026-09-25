import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.Lacunary.tscale_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.sqfn_no_per
import Submission.Work.BourgainPlan.Maximal.lintegral_rpow_pred_le

/-!
# The dilation-profile families of the oscillation reduction

This file fixes the vocabulary of the *profile reduction* (`dilation_profile_oscZ`): the
oscillation of the family of dilation-profile operators is to be reduced to

* the oscillation of the **sharp cut** family at a single level `t`, for which the hypothesis
  `hcut` of the reduction supplies a bound, and
* the square function of the **square-summable part** `H₂` of the profile.

The three families, all of them Fourier integrals against the probability measure
`mu01 = volume.restrict (Ioc 0 1)`:

* `profFam H r f T ρ i x = ∫_{θ ∈ (0,1]} r θ · H(⌊ρ^i⌋ θ) · P(θ) · e(-2πi x θ) dθ`, where
  `P = trigP T f`.  This is the family of the target (`H` the profile, `r` the weight).
* `profFamM` — the same as a `mu01`-integral (the form in which the Fubini argument is run).
* `cutFamM t r f T ρ i x = ∫_{θ ∈ (0,1]} r θ · 1_{θ ≤ t / ⌊ρ^i⌋} · P(θ) · e(-2πi x θ) dθ`, the
  family of the `hcut` hypothesis, written as a `mu01`-integral.

The bridge lemmas `profFam_eq_profFamM` and `cutFamM_eq_cutFam` identify the interval-integral
and the `mu01` formulations, and `cutFamM_eq_cutFam` identifies `cutFamM` with the (already
existing) family `Lacunary.cutFam` of `hcut`.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The **dilation-profile family**: `i ↦ x ↦ ∫_{θ ∈ (0,1]} r θ · H(⌊ρ^i⌋ θ) · P(θ) · e(-2πi x θ)`. -/
def profFam (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ

/-- `profFam` written as an integral against the probability measure `mu01`. -/
def profFamM (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ ∂mu01

/-- The **cut family at level `t`**, as an integral against `mu01`.  For `r` bounded by `cap` this
is exactly the family appearing in the hypothesis `hcut` of `dilation_profile_oscZ`. -/
def cutFamM (t : ℝ) (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) : ℂ :=
  ∫ θ, (r θ * (if θ ≤ t / (lacScale ρ i : ℝ) then (1:ℂ) else 0)) * trigP T f θ * Echar x θ ∂mu01

@[simp] lemma profFam_def (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) :
    profFam H r f T ρ i x
      = ∫ θ in (0:ℝ)..1, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ := rfl

@[simp] lemma profFamM_def (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) :
    profFamM H r f T ρ i x
      = ∫ θ, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ ∂mu01 := rfl

@[simp] lemma cutFamM_def (t : ℝ) (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ)
    (x : ℤ) :
    cutFamM t r f T ρ i x
      = ∫ θ, (r θ * (if θ ≤ t / (lacScale ρ i : ℝ) then (1:ℂ) else 0)) * trigP T f θ *
          Echar x θ ∂mu01 := rfl

/-- `mu01` is a probability measure. -/
instance isProbabilityMeasure_mu01 : IsProbabilityMeasure mu01 :=
  ⟨by rw [mu01, Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩

/-- The interval-integral and the `mu01` formulations of `profFam` agree. -/
lemma profFam_eq_profFamM (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ) (x : ℤ) :
    profFam H r f T ρ i x = profFamM H r f T ρ i x := by
  rw [profFam, profFamM, intervalIntegral_eq_mu01]

/-- `cutFamM` is the family `cutFam` of the `hcut` hypothesis, at the shift `t / ⌊ρ^i⌋`. -/
lemma cutFamM_eq_cutFam (t : ℝ) (r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ)
    (x : ℤ) :
    cutFamM t r f T ρ i x
      = cutFam r f T (fun i => t / (lacScale ρ i : ℝ)) i x := by
  rw [cutFamM, cutFam, intervalIntegral_eq_mu01]
  simp only [trigP, Echar]

/-- The `mu01` formulation of `profFam` as an interval integral. -/
lemma profFamM_eq_of_interval (H r : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (ρ : ℝ) (i : ℕ)
    (x : ℤ) :
    profFamM H r f T ρ i x
      = ∫ θ in (0:ℝ)..1, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ :=
  (profFam_eq_profFamM H r f T ρ i x).symm

end

end Work.BourgainPlan.Oscillation.Lacunary
