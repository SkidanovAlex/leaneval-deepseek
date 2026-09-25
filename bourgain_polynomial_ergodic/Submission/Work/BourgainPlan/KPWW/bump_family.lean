import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The explicit smooth bump family of the `family_bound_of_thm19` derivation

The target `Work.BourgainPlan.KPWW.family_bound_of_thm19` needs, for every `1 < p < ∞`, a family
`φ : ℕ → ℤ → 𝕋 → ℂ` of bumps of dyadic scale such that the Ionescu–Wainger projections
`opArc (φ l m) (canonicalFinset (2^l))` are `ℓᵖ`-bounded with the loss `2^{Cγl}`, uniformly in the
scale `2^m`.

The family used here is built from a **fixed** profile `trapProfile` (the trapezoid which is `1` on
`[-1/4,1/4]` and decreases linearly to `0` at `|x| = 1/2`) by dilation:

`circleBump m θ = trapProfile (‖θ‖ / 2^m)`.

Its advantage over the bump `η` of the ambient statement is that its Fourier coefficients are
**summable uniformly in the scale** (`λ ↦ λ·\hatψ(λ·)` has a bounded `ℓ¹` norm, because the
explicit Fourier transform `\hatψ(s) = 2(cos(πs/2) - cos(πs))/(π²s²)` decays like `s^{-2}`), which
is what makes (a) the discrete `ℓᵖ` bound (kernel + Young) available uniformly in the scale and
(b) the continuous `Lᵖ(ℝ)` bound for the *periodic* multiplier available with a constant
independent of the scale.

This file contains the definition and the elementary pointwise properties; the two analytic
lemmas used by the derivation are delegated separately:
* `circleBumpCoeff_summable_bound` — the uniform `ℓ¹` bound on the Fourier coefficients;
* `circleBump_fourier_series` — the pointwise (absolutely convergent) Fourier series.
-/

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.KPWW

noncomputable section

/-! ## The trapezoid profile -/

/-- The trapezoid profile: `1` on `[-1/4,1/4]`, decreasing linearly to `0` at `|x| = 1/2`, and `0`
outside `[-1/2,1/2]`.  It is even, continuous, bounded by `1`, and its Fourier transform is
`\hatψ(s) = 2(cos(πs/2) - cos(πs))/(π²s²)` (`s ≠ 0`), whence `|\hatψ(s)| ≤ 4/(π²s²)` and
`|\hatψ(s)| ≤ 3/4`. -/
def trapProfile (x : ℝ) : ℝ := min 1 (max 0 (2 - 4 * |x|))

lemma trapProfile_even (x : ℝ) : trapProfile (-x) = trapProfile x := by
  simp [trapProfile, abs_neg]

lemma trapProfile_nonneg (x : ℝ) : 0 ≤ trapProfile x := by
  have h : (0:ℝ) ≤ max 0 (2 - 4 * |x|) := le_max_left _ _
  exact le_min (by norm_num) h

lemma trapProfile_le_one (x : ℝ) : trapProfile x ≤ 1 := min_le_left _ _

lemma trapProfile_eq_one {x : ℝ} (h : |x| ≤ 1/4) : trapProfile x = 1 := by
  have h1 : (1:ℝ) ≤ 2 - 4 * |x| := by linarith [abs_nonneg x]
  rw [trapProfile, max_eq_right (by linarith : (0:ℝ) ≤ 2 - 4 * |x|), min_eq_left h1]

lemma trapProfile_eq_zero {x : ℝ} (h : 1/2 ≤ |x|) : trapProfile x = 0 := by
  have h1 : (2:ℝ) - 4 * |x| ≤ 0 := by linarith
  rw [trapProfile, max_eq_left h1, min_eq_right (by norm_num)]

lemma continuous_trapProfile : Continuous trapProfile := by
  unfold trapProfile
  fun_prop

lemma measurable_trapProfile : Measurable trapProfile := continuous_trapProfile.measurable

/-! ## The circle bump family -/

/-- **The bump of scale `2^m`** on the circle: `circleBump m θ = trapProfile (‖θ‖ / 2^m)`, a
function supported in the ball of radius `2^m/2` around `0` and equal to `1` on the ball of radius
`2^m/4`. -/
def circleBump (m : ℤ) : Work.BourgainPlan.IonescuWainger.Circle → ℂ :=
  fun θ => (trapProfile (‖θ‖ / (2 : ℝ) ^ m) : ℂ)

@[simp] lemma circleBump_apply (m : ℤ) (θ : Work.BourgainPlan.IonescuWainger.Circle) :
    circleBump m θ = (trapProfile (‖θ‖ / (2 : ℝ) ^ m) : ℂ) := rfl

lemma norm_circleBump_le (m : ℤ) (θ : Work.BourgainPlan.IonescuWainger.Circle) :
    ‖circleBump m θ‖ ≤ 1 := by
  rw [circleBump_apply, Complex.norm_of_nonneg (trapProfile_nonneg _)]
  exact trapProfile_le_one _

lemma circleBump_eq_one (m : ℤ) {θ : Work.BourgainPlan.IonescuWainger.Circle}
    (h : ‖θ‖ ≤ (2 : ℝ) ^ m / 4) : circleBump m θ = 1 := by
  have hpos : (0:ℝ) < (2:ℝ)^m := zpow_pos (by norm_num) m
  have h1 : |‖θ‖ / (2:ℝ)^m| ≤ 1/4 := by
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le), div_le_iff₀ hpos]
    linarith
  rw [circleBump_apply, trapProfile_eq_one h1, Complex.ofReal_one]

lemma circleBump_eq_zero (m : ℤ) {θ : Work.BourgainPlan.IonescuWainger.Circle}
    (h : (2 : ℝ) ^ m / 2 < ‖θ‖) : circleBump m θ = 0 := by
  have hpos : (0:ℝ) < (2:ℝ)^m := zpow_pos (by norm_num) m
  have h1 : 1/2 ≤ |‖θ‖ / (2:ℝ)^m| := by
    rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le), le_div_iff₀ hpos]
    linarith
  rw [circleBump_apply, trapProfile_eq_zero h1, Complex.ofReal_zero]

lemma continuous_circleBump (m : ℤ) :
    Continuous (circleBump m : Work.BourgainPlan.IonescuWainger.Circle → ℂ) := by
  rw [show (circleBump m : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
      = fun θ => (trapProfile (‖θ‖ / (2 : ℝ) ^ m) : ℂ) from rfl]
  exact Complex.continuous_ofReal.comp
    (continuous_trapProfile.comp (continuous_norm.div_const _))

lemma measurable_circleBump (m : ℤ) :
    Measurable (circleBump m : Work.BourgainPlan.IonescuWainger.Circle → ℂ) :=
  (continuous_circleBump m).measurable

lemma circleBump_memLp (m : ℤ) :
    MemLp (circleBump m) ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  memLp_top_of_bound (measurable_circleBump m).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_circleBump_le m))

/-! ## The Fourier coefficients -/

/-- The `n`-th Fourier coefficient of the circle bump of scale `2^m`,
`∫_𝕋 circleBump m θ · star (fourier n θ) dθ`. -/
def circleBumpCoeff (m : ℤ) (n : ℤ) : ℂ :=
  ∫ θ : Work.BourgainPlan.IonescuWainger.Circle,
    circleBump m θ * star (fourier n θ) ∂(AddCircle.haarAddCircle (T := 1))

end

end Work.BourgainPlan.KPWW
