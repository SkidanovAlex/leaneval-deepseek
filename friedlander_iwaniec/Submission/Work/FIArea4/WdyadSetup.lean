import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Setup for the dyadic dual variance `Wdyad` (Friedlander–Iwaniec §11)

This module contains the definitions and elementary facts shared by the modules of the
`Wdyad` development (`Submission/Work/FIArea4/prop_11_1_W_dyad.lean`).  Nothing here is
`Wdyad`-specific: it is the *smooth majorant* used to replace the sharp `s`-interval
`(σ, 2σ]` by a rapidly decaying function, so that Poisson summation can be applied.

The majorant is the Gaussian

`gmajor σ x = exp (π/4) * exp (-π * ((x - 3σ/2)/σ)^2)`,

which is `≥ 1` on `(σ, 2σ]`, nonnegative everywhere, and whose Fourier transform is again a
Gaussian (hence decays faster than any power).
-/

namespace Work.FIArea4

open Finset
open scoped FourierTransform BigOperators

noncomputable section

/-- The Gaussian majorant of the interval `(σ, 2σ]`. -/
def gmajor (σ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (Real.pi / 4) * Real.exp (-(Real.pi) * ((x - 3 * σ / 2) / σ) ^ 2)

/-- The majorant as a complex-valued function (for the Fourier transform). -/
def gmajorC (σ : ℝ) : ℝ → ℂ := fun x => (gmajor σ x : ℂ)

/-- The entry `M ((d,a),(r,s))` of the variance matrix with `s` allowed to be any integer. -/
def MentryZ (d a r : ℕ) (s : ℤ) : ℂ :=
  if Nat.Coprime r d ∧ ((s : ZMod d) = (r : ZMod d) * (a : ZMod d))
  then (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0

/-- The class sum with `s : ℤ`. -/
def TZ (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (r : ℕ) (s : ℤ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, γ a d * MentryZ d a r s

lemma gmajor_nonneg (σ x : ℝ) : 0 ≤ gmajor σ x := by
  unfold gmajor; positivity

lemma gmajor_ge_one {σ x : ℝ} (hσ : 0 < σ) (h1 : σ ≤ x) (h2 : x ≤ 2 * σ) :
    1 ≤ gmajor σ x := by
  have hsq : ((x - 3 * σ / 2) / σ) ^ 2 ≤ 1 / 4 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - 3 * σ / 2), h1, h2, hσ]
  rw [gmajor, ← Real.exp_add]
  apply Real.one_le_exp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hsq, hpi]

lemma gmajor_contDiff (σ : ℝ) : ContDiff ℝ 2 (gmajor σ) := by
  unfold gmajor
  fun_prop

end

end Work.FIArea4
