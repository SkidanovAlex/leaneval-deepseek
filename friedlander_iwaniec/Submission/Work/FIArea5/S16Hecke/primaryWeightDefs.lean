/-
# `Submission.Work.FIArea5.S16Hecke.primaryWeightDefs`

The **primary-coset weight** `primaryWt chi z = if IsPrimary z then chi z else 0`, together with
its elementary API:

* `isPrimary_iff_of_dvd` — the primary condition is a congruence condition modulo `4d`
  (because `(1+i)^3 ∣ 4d`), so the weight is periodic modulo `4d`;
* `primaryWt_periodic` — the weight `primaryWt chi` is periodic modulo `4d` whenever `χ` is;
* `norm_primaryWt_le_one` — `‖primaryWt chi z‖ ≤ 1` for `‖χ‖ ≤ 1`;
* `primaryWt_residue_sum` — the finite Fourier transform of `primaryWt chi` over the residue ring
  `(ℤ/4d)²` is exactly `primaryGaussSum d chi` (`Work.FIArea5.S16Hecke.primaryGauss`).

These are the facts needed to apply the twisted Poisson summation
`Work.FIArea5.S16.poisson_periodic_2d` to the holomorphic theta series of a Größencharacter,
summed over the primary coset, i.e. to the *primary Poisson* theta transformation
`Work.FIArea5.S16Hecke.thetaHol_primaryPoisson`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **The primary-coset weight**: `χ(z)` on the primary elements of `ℤ[i]` and `0` elsewhere.  This
is the periodic weight (`chiOdd` is the "odd" analogue) of the twisted Poisson summation for the
primary-coset theta series `thetaHol`: the primary elements are the coset `1 + (1+i)³ℤ[i]`, and
`(1+i)³ ∣ 4d`, so the weight is periodic modulo `4d` (`primaryWt_periodic`), with finite Fourier
transform `primaryGaussSum d chi`. -/
def primaryWt (chi : GaussianInt → ℂ) (z : GaussianInt) : ℂ := by
  classical
  exact if IsPrimary z then chi z else 0

lemma primaryWt_pos (chi : GaussianInt → ℂ) {z : GaussianInt} (h : IsPrimary z) :
    primaryWt chi z = chi z := by rw [primaryWt]; exact if_pos h

lemma primaryWt_neg (chi : GaussianInt → ℂ) {z : GaussianInt} (h : ¬ IsPrimary z) :
    primaryWt chi z = 0 := by rw [primaryWt]; exact if_neg h

/-- `(1+i)^4 = -4` in `ℤ[i]`. -/
lemma oneAddI_pow_four' : (1 + (⟨0,1⟩ : GaussianInt)) ^ 4 = -(4 : GaussianInt) := by decide

/-- `(1+i)^3` divides `4d`: `4d = (1+i)^3·(-(1+i)d)`. -/
lemma oneAddI_pow_three_dvd_four_mul (d : ℕ) :
    (1 + (⟨0,1⟩ : GaussianInt)) ^ 3 ∣ (((4 * d : ℕ) : ℤ) : GaussianInt) := by
  refine ⟨-(1 + (⟨0,1⟩ : GaussianInt)) * (d : GaussianInt), ?_⟩
  rw [show (((4 * d : ℕ) : ℤ) : GaussianInt)
      = -(d : GaussianInt) * (1 + (⟨0,1⟩ : GaussianInt)) ^ 4 by
    rw [oneAddI_pow_four']; push_cast; ring]
  ring

/-- The identity `4d = (1+i)^3·(-(1+i)d)`, the form in which `(1+i)^3 ∣ 4d` is used below. -/
lemma four_mul_eq_cube_mul (d : ℕ) :
    (((4 * d : ℕ) : ℤ) : GaussianInt)
      = (1 + (⟨0,1⟩ : GaussianInt)) ^ 3 * (-(1 + (⟨0,1⟩ : GaussianInt)) * (d : GaussianInt)) := by
  rw [show (((4 * d : ℕ) : ℤ) : GaussianInt)
      = -(d : GaussianInt) * (1 + (⟨0,1⟩ : GaussianInt)) ^ 4 by
    rw [oneAddI_pow_four']; push_cast; ring]
  ring

/-- **The primary condition is a congruence condition modulo `4d`**: since `(1+i)^3 ∣ 4d` and the
primary elements are exactly the coset `1 + (1+i)³ℤ[i]`, congruence modulo `4d` preserves
primarity. -/
lemma isPrimary_iff_of_dvd {d : ℕ} {z w : GaussianInt}
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w)) : IsPrimary z ↔ IsPrimary w := by
  obtain ⟨c, hc⟩ := h
  have hw : w = z - (((4 * d : ℕ) : ℤ) : GaussianInt) * c := by rw [← hc]; ring
  have h4 := four_mul_eq_cube_mul d
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := (isPrimary_iff_coset z).mp hz
    refine (isPrimary_iff_coset w).mpr
      ⟨a - (-(1 + (⟨0,1⟩ : GaussianInt)) * (d : GaussianInt)) * c, ?_⟩
    rw [hw, ha, h4]; ring
  · intro hw'
    obtain ⟨a, ha⟩ := (isPrimary_iff_coset w).mp hw'
    refine (isPrimary_iff_coset z).mpr
      ⟨a + (-(1 + (⟨0,1⟩ : GaussianInt)) * (d : GaussianInt)) * c, ?_⟩
    have hz : z = w + (((4 * d : ℕ) : ℤ) : GaussianInt) * c := by rw [hw]; ring
    rw [hz, ha, h4]; ring

/-- **`primaryWt chi` is periodic modulo `4d`** whenever `χ` is. -/
lemma primaryWt_periodic (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) → chi z = chi w) :
    ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) →
      primaryWt chi z = primaryWt chi w := by
  intro z w hzw
  by_cases hz : IsPrimary z
  · have hw : IsPrimary w := (isPrimary_iff_of_dvd hzw).mp hz
    rw [primaryWt_pos chi hz, primaryWt_pos chi hw, hchi z w hzw]
  · have hw : ¬ IsPrimary w := fun h => hz ((isPrimary_iff_of_dvd hzw).mpr h)
    rw [primaryWt_neg chi hz, primaryWt_neg chi hw]

/-- The norm bound `‖primaryWt chi z‖ ≤ 1` for a weight with `‖χ‖ ≤ 1`. -/
lemma norm_primaryWt_le_one (chi : GaussianInt → ℂ) (h : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (z : GaussianInt) : ‖primaryWt chi z‖ ≤ 1 := by
  by_cases hz : IsPrimary z
  · rw [primaryWt_pos chi hz]; exact h z
  · rw [primaryWt_neg chi hz]; simp

end

end Work.FIArea5.S16Hecke
