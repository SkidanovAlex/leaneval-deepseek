/-
# `Submission.Work.FIArea5.S16Hecke.zfrAux`

Auxiliary definitions for the zero-free-region work of the Hecke `L`-function chapter: the
**principal strict character** `principalChar d` (the indicator of the units modulo `4d`), whose
Hecke `L`-series is `Σ_{(𝔞,4d)=1} N𝔞^{-s}` — the "ζ_K with the bad Euler factors removed" object
that plays the role of `ζ` in the classical de la Vallée Poussin `3-4-1` inequality for the Hecke
`L`-function of `ψ(z) = χ(z)(z/|z|)^m`.

This file is deliberately elementary and `sorry`-free (it is imported by the delegated lemmas of
the zero-free-region chapter, so that nothing above it can contain an unproved statement).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **The principal strict character modulo `4d`**: `1` on the units of `ℤ[i]/(4d)`, `0` elsewhere. -/
def principalChar (d : ℕ) : GaussianInt → ℂ := fun z => if IsUnitMod4d d z then 1 else 0

lemma principalChar_of_unit {d : ℕ} {z : GaussianInt} (h : IsUnitMod4d d z) :
    principalChar d z = 1 := by unfold principalChar; exact if_pos h

lemma principalChar_of_not_unit {d : ℕ} {z : GaussianInt} (h : ¬ IsUnitMod4d d z) :
    principalChar d z = 0 := by unfold principalChar; exact if_neg h

lemma isUnitMod4d_one (d : ℕ) : IsUnitMod4d d (1 : GaussianInt) :=
  ⟨1, by ring_nf; exact dvd_zero _⟩

lemma principalChar_one (d : ℕ) : principalChar d (1 : GaussianInt) = 1 :=
  principalChar_of_unit (isUnitMod4d_one d)

/-- The units modulo `4d` are closed under products (`z·w` invertible iff both factors are). -/
lemma isUnitMod4d_mul_iff {d : ℕ} {z w : GaussianInt} :
    IsUnitMod4d d (z * w) ↔ IsUnitMod4d d z ∧ IsUnitMod4d d w := by
  constructor
  · intro ⟨c, hc⟩
    refine ⟨⟨w * c, ?_⟩, ⟨z * c, ?_⟩⟩
    · simpa [mul_assoc] using hc
    · have h2 : z * w * c = w * (z * c) := by ring
      rwa [h2] at hc
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a * b, ?_⟩
    have h : z * w * (a * b) - 1 = (z * a - 1) * (w * b) + (w * b - 1) := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

lemma principalChar_mul (d : ℕ) (z w : GaussianInt) :
    principalChar d (z * w) = principalChar d z * principalChar d w := by
  by_cases hz : IsUnitMod4d d z <;> by_cases hw : IsUnitMod4d d w
  · rw [principalChar_of_unit (isUnitMod4d_mul_iff.mpr ⟨hz, hw⟩), principalChar_of_unit hz,
      principalChar_of_unit hw, mul_one]
  · rw [principalChar_of_not_unit (fun h => hw (isUnitMod4d_mul_iff.mp h).2),
      principalChar_of_unit hz, principalChar_of_not_unit hw, mul_zero]
  · rw [principalChar_of_not_unit (fun h => hz (isUnitMod4d_mul_iff.mp h).1),
      principalChar_of_not_unit hz, principalChar_of_unit hw, zero_mul]
  · rw [principalChar_of_not_unit (fun h => hz (isUnitMod4d_mul_iff.mp h).1),
      principalChar_of_not_unit hz, principalChar_of_not_unit hw, zero_mul]

lemma norm_principalChar_le_one (d : ℕ) (z : GaussianInt) : ‖principalChar d z‖ ≤ 1 := by
  by_cases h : IsUnitMod4d d z
  · rw [principalChar_of_unit h]; norm_num
  · rw [principalChar_of_not_unit h]; norm_num

/-- A multiple of `4d` is not a unit modulo `4d` (for `d ≥ 1`). -/
lemma not_isUnitMod4d_of_dvd {d : ℕ} (hd : 1 ≤ d) {z : GaussianInt}
    (h : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z) : ¬ IsUnitMod4d d z := by
  rintro ⟨a, ha⟩
  have hza : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z * a := dvd_mul_of_dvd_left h a
  have h1 : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (1 : GaussianInt) := by
    have hz : (1 : GaussianInt) = z * a - (z * a - 1) := by ring
    rw [hz]
    exact dvd_sub hza ha
  obtain ⟨b, hb⟩ := h1
  have hgn : Work.FIPlan.gnorm (1 : GaussianInt)
      = Work.FIPlan.gnorm (((((4 * d : ℕ) : ℤ) : GaussianInt)) * b) := by rw [hb]
  rw [gnorm_mul, gnorm_one] at hgn
  have h4 : Work.FIPlan.gnorm (((((4 * d : ℕ) : ℤ) : GaussianInt))) = (4 * d) ^ 2 := by
    simp [Work.FIPlan.gnorm, Zsqrtd.norm_def, Int.natAbs_mul, Int.natAbs_natCast, pow_two]
  rw [h4] at hgn
  have hpos : 1 ≤ Work.FIPlan.gnorm b := by
    rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm b) with h0 | h0
    · rw [h0, mul_zero] at hgn
      exact absurd hgn (by norm_num)
    · exact h0
  have hgn' : (1 : ℝ) = ((4 * d) ^ 2 : ℝ) * (Work.FIPlan.gnorm b : ℝ) := by exact_mod_cast hgn
  have hb1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm b : ℝ) := by exact_mod_cast hpos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith [sq_nonneg (4 * (d : ℝ))]

lemma principalChar_periodic {d : ℕ} {z w : GaussianInt}
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (z - w)) :
    principalChar d z = principalChar d w := by
  have key : IsUnitMod4d d z ↔ IsUnitMod4d d w := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have : w * a - 1 = (z * a - 1) - (z - w) * a := by ring
      rw [this]
      exact dvd_sub ha (dvd_mul_of_dvd_left h a)
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      have : z * a - 1 = (w * a - 1) + (z - w) * a := by ring
      rw [this]
      exact dvd_add ha (dvd_mul_of_dvd_left h a)
  by_cases hz : IsUnitMod4d d z
  · rw [principalChar_of_unit hz, principalChar_of_unit (key.mp hz)]
  · rw [principalChar_of_not_unit hz, principalChar_of_not_unit (fun hw => hz (key.mpr hw))]

/-- The squared character `χ²`, as a function on `ℤ[i]`. -/
def chiSq (chi : GaussianInt → ℂ) : GaussianInt → ℂ := fun z => chi z * chi z

/-- `-Re (f'(s)/f(s))`, the quantity bounded in the zero-free-region arguments. -/
def negLogDerivRe (f : ℂ → ℂ) (s : ℂ) : ℝ := ((- deriv f s) / f s).re

end

end Work.FIArea5.S16Hecke
