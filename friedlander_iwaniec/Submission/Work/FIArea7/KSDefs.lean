/-
# `Submission.Work.FIArea7.KSDefs` — the `r`-decomposition of the linear form `K(N)`

This file opens the proof of *FI* Proposition 22.1 (`Work.FIArea7.KSum_bound`): the box sum
`KLinear Rz w k chi = Σ∧_{z ∈ gBox Rz} ψ(z)[wz]` is rewritten as an iterated sum over the real part
`r` of `z` (`KInner Rz w k chi r`), which is the form in which the Pólya–Vinogradov estimate is
applied (for fixed `r` the sum over `s = Im z` is a character sum in `s`).

The estimate of `KInner` itself lives in `Submission/Work/FIArea7/KInner_bound.lean`; the final
assembly in `Submission/Work/FIArea7/KSum_bound.lean`.
-/
import Mathlib
import Submission.Work.FIArea7.Prop172
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The inner sum of `Work.FIArea7.KLinear` over the fibre of `z.re = r`: for fixed real part `r`,
the primary `z = r + i s` of the box `|s| ≤ Rz` contribute `ψ(z)[wz]`. -/
def KInner (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ) (r : ℤ) : ℂ :=
  ∑ s ∈ Finset.Icc (-Rz) Rz,
    (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) then
      grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)

/-- `‖ψ(z)‖ ≤ ‖χ z‖ ≤ 1` for `z ≠ 0`: the Hecke character (17.17) has unit modulus. -/
theorem norm_grossenChar_le (chi : GaussianInt → ℂ) (k : ℤ) {z : GaussianInt} (hz : z ≠ 0) :
    ‖grossenChar chi k z‖ ≤ ‖chi z‖ := by
  have hzC : (z : ℂ) ≠ 0 := fun h => hz (GaussianInt.toComplex_injective (by simpa using h))
  have hnorm : ‖(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (by simpa using hzC)
  rw [grossenChar, norm_mul, norm_zpow, hnorm, one_zpow, mul_one]

/-- `‖ψ(z)‖ ≤ 1` for every `z`, provided `‖χ‖ ≤ 1`. -/
theorem norm_grossenChar_le_one (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (z : GaussianInt) :
    ‖grossenChar chi k z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [grossenChar]
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using hchi 0
    · rw [show ((0 : GaussianInt) : ℂ) / ((‖((0 : GaussianInt) : ℂ)‖ : ℝ) : ℂ) = 0 by simp,
        zero_zpow _ hk, mul_zero, norm_zero]
      norm_num
  · exact le_trans (norm_grossenChar_le chi k hz) (hchi z)

end

end Work.FIArea7
