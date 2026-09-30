import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite support of a signed positive logarithm over the finite places

Let `L` be a number field and `x ∈ L`, `x ≠ 0`.  A finite place `w` of `L` is an
absolute value `L → ℝ`, and for all but finitely many `w` one has `w x = 1`
(`NumberField.FinitePlace.hasFiniteMulSupport`).  Consequently the function

`w ↦ log⁺ (w x)`  (and likewise `w ↦ log⁺ ((w x)⁻¹)`)

vanishes outside that finite set, because `log⁺ 1 = 0`.  Multiplying by an
arbitrary real constant `D` and replacing `w x` by its inverse according to the
sign of an integer `s` therefore still has finite support; this is the content of
`finplace_posLog_sgn_support`.

This is used in the proof of the Baker–Wüstholz theorem to take the logarithm of
a product over the finite places, only finitely many of whose factors differ
from `1`.
-/

namespace Work.BW

/-- For `x ≠ 0` in a number field `L`, the function sending a finite place `w` to
`D * log⁺ (w x)` when `0 ≤ s` and to `D * log⁺ ((w x)⁻¹)` when `s < 0` has finite
support. -/
theorem finplace_posLog_sgn_support {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0)
    (s : ℤ) (D : ℝ) :
    Function.HasFiniteSupport (fun w : NumberField.FinitePlace L =>
      D * (if 0 ≤ s then w x else (w x)⁻¹).posLog) := by
  -- All but finitely many finite places satisfy `w x = 1`.
  have hms : (fun w : NumberField.FinitePlace L => w x).HasFiniteMulSupport :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  -- The support of the signed positive logarithm is contained in that finite set.
  have h1 : (Function.support fun w : NumberField.FinitePlace L =>
      (if 0 ≤ s then w x else (w x)⁻¹).posLog) ⊆
      Function.mulSupport (fun w : NumberField.FinitePlace L => w x) := by
    intro w hw
    rw [Function.support, Set.mem_ofPred_eq] at hw
    rw [Function.mulSupport, Set.mem_ofPred_eq]
    by_cases hs : 0 ≤ s
    · rw [ite_eq_left hs] at hw
      intro hwx
      exact hw (by rw [hwx]; simp)
    · rw [ite_eq_right hs] at hw
      intro hwx
      exact hw (by rw [hwx]; simp)
  have hfin : (fun w : NumberField.FinitePlace L =>
      (if 0 ≤ s then w x else (w x)⁻¹).posLog).HasFiniteSupport := hms.subset h1
  -- Multiplying by the constant `D` does not increase the support.
  exact hfin.smul_right (fun _ : NumberField.FinitePlace L => D)

end Work.BW
