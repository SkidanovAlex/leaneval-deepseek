import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The Walsh character sum over the coordinates of `𝔽₂^ι`

For the standard additive character `χ = ZMod.stdAddChar` on `𝔽₂` and a set `A` of
coordinates, the sum over all `y : ι → ZMod 2` of the "coordinate character"
`∏_{i ∈ A} χ (y i)` is `2 ^ #ι` when `A = ∅` and `0` otherwise:

`∑ y, ∏ i, (if i ∈ A then χ (y i) else 1) = if A = ∅ then 2 ^ #ι else 0`.

The product over `ι` is an exact product of a sum over the product type (Fubini for the
coordinate functions), each factor `∑ a, (if i ∈ A then χ a else 1)` being `2` for
`i ∉ A` and `∑ a, χ a = 0` for `i ∈ A` (as `χ` is a non-trivial character).

This is the "all-one vector" character sum used in the Walsh/Fourier analysis of the
pseudorandom-Grassmann setup.
-/

namespace Commons.Analysis.Walsh

open Finset BigOperators

/-- Interchange a sum over a dependent product type `∀ i, κ i` with a product over the
coordinates: `∑ g, ∏ i, f i (g i) = ∏ i, ∑ a, f i a`. -/
lemma sum_prod_pi' {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    ∑ g : (∀ i, κ i), ∏ i, f i (g i) = ∏ i, ∑ a, f i a := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ i))) f]
  simp

/-- The sum of the standard additive character on `𝔽₂` over the whole group vanishes. -/
lemma sum_stdAddChar_two : (∑ a : ZMod 2, ZMod.stdAddChar a) = (0 : ℂ) := by
  have h := AddChar.sum_mulShift (1 : ZMod 2) (ZMod.isPrimitive_stdAddChar 2)
    (ψ := ZMod.stdAddChar)
  simpa using h

/-- A product over `ι` of the indicator factors `if i ∈ A then 0 else c` is `c ^ #ι` when
`A = ∅` and `0` otherwise. -/
lemma prod_ite_mem_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (c : ℂ) :
    ∏ i, (if i ∈ A then 0 else c) = if A = ∅ then c ^ Fintype.card ι else 0 := by
  classical
  by_cases hA : A = ∅
  · subst hA
    simp [Finset.prod_const]
  · rw [if_neg hA]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_pos hi)

theorem sum_coord_chi {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    (∑ y : ι → ZMod 2, ∏ i : ι, (if i ∈ A then ZMod.stdAddChar (y i) else 1))
      = if A = ∅ then (2 : ℂ) ^ (Fintype.card ι) else 0 := by
  classical
  rw [sum_prod_pi' (fun i (a : ZMod 2) => if i ∈ A then ZMod.stdAddChar a else 1)]
  have h : ∀ i, (∑ a : ZMod 2, (if i ∈ A then ZMod.stdAddChar a else 1))
      = if i ∈ A then 0 else 2 := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, if_true]
      exact sum_stdAddChar_two
    · simp only [hi, if_false]
      norm_num
  rw [Finset.prod_congr rfl (fun i _ => h i)]
  exact prod_ite_mem_zero A 2

end Commons.Analysis.Walsh