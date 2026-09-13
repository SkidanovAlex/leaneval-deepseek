import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The Walsh character sum over `𝔽₂ⁿ`

For the standard additive character `χ = ZMod.stdAddChar` on `𝔽₂`, the sum over all
subsets `S ⊆ Fin n` of the product `∏_{i ∈ S} χ (z i)` equals `2 ^ n` when `z = 0`
and `0` otherwise:

`∑ S, ∏ i ∈ S, χ (z i) = if z = 0 then 2 ^ n else 0`.

The proof expands the sum over subsets into the product `∏ i, (1 + χ (z i))`
(the binomial/Fourier expansion of a product of `(1 + χ (z i))`), and evaluates each
factor using that `χ` is `1` at `0` and `-1` at `1` on `𝔽₂`.
-/

namespace Commons.Analysis.Walsh

open Finset BigOperators

/-- Expanding a sum of subset products: `∑_{S} ∏_{i ∈ S} f i = ∏_i (1 + f i)`. -/
lemma sum_prod_eq_prod_one_add {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ S : Finset ι, ∏ i ∈ S, f i) = ∏ i, (1 + f i) := by
  rw [show (∏ i, (1 + f i)) = ∏ i ∈ (Finset.univ : Finset ι), (1 + f i) from rfl]
  rw [Finset.prod_one_add, Finset.powerset_univ]

/-- `ZMod.stdAddChar` on `𝔽₂`: `1 + χ x` is `2` for `x = 0` and `0` for `x = 1`. -/
lemma one_add_stdAddChar (x : ZMod 2) :
    (1 : ℂ) + ZMod.stdAddChar x = if x = 0 then 2 else 0 := by
  rcases (show x = 0 ∨ x = 1 by revert x; decide) with h | h
  · subst h; norm_num
  · subst h
    rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    have h1 : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
      rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp]
      rw [ZMod.stdAddChar_coe (1 : ℤ)]
      rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 : ℤ) / (2 : ℕ) =
        Real.pi * Complex.I by push_cast; ring_nf]
      rw [Complex.exp_pi_mul_I]
    rw [h1]; norm_num

/-- A product of `if f i = 0 then c else 0` is `c ^ #ι` iff `f = 0` and `0` otherwise. -/
lemma prod_ite_eq_zero {ι : Type*} [Fintype ι] {M : ι → Type*} [∀ i, Zero (M i)]
    [∀ i, DecidableEq (M i)] (c : ℂ) (f : ∀ i, M i) :
    ∏ i, (if f i = 0 then c else 0) = if f = 0 then c ^ Fintype.card ι else 0 := by
  classical
  by_cases h : f = 0
  · subst h
    simp [Finset.prod_const]
  · obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (funext hc)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem sum_chi_index (n : ℕ) (z : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), ∏ i ∈ S, ZMod.stdAddChar (z i)) =
      if z = 0 then (2 : ℂ) ^ n else 0 := by
  rw [sum_prod_eq_prod_one_add]
  simp only [one_add_stdAddChar]
  rw [prod_ite_eq_zero]
  simp [Fintype.card_fin]

end Commons.Analysis.Walsh