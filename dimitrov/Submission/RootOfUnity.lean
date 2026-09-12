import Mathlib
import Submission.ConjPoly
import Submission.Minpoly
import Submission.Dictionary
import Submission.Conjugates
import Submission.Powers
import Submission.RootProd

/-!
# From `pow4 = pow2` (of the minimal polynomial) to "`α` is a root of unity"

This module closes the algebraic dichotomy (Layer C).  Over `ℂ`, the identity
`pow4 P = pow2 P` (with `P := minpoly ℤ α`) means the multiset `{z⁴ : z ∈ S}`
of fourth powers of the conjugates equals the multiset `{z² : z ∈ S}` of
squares.  Taking maximal moduli then forces every conjugate to lie on the
closed unit disk; Kronecker's theorem
(`NumberField.Embeddings.pow_eq_one_of_norm_le_one`) turns that into
`IsOfFinOrder α`.

## Proof plans

`pow4_eq_pow2_imp_house_le_one`:
1. Map the equality `pow4 P = pow2 P` to `ℂ` (`congrArg (Polynomial.map (algebraMap ℤ ℂ))`),
   and push the maps through using `pow4_map` / `pow2_map` (Submission.ConjPoly),
   obtaining `pow4 P̅ = pow2 P̅` with `P̅ := P.map (algebraMap ℤ ℂ)`.
2. Use `minpoly_complex_eq_prod` (Submission.ConjPoly):
   `P̅ = ∏ z∈S (X - C z)` with `S := conjugateValues α`.
   Conclude (with `Submission.RootProd.pow2_eq_prod_sub_sq` applied to that
   product, and `Submission.ConjPoly.pow4_prod`):
   `S.prod (fun z => X - C (z ^ 4)) = S.prod (fun z => X - C (z ^ 2))`.
   Name this `hprod`.
3. Show `house α ≤ 1` by contradiction: assume `1 < house α`.
   * `exists_conj_house α` (Submission.Conjugates) yields `σ₀` with
     `‖σ₀ α‖ = house α`; set `z₀ := σ₀ α` (so `z₀ ∈ S`, `1 < ‖z₀‖`, and by
     `norm_conj_le_house` every `z ∈ S` satisfies `‖z‖ ≤ ‖z₀‖`).
   * Evaluate the polynomial identity `hprod` at `X := z₀ ^ 4`
     (`Polynomial.eval₂` / `eval`), using `eval_prod` / `eval₂_prod` to rewrite
     products of evaluations.  LHS vanishes because one factor is `z₀⁴ - z₀⁴`.
     Hence RHS vanishes: `∏ z∈S (z₀ ^ 4 - z ^ 2) = 0`; by
     `Finset.prod_eq_zero_iff` get `z₁ ∈ S` with `z₀ ^ 4 = z₁ ^ 2`.
   * Then `‖z₁‖ = ‖z₀‖ ^ 2` (take norms; use `norm_mul`, `norm_pow` and
     nonnegativity), which is `> ‖z₀‖`, contradicting `‖z₁‖ ≤ ‖z₀‖`
     (`norm_conj_le_house`).
   You will need: `z ∈ S` implies `‖z‖ ≤ house α` (already
   `norm_conj_le_house`), and `z₀ ∈ S`.

`house_le_one_imp_rootOfUnity`: for every embedding `σ`,
`‖σ α‖ ≤ house α ≤ 1` (`norm_conj_le_house` then `le_trans`), so
`NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ α hα0 hα` gives
`∃ n, 0 < n ∧ α ^ n = 1`; convert with `isOfFinOrder_iff_pow_eq_one`.

`pow4_eq_pow2_imp_rootOfUnity`: compose the two theorems above.

You may add helper lemmas. Do NOT change the statements. No sorries may remain.
-/

noncomputable section

open Polynomial
open scoped Complex Polynomial

namespace Submission.RootOfUnity

open Submission.Conjugates
open Submission.ConjPoly
open Submission.Powers
open Submission.RootProd

variable {K : Type*} [Field K] [NumberField K]

/-- If `pow4 P = pow2 P` for the minimal polynomial `P := minpoly ℤ α`, then the
house of `α` is at most 1. -/
theorem pow4_eq_pow2_imp_house_le_one (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (h : pow4 (minpoly ℤ α) = pow2 (minpoly ℤ α)) :
    NumberField.house α ≤ 1 := by
  classical
  have hmonic : (minpoly ℤ α).Monic := minpoly.monic hα
  have hmap : ((pow4 (minpoly ℤ α)).map (algebraMap ℤ ℂ)) =
      ((pow2 (minpoly ℤ α)).map (algebraMap ℤ ℂ)) := congrArg (Polynomial.map (algebraMap ℤ ℂ)) h
  have hP4 : pow4 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) =
      pow2 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := by
    rw [← pow4_map (minpoly ℤ α) (algebraMap ℤ ℂ) hmonic]
    rw [← pow2_map (minpoly ℤ α) (algebraMap ℤ ℂ) hmonic]
    exact hmap
  have hPbar : (minpoly ℤ α).map (algebraMap ℤ ℂ) =
      (conjugateValues α).prod (fun z : ℂ => X - C z) :=
    minpoly_complex_eq_prod α hα
  have hprod : (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4)) =
      (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
    calc
      (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4))
          = pow4 ((conjugateValues α).prod (fun z : ℂ => X - C z)) := by
              rw [pow4_prod]
      _ = pow4 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := by rw [← hPbar]
      _ = pow2 ((minpoly ℤ α).map (algebraMap ℤ ℂ)) := hP4
      _ = pow2 ((conjugateValues α).prod (fun z : ℂ => X - C z)) := by rw [hPbar]
      _ = (conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2)) := by
              exact pow2_eq_prod_sub_sq (conjugateValues α)
                ((conjugateValues α).prod (fun z : ℂ => X - C z)) rfl
  by_contra hle
  have hgt : (1 : ℝ) < NumberField.house α := lt_of_not_ge hle
  rcases exists_conj_house α with ⟨σ₀, hσ₀⟩
  let z₀ : ℂ := σ₀ α
  have hz₀house : ‖z₀‖ = NumberField.house α := by
    dsimp [z₀]
    exact hσ₀.symm
  have hz₀mem : z₀ ∈ conjugateValues α := by
    dsimp [z₀, conjugateValues]
    exact Finset.mem_image.mpr ⟨σ₀, Finset.mem_univ σ₀, rfl⟩
  have h1lt : (1 : ℝ) < ‖z₀‖ := by
    rwa [hz₀house]
  have heval_eq : Polynomial.eval (z₀ ^ 4)
        ((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4))) =
      Polynomial.eval (z₀ ^ 4)
        ((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2))) := by
    exact congrArg (Polynomial.eval (z₀ ^ 4)) hprod
  have heval_lhs : Polynomial.eval (z₀ ^ 4)
        ((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 4))) = 0 := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero hz₀mem ?_
    simp
  have heval_rhs : Polynomial.eval (z₀ ^ 4)
        ((conjugateValues α).prod (fun z : ℂ => X - C (z ^ 2))) = 0 := by
    rw [← heval_eq]
    exact heval_lhs
  rw [Polynomial.eval_prod] at heval_rhs
  rcases (Finset.prod_eq_zero_iff.mp heval_rhs) with ⟨z₁, hz₁mem, hz₁⟩
  have hsq : z₁ ^ 2 = z₀ ^ 4 := by
    have hz₁' : z₀ ^ 4 - z₁ ^ 2 = 0 := by simpa using hz₁
    exact (sub_eq_zero.mp hz₁').symm
  have hnorm : ‖z₁‖ ^ 2 = ‖z₀‖ ^ 4 := by
    have hnorm' : ‖z₁ ^ 2‖ = ‖z₀ ^ 4‖ := congrArg (fun w : ℂ => ‖w‖) hsq
    rwa [norm_pow, norm_pow] at hnorm'
  have hz₁le : ‖z₁‖ ≤ ‖z₀‖ := by
    rcases Finset.mem_image.mp hz₁mem with ⟨σ₁, hσ₁mem, hσ₁⟩
    calc
      ‖z₁‖ = ‖σ₁ α‖ := by rw [hσ₁]
      _ ≤ NumberField.house α := norm_conj_le_house α σ₁
      _ = ‖z₀‖ := by rw [hz₀house]
  have hz1sq_le : ‖z₁‖ ^ 2 ≤ ‖z₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz₁le 2
  have hle' : ‖z₀‖ ^ 4 ≤ ‖z₀‖ ^ 2 := by nlinarith [hnorm, hz1sq_le]
  have hgt' : ‖z₀‖ ^ 2 < ‖z₀‖ ^ 4 := pow_lt_pow_right₀ h1lt (by norm_num)
  nlinarith


/-- A nonzero algebraic integer all of whose conjugates have modulus at most 1
is a root of unity (Kronecker). -/
theorem house_le_one_imp_rootOfUnity (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hh : NumberField.house α ≤ 1) : IsOfFinOrder α := by
  rw [isOfFinOrder_iff_pow_eq_one]
  have hnorm : ∀ σ : K →+* ℂ, ‖σ α‖ ≤ 1 := fun σ => le_trans (norm_conj_le_house α σ) hh
  obtain ⟨n, hnpos, hnpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hα0 hα hnorm
  exact ⟨n, hnpos, hnpow⟩

/-- **Dichotomy conclusion.** `pow4 P = pow2 P` (with `P := minpoly ℤ α`) forces
a nonzero `α` to be a root of unity. -/
theorem pow4_eq_pow2_imp_rootOfUnity (α : K) (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (h : pow4 (minpoly ℤ α) = pow2 (minpoly ℤ α)) : IsOfFinOrder α := by
  exact house_le_one_imp_rootOfUnity α hα hα0 (pow4_eq_pow2_imp_house_le_one α hα hα0 h)

end Submission.RootOfUnity

end
