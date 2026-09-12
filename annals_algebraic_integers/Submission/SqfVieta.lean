import Mathlib
import Submission.Notions

/-!
# Sum-of-roots identities (Vieta) connecting coefficients and root means

Generic facts needed by the keystone (Gap B of the squarefree/keystone chain):

1. for a MONIC integer polynomial `R` of degree `n ≥ 1`,
   `rootSumComplex R = -R.coeff (n - 1)` (over ℂ), hence
   `rootMeanReal R = -R.coeff (n - 1) / (n : ℝ)` — the complexified `R` splits
   over ℂ (`IsAlgClosed.splits`) and `Splits.nextCoeff_eq_neg_sum_roots_of_monic`
   identifies the root sum with `-nextCoeff`, which is `-coeff (n - 1)`;

2. for a real product `∏ᵢ (X − C (α i))` (degree `n ≥ 1`),
   `Σᵢ α i = -coeff (n - 1)` (Mathlib `prod_X_sub_C_coeff_card_pred`);

3. a bridge: if additionally the monic integer `Rn` and the monic real
   factorized `P` agree in coefficient `n - 1`, then
   `rootMeanReal Rn = (Σᵢ α i) / (n : ℝ)`.

Namespace `Submission.SqfVieta`.  Only Mathlib + `Submission.Notions`.
-/

noncomputable section
open scoped Real BigOperators
open Polynomial

namespace Submission.SqfVieta

open Submission.Notions

/-- The complexified `aroots` over ℚ of an integer polynomial coincide with the
roots of its complexification. -/
lemma aroots_ℚℂ_eq_roots_map {R : Polynomial ℤ} :
    ((R.map (algebraMap ℤ ℚ)).aroots ℂ) = (R.map (algebraMap ℤ ℂ)).roots := by
  rw [Polynomial.aroots_def]
  congr 1
  ext n
  simp

/-- Root sum of a monic integer polynomial of degree `n ≥ 1` is
`-coeff (n-1)`. -/
lemma rootSumComplex_eq_neg_coeff {R : Polynomial ℤ} (hmon : R.Monic)
    {n : ℕ} (hdeg : R.natDegree = n) (hn : 1 ≤ n) :
    rootSumComplex R = - (R.coeff (n - 1) : ℂ) := by
  let RC : Polynomial ℂ := R.map (algebraMap ℤ ℂ)
  have hRCmon : RC.Monic := by
    dsimp [RC]
    simpa using (hmon.map (algebraMap ℤ ℂ))
  have hRCsplits : RC.Splits := IsAlgClosed.splits RC
  have hRCdeg : RC.natDegree = n := by
    dsimp [RC]
    rw [Polynomial.natDegree_map_eq_of_injective (Int.cast_injective)]
    exact hdeg
  have hn' : RC.natDegree ≠ 0 := by omega
  have hnext : RC.nextCoeff = RC.coeff (n - 1) := by
    rw [nextCoeff, if_neg hn', hRCdeg]
  have hspl := Splits.nextCoeff_eq_neg_sum_roots_of_monic hRCsplits hRCmon
  calc
    rootSumComplex R = RC.roots.sum := by
      have hlem := congrArg Multiset.sum (aroots_ℚℂ_eq_roots_map (R := R))
      simpa [RC, rootSumComplex] using hlem
    _ = -RC.nextCoeff := by
      rw [hspl]
      simp
    _ = - (R.coeff (n - 1) : ℂ) := by
      rw [hnext]
      dsimp [RC]
      rw [Polynomial.coeff_map]
      simp

/-- Root mean of a monic integer polynomial of degree `n ≥ 1` is
`-coeff (n-1) / n`. -/
lemma rootMeanReal_eq_neg_coeff_div {R : Polynomial ℤ} (hmon : R.Monic)
    {n : ℕ} (hdeg : R.natDegree = n) (hn : 1 ≤ n) :
    rootMeanReal R = - (R.coeff (n - 1) : ℝ) / (n : ℝ) := by
  have hsum := rootSumComplex_eq_neg_coeff hmon hdeg hn
  have hre : (rootSumComplex R).re = - (R.coeff (n - 1) : ℝ) := by
    rw [hsum]
    simp
  unfold rootMeanReal
  rw [hdeg, hre]

/-- Vieta for a product of real linear factors: `Σᵢ α i = -coeff (n-1)` of
`∏ᵢ (X − C(α i))`. -/
lemma prod_X_sub_C_sum_eq_neg_coeff {n : ℕ} (α : Fin n → ℝ) (hn : 1 ≤ n) :
    (∑ i : Fin n, α i) = - ((∏ i : Fin n, (X - C (α i) : Polynomial ℝ))).coeff (n - 1) := by
  have hcard : 0 < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn
  have h := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin n))
    (fun i : Fin n => α i) hcard
  -- h : coeff (∏ i ∈ univ, X - C(α i)) (card - 1) = -∑ i ∈ univ, α i
  have hcard' : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard'] at h
  rw [h]
  simp

/-- Bridge: if the monic integer `Rn` and the real factored `P` have the same
coefficient at degree `n - 1`, the root mean of `Rn` is the mean of the roots
`α` of `P`. -/
lemma rootMeanReal_eq_sum_div {Rn : Polynomial ℤ} (hmonRn : Rn.Monic)
    {n : ℕ} {P : Polynomial ℝ} {α : Fin n → ℝ} (hdegRn : Rn.natDegree = n) (hn : 1 ≤ n)
    (hcoeff : P.coeff (n - 1) = (Rn.coeff (n - 1) : ℝ))
    (hPfac : P = ∏ i : Fin n, (X - C (α i) : Polynomial ℝ)) :
    rootMeanReal Rn = (∑ i : Fin n, α i) / (n : ℝ) := by
  have hrm := rootMeanReal_eq_neg_coeff_div hmonRn hdegRn hn
  calc
    rootMeanReal Rn = - (Rn.coeff (n - 1) : ℝ) / (n : ℝ) := hrm
    _ = - P.coeff (n - 1) / (n : ℝ) := by rw [hcoeff]
    _ = (∑ i : Fin n, α i) / (n : ℝ) := by
      have hv := prod_X_sub_C_sum_eq_neg_coeff α hn
      rw [← hPfac] at hv
      rw [← hv]

end Submission.SqfVieta
