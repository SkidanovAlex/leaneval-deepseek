import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `1 + Σᵢ mᵢ^{2k} ≤ (card ι + 1) * monomialSum k m`

`monomialSum k m = ∑_{|α| ≤ k} ∏ᵢ (2π mᵢ)^{2αᵢ}` is the Fourier-side weight of
`Σ_{|α| ≤ k} ‖∂^α f‖²_{L²}` (see `Torus.lean`).  The estimate proved here is the elementary
bookkeeping fact that the two "extreme" families of monomials are already present in the sum:

* the zero multi-index contributes `1`;
* for each `i`, the multi-index `k·eᵢ` contributes `(2π mᵢ)^{2k} ≥ mᵢ^{2k}`.

Since all summands are nonnegative, each of these is bounded by `monomialSum k m`; summing
`mᵢ^{2k} ≤ monomialSum k m` over `i` gives `Σᵢ mᵢ^{2k} ≤ card ι * monomialSum k m`, and
`1 ≤ monomialSum k m` finishes the count `1 + card ι ≤ card ι + 1`.
-/

namespace Work.Diff.STE

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every summand of `monomialSum` is nonnegative: the monomials are even powers. -/
private lemma monomialSum_summand_nonneg (k : ℕ) (m : ι → ℤ) (α : ι → Fin (k + 1)) :
    0 ≤ (if (∑ i, (α i : ℕ)) ≤ k then
          ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)) else 0) := by
  split_ifs with h
  · exact Finset.prod_nonneg fun i _ => by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
  · exact le_refl 0

/-- `monomialSum k m ≥ 1`: the zero multi-index contributes `1`. -/
private lemma one_le_monomialSum (k : ℕ) (m : ι → ℤ) : 1 ≤ monomialSum k m := by
  have h := Finset.single_le_sum
    (f := fun α : ι → Fin (k + 1) =>
      if (∑ i, (α i : ℕ)) ≤ k then ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)) else 0)
    (fun α _ => monomialSum_summand_nonneg k m α) (Finset.mem_univ (0 : ι → Fin (k + 1)))
  have h0 : (if (∑ i, (((0 : ι → Fin (k + 1)) i) : ℕ)) ≤ k then
        ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (((0 : ι → Fin (k + 1)) i) : ℕ)) else 0) = 1 := by
    simp
  rw [h0] at h
  simpa [monomialSum] using h

/-- The multi-index `k·eᵢ`, as an element of `ι → Fin (k+1)`. -/
private def ke_fun (k : ℕ) (i : ι) : ι → Fin (k + 1) :=
  fun j => if j = i then ⟨k, Nat.lt_succ_self k⟩ else 0

private lemma ke_fun_sum (k : ℕ) (i : ι) :
    (∑ j, ((ke_fun k i j : Fin (k + 1)) : ℕ)) = k := by
  rw [Finset.sum_eq_single i]
  · simp [ke_fun]
  · intro b _ hb; simp [ke_fun, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma ke_fun_prod (k : ℕ) (m : ι → ℤ) (i : ι) :
    (∏ j, (2 * Real.pi * (m j : ℝ)) ^ (2 * ((ke_fun k i j : Fin (k + 1)) : ℕ)))
      = (2 * Real.pi * (m i : ℝ)) ^ (2 * k) := by
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [ke_fun]
  · intro b _ hb; simp [ke_fun, hb]

/-- Each `mᵢ^{2k}` is bounded by `monomialSum k m`, via the monomial `k·eᵢ` (and
`(2π mᵢ)^{2k} ≥ mᵢ^{2k}` because `2π ≥ 1`). -/
private lemma zpow_le_monomialSum (k : ℕ) (m : ι → ℤ) (i : ι) :
    ((m i : ℝ)) ^ (2 * k) ≤ monomialSum k m := by
  have hstep1 : ((m i : ℝ)) ^ (2 * k) ≤ (2 * Real.pi * (m i : ℝ)) ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg _)
    have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [hpi, sq_nonneg (m i : ℝ)]
  have hstep2 : (2 * Real.pi * (m i : ℝ)) ^ (2 * k) ≤ monomialSum k m := by
    have h := Finset.single_le_sum
      (f := fun α : ι → Fin (k + 1) =>
        if (∑ i, (α i : ℕ)) ≤ k then ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)) else 0)
      (fun α _ => monomialSum_summand_nonneg k m α) (Finset.mem_univ (ke_fun k i))
    have hval : (if (∑ j, ((ke_fun k i j : Fin (k + 1)) : ℕ)) ≤ k then
        ∏ j, (2 * Real.pi * (m j : ℝ)) ^ (2 * ((ke_fun k i j : Fin (k + 1)) : ℕ)) else 0)
        = (2 * Real.pi * (m i : ℝ)) ^ (2 * k) := by
      rw [ke_fun_sum k i, ke_fun_prod k m i]
      simp
    rw [hval] at h
    simpa [monomialSum] using h
  exact le_trans hstep1 hstep2

theorem one_add_zpow_le_monomialSum {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℤ) :
    1 + ∑ i, ((m i : ℝ)) ^ (2 * k) ≤ (((Fintype.card ι : ℕ) : ℝ) + 1) * monomialSum k m := by
  have hM1 : 1 ≤ monomialSum k m := one_le_monomialSum k m
  have hterm : ∀ i : ι, ((m i : ℝ)) ^ (2 * k) ≤ monomialSum k m := zpow_le_monomialSum k m
  have hT : ∑ i, ((m i : ℝ)) ^ (2 * k) ≤ (Fintype.card ι : ℝ) * monomialSum k m := by
    calc ∑ i, ((m i : ℝ)) ^ (2 * k) ≤ ∑ _i : ι, monomialSum k m :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card ι : ℝ) * monomialSum k m := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hexp : (((Fintype.card ι : ℕ) : ℝ) + 1) * monomialSum k m
      = (Fintype.card ι : ℝ) * monomialSum k m + monomialSum k m := by ring
  rw [hexp]
  linarith

end Work.Diff.STE
