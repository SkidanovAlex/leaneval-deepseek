import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `monomialSum k m ≤ C * wt m ^ k`: the Leibniz sum is dominated by the weight

`wt m = 1 + Σᵢ mᵢ²` and `monomialSum k m = Σ_{|α| ≤ k} ∏ᵢ (2π mᵢ)^{2 αᵢ}` are weights of order
`2k` in `m`, and `monomialSum` is a finite sum of monomials of degree `≤ 2k`, so it is dominated
by a constant times `(wt m)^k`.  Concretely, each summand satisfies

`∏ᵢ (2π mᵢ)^{2αᵢ} = ∏ᵢ ((2π mᵢ)²)^{αᵢ} ≤ ∏ᵢ (4π² wt m)^{αᵢ} = (4π² wt m)^{Σ αᵢ} ≤ (4π² wt m)^k`

because `mᵢ² ≤ wt m`, `wt m ≥ 1` and `Σ αᵢ ≤ k`.  Summing over the `(k+1)^{card ι}` multi-indices
gives the claim with `C = (card (ι → Fin (k+1))) * (4π²)^k`.
-/

namespace Work.Diff.STE

theorem monomialSum_le_wt_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ι → ℤ,
      Work.Diff.STE.monomialSum k m ≤ C * (Work.Diff.STE.wt m) ^ k := by
  classical
  refine ⟨((Fintype.card (ι → Fin (k + 1)) : ℕ) : ℝ) * (4 * Real.pi ^ 2) ^ k, ?_, ?_⟩
  · have hcardpos : (0 : ℝ) < ((Fintype.card (ι → Fin (k + 1)) : ℕ) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => (0 : Fin (k + 1))⟩)
    have : (0 : ℝ) < (4 * Real.pi ^ 2) ^ k := by positivity
    positivity
  · intro m
    -- each coordinate square is bounded by the weight
    have hmi : ∀ i : ι, ((m i : ℝ)) ^ 2 ≤ Work.Diff.STE.wt m := by
      intro i
      have h := Finset.single_le_sum (f := fun j : ι => ((m j : ℤ) : ℝ) ^ 2)
        (fun j _ => sq_nonneg ((m j : ℤ) : ℝ)) (Finset.mem_univ i)
      simp only [Work.Diff.STE.wt]
      linarith
    -- the base `4π² wt m` is at least one
    have hc1 : 1 ≤ 4 * Real.pi ^ 2 * Work.Diff.STE.wt m := by
      have h1 : 1 ≤ Work.Diff.STE.wt m := Work.Diff.STE.wt_one_le m
      have h2 : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith
    -- every summand of `monomialSum` is bounded by `(4π² wt m)^k`
    have key : ∀ α : ι → Fin (k + 1),
        (if (∑ i, (α i : ℕ)) ≤ k then
          ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)) else 0)
          ≤ (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ k := by
      intro α
      by_cases h : (∑ i, (α i : ℕ)) ≤ k
      · rw [ite_eq_left h]
        have hprod : (∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)))
            ≤ ∏ i, (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ (α i : ℕ) := by
          apply Finset.prod_le_prod₀
          · intro i _
            rw [pow_mul]
            exact pow_nonneg (sq_nonneg _) _
          · intro i _
            rw [pow_mul]
            apply pow_le_pow_left₀ (sq_nonneg _)
            have := hmi i
            nlinarith [Real.pi_pos]
        calc (∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)))
            ≤ ∏ i, (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ (α i : ℕ) := hprod
          _ = (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ (∑ i, (α i : ℕ)) := by
              rw [Finset.prod_pow_eq_pow_sum]
          _ ≤ (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ k := pow_le_pow_right₀ hc1 h
      · rw [ite_eq_right h]
        positivity
    calc Work.Diff.STE.monomialSum k m
        = ∑ α : ι → Fin (k + 1),
            (if (∑ i, (α i : ℕ)) ≤ k then
              ∏ i, (2 * Real.pi * (m i : ℝ)) ^ (2 * (α i : ℕ)) else 0) := rfl
      _ ≤ ∑ _α : ι → Fin (k + 1), (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ k :=
          Finset.sum_le_sum (fun α _ => key α)
      _ = ((Fintype.card (ι → Fin (k + 1)) : ℕ) : ℝ)
            * (4 * Real.pi ^ 2 * Work.Diff.STE.wt m) ^ k := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card (ι → Fin (k + 1)) : ℕ) : ℝ) * (4 * Real.pi ^ 2) ^ k
            * (Work.Diff.STE.wt m) ^ k := by
          rw [mul_pow]; ring

end Work.Diff.STE
