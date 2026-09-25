import Mathlib
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.RegionIII.caRegionIIIDefs

/-!
# `caC1_finset_reduction` — reduction of `Margin.caC1 ε` to a prime sum

For `ξ = caXi ε ≥ 10^8`, `n = caN ε = ⌊√(2.5 ξ)⌋₊ + 1` and `ξ₂ = caXi2 ε`:

`Margin.caC1 ε = ∑_{ξ₂ < p ≤ ξ} (1/(2p²) − 1/(3p³))`,

and every prime `ξ₂ < p ≤ ξ` has `1/(2p²) − 1/(3p³) ≥ 0`.  Since `ξ₂ ≤ ⌊√(2.5 ξ)⌋₊ + 1 = n`
(`A.caXi2_le_sqrt` together with `Nat.floor_add_one`), the index set `{n < p ≤ ξ}` is contained
in `{ξ₂ < p ≤ ξ}`, so dropping the (nonnegative) remaining terms gives

`caC1 ε ≥ ∑_{n < p ≤ ξ} (1/(2p²) − 1/(3p³)) = (1/2)·∑_{n < p ≤ ξ} 1/p² − (1/3)·∑_{n < p ≤ ξ} 1/p³`,

and the last sum is bounded by the full tail over the integers, which telescopes:
`∑_{n < j ≤ m} 1/j³ ≤ 1/n²`.  Hence

`caC1 ε ≥ (1/2)·∑_{n < p ≤ ξ} 1/p² − (1/3)/n²`.

This is precisely the statement below; it is the "finset reduction" consumed by the Region III
estimates of the margin lemma.
-/

set_option maxHeartbeats 1000000

namespace Work.RHContract.A.RegionIII

open Finset

/-- Tail bound for the cube of the reciprocal: `∑_{n < j ≤ m} 1/j³ ≤ 1/n²` for `n ≥ 1`.
This is `∑ 1/j³ ≤ (1/n)·∑ 1/j² ≤ (1/n)·(1/n)` using `sum_Ioc_inv_sq_le_sub`. -/
private lemma sum_Ioc_inv_cube_le (n m : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 3) ≤ 1 / ((n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : n ≠ 0 := by omega
  have hsq : ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 2) ≤ 1 / (n : ℝ) := by
    rcases lt_or_ge m n with hmn | hnm
    · rw [Finset.Ioc_eq_empty_of_le (le_of_lt hmn)]
      simp only [Finset.sum_empty]
      positivity
    · have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := n) (n := m) hnne hnm
      have h1 : ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 2)
          = ∑ j ∈ Finset.Ioc n m, ((j : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_congr rfl; intro j _; rw [one_div]
      rw [h1, one_div]
      have h2 : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := by positivity
      linarith
  have hmain : ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 3)
      ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hnj : n ≤ j := le_of_lt (Finset.mem_Ioc.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hnjr : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hnj
    have h1 : (1 : ℝ) / (j : ℝ) ^ 3 ≤ 1 / ((n : ℝ) * (j : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith
    have h2 : (1 : ℝ) / ((n : ℝ) * (j : ℝ) ^ 2) = (1 / (n : ℝ)) * (1 / (j : ℝ) ^ 2) := by
      field_simp
    linarith
  calc ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 3)
      ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.Ioc n m, (1 : ℝ) / ((j : ℝ) ^ 2) := hmain
    _ ≤ (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hsq; positivity
    _ = 1 / ((n : ℝ) ^ 2) := by field_simp

theorem caC1_finset_reduction (ε : ℝ) (hε : 0 < ε) (hξ : (10 : ℝ) ^ 8 ≤ Work.RHContract.A.RegionIII.caXiR ε) :
    (1 / 2) * (∑ p ∈ Finset.Ioc (Work.RHContract.A.RegionIII.caN ε) (Work.RHPlan.caXi ε),
        if p.Prime then (1 : ℝ) / ((p : ℝ) ^ 2) else 0)
      - (1 / 3) * (1 / ((Work.RHContract.A.RegionIII.caN ε : ℝ) ^ 2))
      ≤ Work.RHContract.Margin.caC1 ε := by
  set m : ℕ := Work.RHPlan.caXi ε with hm
  set n : ℕ := Work.RHContract.A.RegionIII.caN ε with hn
  -- `ξ = caXi ε ≥ 1530`, so `caXi2_le_sqrt` applies
  have hξ1530 : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
    have h := hξ
    rw [caXiR_eq] at h
    have h2 : (1530 : ℝ) ≤ (10 : ℝ) ^ 8 := by norm_num
    linarith
  have hn1 : 1 ≤ n := by
    rw [hn, caN_eq]
    omega
  -- `ξ₂ = caXi2 ε ≤ ⌊√(2.5 ξ)⌋₊ + 1 = caN ε`
  have hcaXi2 : Work.RHContract.Margin.caXi2 ε ≤ n := by
    have h2 : ((Work.RHContract.Margin.caXi2 ε : ℕ) : ℝ)
        ≤ Real.sqrt (2.5 * caXiR ε) + 1 := by
      have h := Work.RHContract.A.caXi2_le_sqrt ε hε hξ1530
      rwa [caXiR_eq]
    have h3 : Nat.floor (Real.sqrt (2.5 * caXiR ε) + 1) = n := by
      rw [caXiR_eq, hn, caN_eq]
      exact Nat.floor_add_one (Real.sqrt_nonneg _)
    have h4 : Work.RHContract.Margin.caXi2 ε
        ≤ Nat.floor (Real.sqrt (2.5 * caXiR ε) + 1) := Nat.le_floor h2
    rw [h3] at h4
    exact h4
  -- the index set `{n < p ≤ m, p prime}` is `{p ≤ m prime : n < p}`
  have hset : (Nat.primesLE m).filter (fun q : ℕ => n < q) = (Finset.Ioc n m).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ioc]
    tauto
  have hS : (∑ p ∈ Finset.Ioc n m, if p.Prime then (1 : ℝ) / ((p : ℝ) ^ 2) else 0)
      = ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 2) := by
    rw [← Finset.sum_filter, hset]
  -- tail bound on `∑ 1/p³`
  have hkey : ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 3)
      ≤ 1 / ((n : ℝ) ^ 2) := by
    have hsub : (Nat.primesLE m).filter (fun q : ℕ => n < q) ⊆ Finset.Ioc n m := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_Ioc.mpr ⟨hp.2, (Nat.mem_primesLE.mp hp.1).1⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
      (sum_Ioc_inv_cube_le n m hn1)
  -- splitting the difference of the two terms
  have hV : ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q),
          (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3))
      = (1 / 2) * (∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 2))
        - (1 / 3) * (∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 3)) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; field_simp
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; field_simp
  have hstep : (1 / 2) * (∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 2))
      - (1 / 3) * (1 / ((n : ℝ) ^ 2))
      ≤ ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q),
          (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) := by
    rw [hV]
    have hh := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    linarith
  -- the smaller index set is contained in the `caC1` one
  have hA_le_C1 : ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q),
        (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) ≤ Work.RHContract.Margin.caC1 ε := by
    have hC1unfold : Work.RHContract.Margin.caC1 ε
        = ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => Work.RHContract.Margin.caXi2 ε < q),
            (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) := by
      unfold Work.RHContract.Margin.caC1
      rw [Nat.floor_natCast, ← hm]
    rw [hC1unfold]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, lt_of_le_of_lt hcaXi2 hp.2⟩
    · intro p hp _
      obtain ⟨hp1, _⟩ := Finset.mem_filter.mp hp
      have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp1).2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have h3 : 1 / (3 * (p : ℝ) ^ 3) ≤ 1 / (2 * (p : ℝ) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
  calc (1 / 2) * (∑ p ∈ Finset.Ioc n m, if p.Prime then (1 : ℝ) / ((p : ℝ) ^ 2) else 0)
          - (1 / 3) * (1 / ((n : ℝ) ^ 2))
      = (1 / 2) * (∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q), (1 : ℝ) / ((p : ℝ) ^ 2))
          - (1 / 3) * (1 / ((n : ℝ) ^ 2)) := by rw [hS]
    _ ≤ ∑ p ∈ (Nat.primesLE m).filter (fun q : ℕ => n < q),
          (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) := hstep
    _ ≤ Work.RHContract.Margin.caC1 ε := hA_le_C1

end Work.RHContract.A.RegionIII
