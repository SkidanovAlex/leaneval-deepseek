import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open ArithmeticFunction Finset

/-- The weighted von Mangoldt summand `F n · Λ(n)/n`, used only to keep the statements below
readable. -/
private noncomputable def WLambda (F : ℕ → ℂ) (n : ℕ) : ℂ :=
  F n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ)

/-- Namespace `Work.BMF.liouville`. Import: `Mathlib`.

The weighted von Mangoldt sum over `n ≤ M` is the sum over prime powers `p ^ k ≤ M`:
for any function `F : ℕ → ℂ`,
`∑_{n=1}^{M} F n · Λ(n)/n = ∑_{p ≤ M prime} ∑_{k=1}^{⌊log_p M⌋} F(p^k)·log p / p^k`.

This is Chebyshev's decomposition `Chebyshev.psi_eq_sum_mul_log_prime` (Mathlib) with `Λ m`
replaced by `F m * Λ m / m`: only the vanishing of `Λ` off prime powers is used. -/
theorem weighted_vonMangoldt_decomp (F : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, F n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ))
      = ∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
          F (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k) := by
  have key : (∑ m ∈ Finset.Icc 1 M, WLambda F m)
      = ∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
          F (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k) := by
    -- Step 1: restrict the sum from `Icc 1 M` to the set of prime powers `≤ M`.
    have h1 : ∑ m ∈ Finset.Icc 1 M, WLambda F m
        = ∑ m ∈ ((Finset.Icc 1 M).filter Nat.Prime).biUnion
            (fun p => Finset.image (p ^ ·) (Finset.Icc 1 (Nat.log p M))), WLambda F m := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨p, hp, hq⟩ := hq
        rw [Finset.mem_filter] at hp
        obtain ⟨hpI, hpp⟩ := hp
        rw [Finset.mem_image] at hq
        obtain ⟨k, hk, rfl⟩ := hq
        rw [Finset.mem_Icc] at hpI hk ⊢
        exact ⟨one_le_pow₀ hpp.one_le, Nat.pow_le_of_le_log (by omega) hk.2⟩
      · intro x hx hxn
        have hΛ : ArithmeticFunction.vonMangoldt x = 0 := by
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
          intro hpp
          obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff x).mp hpp
          apply hxn
          rw [Finset.mem_biUnion]
          refine ⟨p, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨hp.one_le,
              (Nat.le_of_dvd (pow_pos hp.pos k) (dvd_pow_self p hk.ne')).trans
                (Finset.mem_Icc.mp hx).2⟩, hp⟩
          · rw [Finset.mem_image]
            exact ⟨k, by
              rw [Finset.mem_Icc]
              exact ⟨hk, Nat.le_log_of_pow_le hp.one_lt (Finset.mem_Icc.mp hx).2⟩, rfl⟩
        simp [WLambda, hΛ]
    -- Step 2: expand the `biUnion` into a double sum.
    have h2 : ∑ m ∈ ((Finset.Icc 1 M).filter Nat.Prime).biUnion
            (fun p => Finset.image (p ^ ·) (Finset.Icc 1 (Nat.log p M))), WLambda F m
        = ∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime,
            ∑ k ∈ Finset.Icc 1 (Nat.log p M), WLambda F (p ^ k) := by
      have hdisj : (((Finset.Icc 1 M).filter Nat.Prime : Finset ℕ) : Set ℕ).PairwiseDisjoint
          (fun p => Finset.image (p ^ ·) (Finset.Icc 1 (Nat.log p M))) := by
        rw [Finset.pairwiseDisjoint_iff]
        intro p hp q hq hne
        obtain ⟨x, hx⟩ := hne
        rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hx
        obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hxb⟩⟩ := hx
        rw [Finset.mem_Icc] at ha hb
        exact (Nat.Prime.pow_inj' (Finset.mem_filter.mp hp).2
          (Finset.mem_filter.mp hq).2 (by omega) (by omega) hxb.symm).1
      rw [Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hinj : Set.InjOn (fun k => p ^ k) ↑(Finset.Icc 1 (Nat.log p M)) := by
        intro a _ b _ hab
        exact Nat.pow_right_injective (Finset.mem_filter.mp hp).2.two_le hab
      rw [Finset.sum_image hinj]
    -- Step 3: evaluate each summand at a prime power.
    have h3 : ∑ p ∈ (Finset.Icc 1 M).filter Nat.Prime,
            ∑ k ∈ Finset.Icc 1 (Nat.log p M), WLambda F (p ^ k)
        = ∑ p ∈ M.primesLE, ∑ k ∈ Finset.Icc 1 (Nat.log p M),
            F (p ^ k) * (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ k) := by
      rw [Nat.primesLE_eq_filter_Icc_one M]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkne : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
      rw [WLambda, ArithmeticFunction.vonMangoldt_apply_pow hkne,
        ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2, Nat.cast_pow]
    rw [h1, h2, h3]
  simpa only [WLambda] using key

end Work.BMF.liouville
