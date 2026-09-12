import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Generic upper `N^{C}`-scaling lemma (any positive multiplier).
-/

noncomputable section

open scoped Real

namespace Submission.ScaleBoundAny

/-- A large enough exponent for any base `≥ 2` to dominate a fixed constant:
`∃ A ≥ 0, ∀ n ≥ 2, M ≤ n^A`. -/
lemma exists_large_rpow {M : ℝ} (hM1 : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → M ≤ (n : ℝ) ^ A := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (x := M) (y := (2 : ℝ)) (by norm_num : 1 < (2 : ℝ))
  refine ⟨(k : ℝ), Nat.cast_nonneg k, ?_⟩
  intro n hn
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    M ≤ (2 : ℝ) ^ k := le_of_lt hk
    _ = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast (2 : ℝ) k).symm
    _ ≤ (n : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow (by norm_num) hn' (Nat.cast_nonneg k)

/-- Upper-degree scaling with an arbitrary positive multiplier `M0`:
for `Cu > 0`, `K ≥ 0`, `M0 > 0` there is `C > 0` such that for every `N ≥ 2`:
`e^{K}·(N+2)^{Cu}·M0 ≤ N^{C}`. -/
lemma scale_bound_up_any (Cu K M0 : ℝ) (hCu : 0 < Cu) (hK : 0 ≤ K) (hM0 : 0 < M0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      Real.exp K * ((N + 2 : ℕ) : ℝ) ^ Cu * M0 ≤ (N : ℝ) ^ C := by
  let M1 : ℝ := max M0 1
  have hM1ge : 1 ≤ M1 := le_max_right M0 1
  have hM0le : M0 ≤ M1 := le_max_left M0 1
  have hM1nonneg : 0 ≤ M1 := le_trans (by norm_num : (0 : ℝ) ≤ 1) hM1ge
  let X0 : ℝ := Real.exp K * (2 : ℝ) ^ Cu * M1
  have hExpK1 : 1 ≤ Real.exp K := Real.one_le_exp hK
  have hTwoCu1 : 1 ≤ (2 : ℝ) ^ Cu :=
    Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (le_of_lt hCu)
  have hExpK2 : 1 ≤ Real.exp K * (2 : ℝ) ^ Cu := by
    calc
      (1 : ℝ) ≤ Real.exp K := hExpK1
      _ = Real.exp K * 1 := by ring
      _ ≤ Real.exp K * (2 : ℝ) ^ Cu := mul_le_mul_of_nonneg_left hTwoCu1 (Real.exp_nonneg K)
  have hX01 : 1 ≤ X0 := by
    dsimp [X0]
    calc
      (1 : ℝ) ≤ Real.exp K * (2 : ℝ) ^ Cu := hExpK2
      _ = (Real.exp K * (2 : ℝ) ^ Cu) * 1 := by ring
      _ ≤ (Real.exp K * (2 : ℝ) ^ Cu) * M1 := by
        exact mul_le_mul_of_nonneg_left hM1ge
          (mul_nonneg (Real.exp_nonneg K)
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) Cu))
  obtain ⟨A, hA0, hA⟩ := exists_large_rpow (M := X0) hX01
  refine ⟨Cu + A, by nlinarith [hCu, hA0], ?_⟩
  intro N hN
  let x : ℝ := (N : ℝ)
  let m : ℝ := ((N + 2 : ℕ) : ℝ)
  have hNcast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact hNcast
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hx_nonneg : 0 ≤ x := le_of_lt hxpos
  have hm_le : m ≤ 2 * x := by
    dsimp [m, x]
    norm_num
    nlinarith [hNcast]
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have hmCu : m ^ Cu ≤ (2 : ℝ) ^ Cu * x ^ Cu := by
    calc
      m ^ Cu ≤ (2 * x) ^ Cu := Real.rpow_le_rpow hm_nonneg hm_le (le_of_lt hCu)
      _ = (2 : ℝ) ^ Cu * x ^ Cu := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hx_nonneg]
  have hmCu0 : 0 ≤ m ^ Cu := Real.rpow_nonneg hm_nonneg Cu
  have hmain : Real.exp K * m ^ Cu * M0 ≤ x ^ (Cu + A) := by
    calc
      Real.exp K * m ^ Cu * M0 = (Real.exp K * M0) * m ^ Cu := by ring
      _ ≤ (Real.exp K * M1) * m ^ Cu := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM0le (Real.exp_nonneg K)) hmCu0
      _ ≤ (Real.exp K * M1) * ((2 : ℝ) ^ Cu * x ^ Cu) := by
        exact mul_le_mul_of_nonneg_left hmCu (mul_nonneg (Real.exp_nonneg K) hM1nonneg)
      _ = X0 * x ^ Cu := by
        dsimp [X0]
        ring
      _ ≤ x ^ A * x ^ Cu := by
        exact mul_le_mul_of_nonneg_right (hA N hN) (Real.rpow_nonneg hx_nonneg Cu)
      _ = x ^ (A + Cu) := by
        rw [Real.rpow_add hxpos A Cu]
      _ = x ^ (Cu + A) := by ring_nf
  change Real.exp K * m ^ Cu * M0 ≤ x ^ (Cu + A)
  exact hmain

end Submission.ScaleBoundAny
