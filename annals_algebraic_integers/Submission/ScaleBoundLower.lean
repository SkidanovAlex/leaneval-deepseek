import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Generic `n^{-C}`-scaling lemma used by `Submission.PVer1` (pure real analysis).
-/

noncomputable section

open scoped Real

namespace Submission.ScaleBoundLower

/-- A large enough exponent for any base `≥ 2` to dominate a fixed constant:
`∃ A ≥ 0, ∀ n ≥ 2, M ≤ n^A`. -/
lemma exists_large_rpow {M : ℝ} (hM1 : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → M ≤ (n : ℝ) ^ A := by
  let A : ℝ := Real.log M / Real.log 2
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg hlogM (le_of_lt hlog2pos)
  refine ⟨A, hA0, ?_⟩
  intro n hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hpow : (2 : ℝ) ^ A = M := by
    calc
      (2 : ℝ) ^ A = rexp (Real.log 2 * A) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = rexp (Real.log M) := by
          congr 1
          dsimp [A]
          field_simp [ne_of_gt hlog2pos]
      _ = M := Real.exp_log hMpos
  calc
    M = (2 : ℝ) ^ A := hpow.symm
    _ ≤ (n : ℝ) ^ A := Real.rpow_le_rpow (by norm_num) hn2 hA0

/-- Lower-degree scaling: for any `C1 > 0`, `K ≥ 0`, `D ≥ 1` there is `C > 0`
such that for every `N ≥ 2`:
`N^{-C} ≤ e^{-K}·(N+2)^{-C1} / D²` (real exponents). -/
lemma scale_bound_gen (C1 K D : ℝ) (hC1 : 0 < C1) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (N : ℝ) ^ (-C) ≤ Real.exp (-K) * ((N + 2 : ℕ) : ℝ) ^ (-C1) / D ^ 2 := by
  let M0 : ℝ := Real.exp K * D ^ 2 * (2 : ℝ) ^ C1
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hD2pos : 0 < D ^ 2 := pow_pos hDpos 2
  have hC1ge0 : 0 ≤ C1 := le_of_lt hC1
  have hE : 1 ≤ Real.exp K := Real.one_le_exp hK
  have hD2 : 1 ≤ D ^ 2 := by nlinarith [hD]
  have h21 : 1 ≤ (2 : ℝ) ^ C1 := by
    rw [← Real.one_rpow C1]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) hC1ge0
  have hM01 : 1 ≤ M0 := by
    dsimp [M0]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hE hD2) h21
  rcases exists_large_rpow hM01 with ⟨A, hA0, hA⟩
  refine ⟨C1 + A, by linarith, ?_⟩
  intro N hN
  let x : ℝ := (N : ℝ)
  let t : ℝ := ((N + 2 : ℕ) : ℝ)
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hN
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx2
  have hx2ge0 : 0 ≤ x := le_of_lt hxpos
  have htpos : 0 < t := by
    dsimp [t]
    exact_mod_cast (by omega : 0 < N + 2)
  have ht2 : t ≤ 2 * x := by
    dsimp [x, t]
    rw [Nat.cast_add]
    norm_num
    linarith
  have ht0 : 0 ≤ t := le_of_lt htpos
  have hmono1 : t ^ C1 ≤ (2 * x) ^ C1 := Real.rpow_le_rpow ht0 ht2 hC1ge0
  have hA_N : M0 ≤ x ^ A := by
    dsimp [x]
    exact hA N hN
  have hmul : (2 * x) ^ C1 = (2 : ℝ) ^ C1 * x ^ C1 :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx2ge0
  have hmain : Real.exp K * D ^ 2 * t ^ C1 ≤ x ^ (C1 + A) := by
    calc
      Real.exp K * D ^ 2 * t ^ C1
          ≤ Real.exp K * D ^ 2 * (2 * x) ^ C1 :=
              mul_le_mul_of_nonneg_left hmono1 (le_of_lt (mul_pos (Real.exp_pos K) hD2pos))
      _ = M0 * x ^ C1 := by
          dsimp [M0]
          rw [hmul]
          ring
      _ ≤ x ^ A * x ^ C1 :=
              mul_le_mul_of_nonneg_right hA_N (Real.rpow_nonneg hx2ge0 C1)
      _ = x ^ (C1 + A) := by
          rw [mul_comm]
          rw [← Real.rpow_add hxpos C1 A]
  have hYpos : 0 < Real.exp K * D ^ 2 * t ^ C1 := by
    exact mul_pos (mul_pos (Real.exp_pos K) hD2pos) (Real.rpow_pos_of_pos htpos C1)
  have hxpow : 0 < x ^ (C1 + A) := Real.rpow_pos_of_pos hxpos (C1 + A)
  have hmain' : (x ^ (C1 + A))⁻¹ ≤ (Real.exp K * D ^ 2 * t ^ C1)⁻¹ := by
    exact (inv_le_inv₀ hxpow hYpos).mpr hmain
  calc
    x ^ (-(C1 + A)) = (x ^ (C1 + A))⁻¹ := by rw [Real.rpow_neg hx2ge0]
    _ ≤ (Real.exp K * D ^ 2 * t ^ C1)⁻¹ := hmain'
    _ = (Real.exp K)⁻¹ * (t ^ C1)⁻¹ / D ^ 2 := by
        field_simp [ne_of_gt (Real.exp_pos K), ne_of_gt (Real.rpow_pos_of_pos htpos C1),
          pow_ne_zero 2 (ne_of_gt hDpos)]
    _ = Real.exp (-K) * t ^ (-C1) / D ^ 2 := by
        rw [Real.exp_neg]
        rw [Real.rpow_neg (le_of_lt htpos)]

end Submission.ScaleBoundLower
