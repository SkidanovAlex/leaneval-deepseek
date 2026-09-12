import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Generic upper `N^{C}`-scaling lemma used by `Submission.PVer1` (pure real analysis).
-/

noncomputable section

open scoped Real

namespace Submission.ScaleBoundUpper

/-- A large enough exponent for any base `≥ 2` to dominate a fixed constant:
`∃ A ≥ 0, ∀ n ≥ 2, M ≤ n^A`. -/
lemma exists_large_rpow {M : ℝ} (hM1 : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → M ≤ (n : ℝ) ^ A := by
  let A : ℝ := Real.log M / Real.log 2
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    exact div_nonneg (Real.log_nonneg hM1) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  · intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlnM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hln2n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    have h1 : Real.log M ≤ A * Real.log (n : ℝ) := by
      dsimp [A]
      have hdiv : 1 ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
        exact (le_div_iff₀ hlog2).mpr (by simpa using hln2n)
      have hmul : Real.log M * 1 ≤ Real.log M * (Real.log (n : ℝ) / Real.log (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hlnM
      calc
        Real.log M ≤ Real.log M * (Real.log (n : ℝ) / Real.log (2 : ℝ)) := by
          simpa using hmul
        _ = (Real.log M / Real.log 2) * Real.log (n : ℝ) := by
          field_simp [ne_of_gt hlog2]
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hM1
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (A * Real.log (n : ℝ)) := Real.exp_le_exp.mpr h1
      _ = (n : ℝ) ^ A := by
        rw [Real.rpow_def_of_pos hn0]
        congr 1
        ring

/-- Upper-degree scaling: for `Cu > 0`, `K ≥ 0`, `M0 ≥ 1` there is `C > 0`
such that for every `N ≥ 2`: `e^{K}·(N+2)^{Cu}·M0 ≤ N^{C}`. -/
lemma scale_bound_up_gen (Cu K M0 : ℝ) (hCu : 0 < Cu) (hK : 0 ≤ K) (hM : 1 ≤ M0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      Real.exp K * ((N + 2 : ℕ) : ℝ) ^ Cu * M0 ≤ (N : ℝ) ^ C := by
  let E : ℝ := Real.exp K
  have hE1 : 1 ≤ E := by dsimp [E]; exact Real.one_le_exp hK
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have hM0ge : 0 ≤ M0 := le_trans zero_le_one hM
  let M3 : ℝ := E * M0 * (3 : ℝ) ^ Cu
  have h3c : 1 ≤ (3 : ℝ) ^ Cu := by
    calc
      (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero (3 : ℝ)).symm
      _ ≤ (3 : ℝ) ^ Cu := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hCu)
  have hM3 : 1 ≤ M3 := by
    dsimp [M3]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hE1 hM) h3c
  rcases exists_large_rpow (M := M3) hM3 with ⟨A, hAnneg, hA⟩
  let C : ℝ := A + Cu
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact add_pos_of_nonneg_of_pos hAnneg hCu
  · intro N hN
    have hX0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNp2 : 0 < ((N + 2 : ℕ) : ℝ) := by positivity
    have hNp2le3N : ((N + 2 : ℕ) : ℝ) ≤ (3 : ℝ) * (N : ℝ) := by
      have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rw [show ((N + 2 : ℕ) : ℝ) = (N : ℝ) + 2 by norm_num]
      nlinarith
    have hEM0 : 0 ≤ E * M0 := mul_nonneg hE0 hM0ge
    have hpow : ((N + 2 : ℕ) : ℝ) ^ Cu ≤ ((3 : ℝ) * (N : ℝ)) ^ Cu :=
      Real.rpow_le_rpow hNp2.le hNp2le3N (le_of_lt hCu)
    calc
      Real.exp K * ((N + 2 : ℕ) : ℝ) ^ Cu * M0
          = (E * M0) * ((N + 2 : ℕ) : ℝ) ^ Cu := by
              dsimp [E]
              ring
      _ ≤ (E * M0) * ((3 : ℝ) * (N : ℝ)) ^ Cu := by
              exact mul_le_mul_of_nonneg_left hpow hEM0
      _ = (E * M0 * (3 : ℝ) ^ Cu) * (N : ℝ) ^ Cu := by
              rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) hX0.le]
              ring
      _ ≤ (N : ℝ) ^ A * (N : ℝ) ^ Cu := by
              exact mul_le_mul_of_nonneg_right (hA N hN)
                (Real.rpow_nonneg hX0.le Cu)
      _ = (N : ℝ) ^ (A + Cu) := by
              rw [← Real.rpow_add hX0 A Cu]
      _ = (N : ℝ) ^ C := by
              rfl

end Submission.ScaleBoundUpper
