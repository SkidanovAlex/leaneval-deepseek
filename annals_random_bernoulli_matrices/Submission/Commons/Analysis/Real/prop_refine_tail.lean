import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace Commons.Analysis.Real

theorem prop_refine_tail {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (2 : ℝ) ^ (Nat.floor (ε * (n : ℝ) / 2) : ℝ) *
        ((Real.exp (-16 * M / ε) / 24) ^
          Nat.ceil (((Nat.floor (ε * (n : ℝ) / 2) : ℕ) : ℝ) / 2)) ≤
        Real.exp (-2 * M * (n : ℝ)) := by
  refine ⟨Nat.ceil (4 / ε), ?_⟩
  intro n hn
  have hMpos : 0 < M := by linarith
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hnle : (4 / ε : ℝ) ≤ (n : ℝ) := by
    exact (Nat.le_ceil (4 / ε)).trans (by exact_mod_cast hn)
  let x : ℝ := ε * (n : ℝ) / 2
  let A : ℕ := Nat.floor x
  let a : ℝ := (A : ℝ)
  let B : ℕ := Nat.ceil (a / 2)
  let c : ℝ := Real.exp (-16 * M / ε) / 24
  change (2 : ℝ) ^ a * c ^ B ≤ Real.exp (-2 * M * (n : ℝ))
  have hA_ge : x - 1 ≤ a := by
    dsimp [a, A]
    exact le_of_lt (Nat.sub_one_lt_floor x)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact Nat.cast_nonneg A
  have hB_ge : a / 2 ≤ (B : ℝ) := by
    dsimp [B]
    exact Nat.le_ceil (a / 2)
  have hc0 : 0 < c := by
    dsimp [c]
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hlogc : Real.log c = -16 * M / ε - Real.log 24 := by
    dsimp [c]
    rw [Real.log_div (Real.exp_pos (-16 * M / ε)).ne' (by norm_num : (24 : ℝ) ≠ 0)]
    rw [Real.log_exp]
  have hlc_le0 : Real.log c ≤ 0 := by
    rw [hlogc]
    have h2 : -16 * M / ε < 0 := by
      exact div_neg_of_neg_of_pos (by nlinarith) hε0
    have h1 : -16 * M / ε - Real.log 24 ≤ -16 * M / ε := by
      have hlp : 0 < Real.log (24 : ℝ) := Real.log_pos (by norm_num : 1 < (24 : ℝ))
      nlinarith
    exact le_of_lt (lt_of_le_of_lt h1 h2)
  have h2log2 : 2 * Real.log (2 : ℝ) ≤ Real.log (24 : ℝ) := by
    have hlp := Real.log_pow (2 : ℝ) (2 : ℕ)
    have hlp4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      norm_num at hlp
      exact hlp
    have hle : Real.log (4 : ℝ) ≤ Real.log (24 : ℝ) :=
      Real.log_le_log (by norm_num : 0 < (4 : ℝ)) (by norm_num : (4 : ℝ) ≤ (24 : ℝ))
    nlinarith
  have hd_le : Real.log (2 : ℝ) + Real.log c / 2 ≤ -8 * M / ε := by
    rw [hlogc]
    have hcalc : Real.log (2 : ℝ) + (-16 * M / ε - Real.log (24 : ℝ)) / 2 =
        -8 * M / ε + (Real.log (2 : ℝ) - Real.log (24 : ℝ) / 2) := by
      field_simp [hεne]
      ring
    have hsub : Real.log (2 : ℝ) - Real.log (24 : ℝ) / 2 ≤ 0 := by
      nlinarith [h2log2]
    rw [hcalc]
    simpa using add_le_add_left hsub (-8 * M / ε)
  have hneg8 : -8 * M / ε ≤ 0 := by
    exact le_of_lt (div_neg_of_neg_of_pos (by nlinarith) hε0)
  -- main exponent inequality
  have hExp_le : Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c ≤ (x - 1) * (-8 * M / ε) := by
    calc
      Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c
          ≤ Real.log (2 : ℝ) * a + (a / 2) * Real.log c := by
              exact add_le_add_right (mul_le_mul_of_nonpos_right hB_ge hlc_le0) (Real.log (2 : ℝ) * a)
      _ = a * (Real.log (2 : ℝ) + Real.log c / 2) := by ring
      _ ≤ a * (-8 * M / ε) := by
              exact mul_le_mul_of_nonneg_left hd_le ha0
      _ ≤ (x - 1) * (-8 * M / ε) := by
              exact mul_le_mul_of_nonpos_right hA_ge hneg8
  -- exponent form
  have hBpow : c ^ B = Real.exp ((B : ℝ) * Real.log c) := by
    rw [← Real.exp_log (pow_pos hc0 B)]
    rw [Real.log_pow c B]
  have hpow : (2 : ℝ) ^ a * c ^ B =
      Real.exp (Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c) := by
    calc
      (2 : ℝ) ^ a * c ^ B
          = Real.exp (Real.log (2 : ℝ) * a) * c ^ B := by
              rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ)) a]
      _ = Real.exp (Real.log (2 : ℝ) * a) * Real.exp ((B : ℝ) * Real.log c) := by
              rw [hBpow]
      _ = Real.exp (Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c) := by
              rw [Real.exp_add]
  -- bound inside exp ≤ -4Mn + 8M/ε
  have hbound : (x - 1) * (-8 * M / ε) = -4 * M * (n : ℝ) + 8 * M / ε := by
    dsimp [x]
    field_simp [hεne]
    ring
  -- 8 M/ε ≤ 2 M n
  have hm : 8 * M / ε ≤ 2 * M * (n : ℝ) := by
    have h8 : (2 * M) * (4 / ε) = 8 * M / ε := by
      field_simp [hεne]
      ring
    rw [← h8]
    exact mul_le_mul_of_nonneg_left hnle (by nlinarith)
  have hfin : -4 * M * (n : ℝ) + 8 * M / ε ≤ -2 * M * (n : ℝ) := by
    calc
      -4 * M * (n : ℝ) + 8 * M / ε
          ≤ -4 * M * (n : ℝ) + 2 * M * (n : ℝ) := by
              exact add_le_add_right hm (-4 * M * (n : ℝ))
      _ = -2 * M * (n : ℝ) := by ring
  -- assemble
  calc
    (2 : ℝ) ^ a * c ^ B = Real.exp (Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c) := hpow
    _ ≤ Real.exp (-2 * M * (n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        calc
          Real.log (2 : ℝ) * a + (B : ℝ) * Real.log c
              ≤ (x - 1) * (-8 * M / ε) := hExp_le
          _ = -4 * M * (n : ℝ) + 8 * M / ε := hbound
          _ ≤ -2 * M * (n : ℝ) := hfin
