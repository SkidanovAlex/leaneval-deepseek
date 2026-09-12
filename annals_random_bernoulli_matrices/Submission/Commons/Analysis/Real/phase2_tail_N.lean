import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace Commons.Analysis.Real

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ))
  norm_num at h
  exact h

/-- Layer-0 absorption for the Prop.-refinement phase-2 counting export: with
`m ≥ εn/4` and `N ≤ 2^n`, the bound `exp(−2Mn) + (√2·N·√n)·2^m·(12μ')^m`
(with `μ' := exp(−16M/ε)/(24·1024²)`) is at most `exp(−Mn)` for all large `n`. -/
theorem phase2_tail_N {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (m : ℕ), (ε * (n : ℝ) / 4) ≤ (m : ℝ) →
    ∀ (N : ℕ), 1 ≤ N → (N : ℝ) ≤ (2 : ℝ) ^ n →
      Real.exp (-2 * M * (n : ℝ)) +
        (Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)) *
          (2 : ℝ) ^ m * (12 * Real.exp (-16 * M / ε) / (24 * 1024 ^ 2)) ^ m ≤
        Real.exp (-M * (n : ℝ)) := by
  refine ⟨1, ?_⟩
  intro n hn m hm N hN1 hN2
  let x : ℝ := M * (n : ℝ)
  let C : ℝ := 12 * Real.exp (-16 * M / ε) / (24 * 1024 ^ 2)
  let g : ℝ := Real.sqrt 2 * (N : ℝ) * Real.sqrt (n : ℝ)
  change Real.exp (-2 * M * (n : ℝ)) + g * (2 : ℝ) ^ m * C ^ m ≤ Real.exp (-M * (n : ℝ))
  have hMpos : 0 < M := by linarith
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : 0 < (n : ℝ) := by linarith
  have hnRnonneg : 0 ≤ (n : ℝ) := le_of_lt hnRpos
  have hxge : (n : ℝ) ≤ x := by
    dsimp [x]
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ M * (n : ℝ) := mul_le_mul_of_nonneg_right hM hnRnonneg
  have hxge1 : (1 : ℝ) ≤ x := le_trans hnR1 hxge
  have hlogx : Real.log 2 ≤ x := le_trans log_two_le_one hxge1
  -- first term ≤ exp(-x)/2
  have hExpHalf : Real.exp (-x) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-x) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith [hlogx])
      _ = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ))]
        norm_num
  have hA : Real.exp (-2 * x) ≤ (1 / 2 : ℝ) * Real.exp (-x) := by
    calc
      Real.exp (-2 * x) = Real.exp (-x + -x) := by congr 1; ring
      _ = Real.exp (-x) * Real.exp (-x) := by rw [Real.exp_add]
      _ ≤ Real.exp (-x) * (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hExpHalf (Real.exp_pos (-x)).le
      _ = (1 / 2 : ℝ) * Real.exp (-x) := by ring
  -- second term: g * 2^m * C^m with 2*C = exp(-16M/ε)/1024²
  have h2C : 2 * C = Real.exp (-16 * M / ε) / (1024 : ℝ) ^ 2 := by
    dsimp [C]
    field_simp
    ring_nf
  have hden_pos : 0 < (1024 : ℝ) ^ 2 := by positivity
  have hden_ge1 : (1 : ℝ) ≤ (1024 : ℝ) ^ 2 := by norm_num
  have hE0 : 0 ≤ Real.exp (-16 * M / ε) := (Real.exp_pos _).le
  have h2C_le : 2 * C ≤ Real.exp (-16 * M / ε) := by
    rw [h2C]
    rw [div_le_iff₀ hden_pos]
    calc
      Real.exp (-16 * M / ε) ≤ Real.exp (-16 * M / ε) * 1 := by rw [mul_one]
      _ ≤ Real.exp (-16 * M / ε) * (1024 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hden_ge1 hE0
  have h2C_nonneg : 0 ≤ 2 * C := by
    rw [h2C]
    exact div_nonneg hE0 (le_of_lt hden_pos)
  have hk_le0 : -16 * M / ε ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hε0)
  have hstep : (m : ℝ) * (-16 * M / ε) ≤ (ε * (n : ℝ) / 4) * (-16 * M / ε) :=
    mul_le_mul_of_nonpos_right hm hk_le0
  have harg : (m : ℝ) * (-16 * M / ε) ≤ -4 * x := by
    dsimp [x]
    calc
      (m : ℝ) * (-16 * M / ε) ≤ (ε * (n : ℝ) / 4) * (-16 * M / ε) := hstep
      _ = -4 * (M * (n : ℝ)) := by
        field_simp [hεne]
        ring
  have hterm_pow : (2 * C) ^ m ≤ Real.exp (-4 * x) := by
    calc
      (2 * C) ^ m ≤ Real.exp (-16 * M / ε) ^ m := pow_le_pow_left₀ h2C_nonneg h2C_le m
      _ = Real.exp ((m : ℝ) * (-16 * M / ε)) := (Real.exp_nat_mul (-16 * M / ε) m).symm
      _ ≤ Real.exp (-4 * x) := Real.exp_le_exp.mpr (by simpa using harg)
  -- g ≤ √2 * 2^n * √n
  have hN0 : 0 ≤ (N : ℝ) := by
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hg_eq : g = (Real.sqrt 2 * Real.sqrt (n : ℝ)) * (N : ℝ) := by
    dsimp [g]
    ring
  have hfac_nonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (n : ℝ))
  have hg_nonneg : 0 ≤ g := by
    rw [hg_eq]
    exact mul_nonneg hfac_nonneg hN0
  have hg_le : g ≤ Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ) := by
    calc
      g = (Real.sqrt 2 * Real.sqrt (n : ℝ)) * (N : ℝ) := hg_eq
      _ ≤ (Real.sqrt 2 * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hN2 hfac_nonneg
      _ = Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ) := by ring
  have hB2 : g * (2 : ℝ) ^ m * C ^ m ≤
      (Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x) := by
    calc
      g * (2 : ℝ) ^ m * C ^ m = g * ((2 : ℝ) ^ m * C ^ m) := by ring
      _ ≤ g * Real.exp (-4 * x) := by
        have hmc : (2 : ℝ) ^ m * C ^ m ≤ Real.exp (-4 * x) := by
          calc
            (2 : ℝ) ^ m * C ^ m = (2 * C) ^ m := (mul_pow (2 : ℝ) C m).symm
            _ ≤ Real.exp (-4 * x) := hterm_pow
        exact mul_le_mul_of_nonneg_left hmc hg_nonneg
      _ ≤ (Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x) := by
        exact mul_le_mul_of_nonneg_right hg_le (Real.exp_pos (-4 * x)).le
  -- 2√2·2^n·√n·exp(-4x) ≤ exp(-x)/2
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnRpos
  have hnlog2_le : (n : ℝ) * Real.log 2 ≤ (n : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left log_two_le_one hnRnonneg)
  have hhalf : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ (1 / 2 : ℝ) * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ (1 / 2))
  have h3half : (3 / 2 : ℝ) * Real.log 2 ≤ (3 / 2 : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left log_two_le_one (by norm_num : (0 : ℝ) ≤ (3 / 2)))
  have h3x : 3 * (n : ℝ) ≤ 3 * x :=
    mul_le_mul_of_nonneg_left hxge (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
  have hpos5 : 0 ≤ (3 / 2 : ℝ) * (n : ℝ) - 1 := by nlinarith [hnR1]
  have hg0 : 0 ≤ 3 * x - (n : ℝ) * Real.log 2 - (1 / 2) * Real.log (n : ℝ) -
      (3 / 2) * Real.log 2 := by
    nlinarith
  have hArg : (n : ℝ) * Real.log 2 + (1 / 2) * Real.log (n : ℝ) + (3 / 2) * Real.log 2 ≤
      3 * x := by
    nlinarith [hg0]
  have hExpS_le : Real.exp ((n : ℝ) * Real.log 2 + (1 / 2) * Real.log (n : ℝ) +
      Real.log 2 + (1 / 2) * Real.log 2) ≤ Real.exp (3 * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hArg]
  have hAe : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ))]
  have hBe : Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = Real.sqrt (n : ℝ) := by
    calc
      Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = Real.exp (Real.log (n : ℝ) / 2) := by
        congr 1
        ring
      _ = Real.sqrt (Real.exp (Real.log (n : ℝ))) := Real.exp_half (Real.log (n : ℝ))
      _ = Real.sqrt (n : ℝ) := by rw [Real.exp_log hnRpos]
  have hCe : Real.exp (Real.log 2) = (2 : ℝ) :=
    Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ))
  have hDe : Real.exp ((1 / 2 : ℝ) * Real.log 2) = Real.sqrt 2 := by
    calc
      Real.exp ((1 / 2 : ℝ) * Real.log 2) = Real.exp (Real.log 2 / 2) := by
        congr 1
        ring
      _ = Real.sqrt (Real.exp (Real.log 2)) := Real.exp_half (Real.log 2)
      _ = Real.sqrt 2 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ))]
  have hS_exp : Real.exp ((n : ℝ) * Real.log 2 + (1 / 2) * Real.log (n : ℝ) +
      Real.log 2 + (1 / 2) * Real.log 2) =
        Real.exp ((n : ℝ) * Real.log 2) * Real.exp ((1 / 2) * Real.log (n : ℝ)) *
          Real.exp (Real.log 2) * Real.exp ((1 / 2) * Real.log 2) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  have hS_val : Real.exp ((n : ℝ) * Real.log 2 + (1 / 2) * Real.log (n : ℝ) +
      Real.log 2 + (1 / 2) * Real.log 2) =
        2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ) := by
    calc
      Real.exp ((n : ℝ) * Real.log 2 + (1 / 2) * Real.log (n : ℝ) +
          Real.log 2 + (1 / 2) * Real.log 2)
          = Real.exp ((n : ℝ) * Real.log 2) * Real.exp ((1 / 2) * Real.log (n : ℝ)) *
              Real.exp (Real.log 2) * Real.exp ((1 / 2) * Real.log 2) := hS_exp
      _ = (2 : ℝ) ^ n * Real.sqrt (n : ℝ) * (2 : ℝ) * Real.sqrt 2 := by
        rw [hAe, hBe, hCe, hDe]
      _ = 2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ) := by ring
  have hP : 2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ) ≤ Real.exp (3 * x) := by
    rw [← hS_val]
    exact hExpS_le
  have hPexp : (2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x) ≤
      Real.exp (-x) := by
    calc
      (2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x)
          ≤ Real.exp (3 * x) * Real.exp (-4 * x) :=
            mul_le_mul_of_nonneg_right hP (Real.exp_pos (-4 * x)).le
      _ = Real.exp (3 * x + (-4 * x)) := by rw [← Real.exp_add]
      _ = Real.exp (-x) := by congr 1; ring
  have hBig : (Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x) ≤
      (1 / 2 : ℝ) * Real.exp (-x) := by
    calc
      (Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) * Real.exp (-4 * x)
          = (1 / 2 : ℝ) * ((2 * Real.sqrt 2 * (2 : ℝ) ^ n * Real.sqrt (n : ℝ)) *
              Real.exp (-4 * x)) := by ring
      _ ≤ (1 / 2 : ℝ) * Real.exp (-x) := by
        exact mul_le_mul_of_nonneg_left hPexp (by norm_num : (0 : ℝ) ≤ (1 / 2))
  -- assemble
  have hB_final : g * (2 : ℝ) ^ m * C ^ m ≤ (1 / 2 : ℝ) * Real.exp (-x) :=
    le_trans hB2 hBig
  calc
    Real.exp (-2 * M * (n : ℝ)) + g * (2 : ℝ) ^ m * C ^ m
        = Real.exp (-2 * x) + g * (2 : ℝ) ^ m * C ^ m := by
            congr 1
            dsimp [x]
            ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (-x) + (1 / 2 : ℝ) * Real.exp (-x) := add_le_add hA hB_final
    _ = Real.exp (-x) := by ring
    _ = Real.exp (-M * (n : ℝ)) := by
        congr 1
        dsimp [x]
        ring

end Commons.Analysis.Real