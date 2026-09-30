import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_direct.expLogLog_ineq`

There is a constant `C > 0` such that for all reals `P ≥ 2`, `T ≥ 3`, with
`L = log T / log P` and `k = ⌈L⌉`,

`4 ^ (k+1) * k ^ k * (3/2) ^ k ≤ C * exp (2 * L * log (log T))`.

The proof splits on whether `L ≤ 1000` (where `k` is bounded and the left side is a
constant) or `L > 1000` (where `log log T ≥ log L - 1` dominates `log k`).
-/

namespace Work.BMF.mr_direct

open Real

/-- `Real.log 6 ≤ 2`, from `exp 2 = (exp 1)^2 > 2.7^2 > 6`. -/
private lemma log_six_le_two : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 6)]
  have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2:ℝ) = (2:ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [hexp2]
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1, sq_nonneg (Real.exp 1 - 2.7)]

/-- `Real.log 2 ≤ 1`. -/
private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
  linarith [Real.exp_one_gt_d9]

/-- `-1 ≤ log log P` for `P ≥ 2`, via `log x ≥ 1 - 1/x` and `log 2 ≥ 1/2`. -/
private lemma neg_one_le_log_log (P : ℝ) (hP : 2 ≤ P) : -1 ≤ Real.log (Real.log P) := by
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
  have hge := Real.one_sub_inv_le_log_of_pos hlogP
  have hinv : (Real.log P)⁻¹ ≤ 2 := by
    have h : (Real.log P)⁻¹ ≤ ((1:ℝ)/2)⁻¹ := by
      rw [inv_le_inv₀ hlogP (by norm_num : (0:ℝ) < 1/2)]
      linarith [Real.log_two_gt_d9]
    simpa using h
  linarith

/-- `6 < log 1000`, since `exp 6 = (exp 1)^6 < 3^6 = 729 < 1000`. -/
private lemma log_thousand_gt_six : (6:ℝ) < Real.log 1000 := by
  have hexp6 : Real.exp 6 = Real.exp 1 ^ 6 := by
    have := Real.exp_nat_mul (1:ℝ) 6
    simp_all
  have hlt : Real.exp 6 < 1000 := by
    rw [hexp6]
    have h3 : Real.exp 1 ^ 6 < (3:ℝ)^6 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
    norm_num at h3 ⊢
    linarith
  calc (6:ℝ) = Real.log (Real.exp 6) := by rw [Real.log_exp]
    _ < Real.log 1000 := Real.log_lt_log (Real.exp_pos 6) hlt

/-- **Case A** (`k ≤ 1000`): the left-hand side is bounded by a fixed constant. -/
private lemma pow_bound_small (k : ℕ) (hk : k ≤ 1000) :
    (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k
      ≤ (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 := by
  have hkR : (k:ℝ) ≤ 1000 := by exact_mod_cast hk
  have h4 : (4:ℝ)^(k+1) ≤ (4:ℝ)^1001 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hkk : (k:ℝ)^k ≤ (1000:ℝ)^1000 := by
    calc (k:ℝ)^k ≤ (1000:ℝ)^k := pow_le_pow_left₀ (by positivity) hkR k
      _ ≤ (1000:ℝ)^1000 := pow_le_pow_right₀ (by norm_num) hk
  have h32 : (3/2:ℝ)^k ≤ (3/2:ℝ)^1000 := pow_le_pow_right₀ (by norm_num) hk
  exact mul_le_mul (mul_le_mul h4 hkk (by positivity) (by positivity))
    h32 (by positivity) (by positivity)

/-- **Case B core** (`L > 1000`): the exponential of `k log 6 + k log k` is dominated
by `exp (2 L u)` for `u ≥ max 5 (log L - 1)`. -/
private lemma main_bound (L u : ℝ) (k : ℕ)
    (hLgt : 1000 < L) (hk_ge : L ≤ (k:ℝ)) (hk_le : (k:ℝ) ≤ L + 1)
    (hlogL_le : Real.log L ≤ u + 1) (hu_ge : 5 ≤ u) :
    (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k ≤ 4 * Real.exp (2*L*u) := by
  have hLpos : 0 < L := by linarith
  have hk_pos : (0:ℝ) < (k:ℝ) := by linarith
  have hLp1 : 0 ≤ L + 1 := by linarith
  -- collapse `4^(k+1) * (3/2)^k` to `4 * 6^k`
  have hform : (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k = 4 * (6:ℝ)^k * (k:ℝ)^k := by
    rw [pow_succ]
    rw [show (4:ℝ)^k * 4 * (k:ℝ)^k * (3/2:ℝ)^k
          = 4 * ((4:ℝ)^k * (3/2:ℝ)^k) * (k:ℝ)^k by ring]
    rw [← mul_pow]
    norm_num
  have h6k : Real.exp ((k:ℝ) * Real.log 6) = (6:ℝ)^k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 6)]
  have hkk : Real.exp ((k:ℝ) * Real.log (k:ℝ)) = (k:ℝ)^k := by
    rw [Real.exp_nat_mul, Real.exp_log hk_pos]
  have hprod : (6:ℝ)^k * (k:ℝ)^k
      = Real.exp ((k:ℝ) * Real.log 6 + (k:ℝ) * Real.log (k:ℝ)) := by
    rw [← h6k, ← hkk, ← Real.exp_add]
  -- the exponent estimate
  have hlog6pos : 0 ≤ Real.log 6 := le_of_lt (Real.log_pos (by norm_num))
  have hk_ge_one : (1:ℝ) ≤ (k:ℝ) := by linarith
  have h1 : (k:ℝ) * Real.log 6 ≤ (L+1) * 2 := by
    calc (k:ℝ) * Real.log 6 ≤ (L+1) * Real.log 6 := mul_le_mul_of_nonneg_right hk_le hlog6pos
      _ ≤ (L+1) * 2 := mul_le_mul_of_nonneg_left log_six_le_two hLp1
  have hlogk_le : Real.log (k:ℝ) ≤ Real.log L + 1 := by
    have hk_le_2L : (k:ℝ) ≤ 2 * L := by linarith
    have h := Real.log_le_log hk_pos hk_le_2L
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hLpos)] at h
    linarith [log_two_le_one]
  have hlogk_nonneg : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg hk_ge_one
  have h2 : (k:ℝ) * Real.log (k:ℝ) ≤ (L+1) * (u + 2) := by
    calc (k:ℝ) * Real.log (k:ℝ) ≤ (L+1) * (Real.log L + 1) :=
            mul_le_mul hk_le hlogk_le hlogk_nonneg hLp1
      _ ≤ (L+1) * (u + 2) := by
            apply mul_le_mul_of_nonneg_left _ hLp1
            linarith
  have hkey : (L+1) * 2 + (L+1) * (u+2) ≤ 2 * L * u := by nlinarith [hLgt, hu_ge]
  have hsum : (k:ℝ) * Real.log 6 + (k:ℝ) * Real.log (k:ℝ) ≤ 2 * L * u := by linarith
  calc (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k
      = 4 * (6:ℝ)^k * (k:ℝ)^k := hform
    _ = 4 * ((6:ℝ)^k * (k:ℝ)^k) := by ring
    _ = 4 * Real.exp ((k:ℝ) * Real.log 6 + (k:ℝ) * Real.log (k:ℝ)) := by rw [hprod]
    _ ≤ 4 * Real.exp (2 * L * u) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
          exact Real.exp_le_exp.mpr hsum

theorem expLogLog_ineq :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P T : ℝ), 2 ≤ P → 3 ≤ T →
        let L := Real.log T / Real.log P
        let k := Nat.ceil L
        (4 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (3 / 2 : ℝ) ^ k
          ≤ C * Real.exp (2 * L * Real.log (Real.log T)) := by
  refine ⟨(4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4, ?_, ?_⟩
  · positivity
  · intro P T hP hT
    dsimp only
    set L : ℝ := Real.log T / Real.log P with hLdef
    set k : ℕ := Nat.ceil L with hkdef
    set u : ℝ := Real.log (Real.log T) with hudef
    have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hLpos : 0 < L := by rw [hLdef]; exact div_pos hlogT hlogP
    have hkge : L ≤ (k:ℝ) := by rw [hkdef]; exact Nat.le_ceil L
    have hkle : (k:ℝ) ≤ L + 1 := by
      rw [hkdef]; exact le_of_lt (Nat.ceil_lt_add_one hLpos.le)
    by_cases hcase : L ≤ 1000
    · -- small `L`: `k ≤ 1000`
      have hk1000 : k ≤ 1000 := by rw [hkdef]; exact Nat.ceil_le.mpr hcase
      have hsmall := pow_bound_small k hk1000
      have hu0 : 0 ≤ u := by
        rw [hudef]
        apply Real.log_nonneg
        have h3 : (1:ℝ) < Real.log 3 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
          exact Real.exp_one_lt_three
        exact le_trans (le_of_lt h3) (Real.log_le_log (by norm_num : (0:ℝ) < 3) hT)
      have hexp1 : 1 ≤ Real.exp (2 * L * u) := by
        apply Real.one_le_exp
        positivity
      have hCpos : 0 < (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4 := by positivity
      calc (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k
          ≤ (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 := hsmall
        _ ≤ (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4 := by linarith
        _ = ((4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4) * 1 := by ring
        _ ≤ ((4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4) * Real.exp (2*L*u) :=
              mul_le_mul_of_nonneg_left hexp1 hCpos.le
    · -- large `L`
      have hLgt : 1000 < L := not_le.mp hcase
      have hLT : L * Real.log P = Real.log T := by
        rw [hLdef, div_mul_cancel₀ _ (ne_of_gt hlogP)]
      have hu_eq : u = Real.log L + Real.log (Real.log P) := by
        rw [hudef, ← hLT, Real.log_mul (ne_of_gt hLpos) (ne_of_gt hlogP)]
      have hlogL_gt_six : 6 < Real.log L :=
        lt_trans log_thousand_gt_six (Real.log_lt_log (by norm_num) hLgt)
      have hloglogP : -1 ≤ Real.log (Real.log P) := neg_one_le_log_log P hP
      have hu_ge : 5 ≤ u := by rw [hu_eq]; linarith
      have hlogL_le : Real.log L ≤ u + 1 := by rw [hu_eq]; linarith
      have hmain := main_bound L u k hLgt hkge hkle hlogL_le hu_ge
      have hC4 : (4:ℝ) ≤ (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4 := by
        have hp : (0:ℝ) < (4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 := by positivity
        linarith
      calc (4:ℝ)^(k+1) * (k:ℝ)^k * (3/2:ℝ)^k
          ≤ 4 * Real.exp (2 * L * u) := hmain
        _ ≤ ((4:ℝ)^1001 * (1000:ℝ)^1000 * (3/2:ℝ)^1000 + 4) * Real.exp (2 * L * u) :=
              mul_le_mul_of_nonneg_right hC4 (Real.exp_pos _).le

end Work.BMF.mr_direct
