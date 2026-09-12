import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

set_option maxHeartbeats 0

/-- For `x ≥ 8`, `5 * x^(5/2) * exp (-3x) ≤ 1`. -/
private lemma five_sq_rpow52_exp_neg_three_le_one {x : ℝ} (hx : 8 ≤ x) :
    5 * x ^ ((5 : ℝ) / 2) * Real.exp (-3 * x) ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log x ≤ x := by
    have h := Real.log_le_rpow_div (le_of_lt hx0) (by norm_num : (0 : ℝ) < 1)
    simpa using h
  have hlog5 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    norm_num at h ⊢
    linarith
  have hx52pos : 0 < x ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 ((5 : ℝ) / 2)
  have hprod_pos : 0 < 5 * x ^ ((5 : ℝ) / 2) := by positivity
  have hlog_rn : Real.log (x ^ ((5 : ℝ) / 2)) = ((5 : ℝ) / 2) * Real.log x :=
    Real.log_rpow hx0 ((5 : ℝ) / 2)
  have hln : Real.log 5 + ((5 : ℝ) / 2) * Real.log x ≤ 3 * x := by
    nlinarith [hlogx, hlog5, hx]
  have hlog_eq : Real.log (5 * x ^ ((5 : ℝ) / 2)) = Real.log 5 + ((5 : ℝ) / 2) * Real.log x := by
    rw [Real.log_mul]
    · rw [hlog_rn]
    · norm_num
    · exact ne_of_gt hx52pos
  have hbody : 5 * x ^ ((5 : ℝ) / 2) ≤ Real.exp (3 * x) := by
    rw [← Real.exp_log hprod_pos]
    exact (Real.exp_le_exp).2 (by rw [hlog_eq]; exact hln)
  calc
    5 * x ^ ((5 : ℝ) / 2) * Real.exp (-3 * x)
        ≤ Real.exp (3 * x) * Real.exp (-3 * x) := by
          exact mul_le_mul_of_nonneg_right hbody (le_of_lt (Real.exp_pos (-3 * x)))
    _ = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero

private lemma ceil_gap_lower {η : ℝ} (hη0 : 0 < η) {n : ℕ}
    (hηn4 : (4 : ℝ) ≤ η * (n : ℝ)) :
    (η / 4) * (n : ℝ) ≤
      (((Nat.ceil (η * (n : ℝ)) : ℕ) - Nat.ceil ((η / 2) * (n : ℝ)) : ℕ) : ℝ) := by
  let x : ℝ := η * (n : ℝ)
  let y : ℝ := (η / 2) * (n : ℝ)
  let k : ℕ := Nat.ceil x
  let j : ℕ := Nat.ceil y
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (le_of_lt (by linarith : 0 < η / 2)) (Nat.cast_nonneg n)
  have hyx : y ≤ x := by
    dsimp [y, x]
    exact mul_le_mul_of_nonneg_right (by linarith : η / 2 ≤ η) (Nat.cast_nonneg n)
  have hkj : j ≤ k := by
    dsimp [j, k]
    exact Nat.ceil_le_ceil hyx
  have hkge : x ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil x
  have hjle : (j : ℝ) ≤ y + 1 := by
    have := Nat.ceil_lt_add_one hy0
    dsimp [j] at this ⊢
    exact le_of_lt this
  have hsub : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
    exact Nat.cast_sub hkj
  have hA : x - (y + 1) ≤ ((k - j : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith [hkge, hjle]
  have hB : (η / 4) * (n : ℝ) ≤ x - (y + 1) := by
    dsimp [x, y]
    nlinarith [hηn4]
  exact le_trans hB hA

theorem rough_decay_layer0_rpow52 :
    ∀ {M : ℝ} (hM : 0 < M) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
      {cQ : ℝ} (hcQ : 0 < cQ),
      ∃ (L : ℝ) (n₀ : ℕ), 1 ≤ L ∧ 1 ≤ n₀ ∧
        ∀ (n : ℕ) (hn0 : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N)
          (hN2 : (N : ℝ) ≤ (2 : ℝ) ^ n) (ℓ : ℕ) (hℓge : n ≤ 2 * ℓ)
          (hℓle : ℓ ≤ n),
          (cQ / L ≤ 1) ∧
            5 * (N : ℝ) ^ 2 * (n : ℝ) ^ ((5 : ℝ) / 2) * (2 : ℝ) ^ ℓ *
              ((ℓ.choose (Nat.ceil (η * (n : ℝ)))) : ℝ) *
              (cQ / L) ^ (Nat.ceil (η * (n : ℝ)) - Nat.ceil ((η / 2) * (n : ℝ))) ≤
              Real.exp (-M * (n : ℝ)) := by
  intro M hM η hη0 hη1 cQ hcQ
  let a : ℝ := η / 4
  let K : ℝ := (M + 3 + 4 * Real.log 2) / a
  let L : ℝ := max cQ 1 * Real.exp K
  let n₀ : ℕ := Nat.ceil (4 / η)
  have ha : 0 < a := by dsimp [a]; linarith [hη0]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hnum : 0 < M + 3 + 4 * Real.log 2 := by nlinarith [hM, hlog2]
  have hKpos : 0 < K := by dsimp [K]; exact div_pos hnum ha
  have hK0 : 0 ≤ K := le_of_lt hKpos
  have hKa : K * a = M + 3 + 4 * Real.log 2 := by
    dsimp [K]
    field_simp [a, ne_of_gt ha]
  have hmax_pos : 0 < max cQ 1 := lt_of_lt_of_le hcQ (le_max_left cQ 1)
  have hLpos : 0 < L := by dsimp [L]; exact mul_pos hmax_pos (Real.exp_pos K)
  have hL1 : 1 ≤ L := by
    dsimp [L]
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ max cQ 1 * Real.exp K := by
        exact mul_le_mul (le_max_right cQ 1) (Real.one_le_exp hK0) (by norm_num)
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right cQ 1))
  have hge : cQ * Real.exp K ≤ L := by
    dsimp [L]
    exact mul_le_mul_of_nonneg_right (le_max_left cQ 1) (le_of_lt (Real.exp_pos K))
  -- n₀ properties
  have h4η : (4 / η) ≤ (n₀ : ℝ) := by dsimp [n₀]; exact Nat.le_ceil (4 / η)
  have h84 : (8 : ℝ) ≤ 4 / η := by
    apply (le_div_iff₀ hη0).2
    nlinarith [hη1]
  have hn0one : 1 ≤ n₀ := by
    have h : (1 : ℝ) ≤ (n₀ : ℝ) := by nlinarith [h4η, h84]
    exact_mod_cast h
  have hcQ_le_L : cQ ≤ L := by
    calc
      cQ ≤ max cQ 1 := le_max_left cQ 1
      _ ≤ max cQ 1 * Real.exp K := by
        have hstep := mul_le_mul_of_nonneg_right (Real.one_le_exp hK0) (le_of_lt hmax_pos)
        simpa [mul_one] using hstep
  have hcQ_div_L_le_one : cQ / L ≤ 1 := by
    exact (div_le_iff₀ hLpos).2 (by simpa using hcQ_le_L)
  -- q and p
  let q : ℝ := Real.exp (-K)
  have hp_le_q : cQ / L ≤ q := by
    dsimp [q]
    rw [Real.exp_neg]
    rw [div_le_iff₀ hLpos, mul_comm]
    exact (le_div_iff₀ (Real.exp_pos K)).2 hge
  refine ⟨L, n₀, hL1, hn0one, ?_⟩
  intro n hn0 N hN1 hN2 ℓ hℓge hℓle
  let rn : ℝ := (n : ℝ)
  let rnP : ℝ := rn ^ ((5 : ℝ) / 2)
  let T : ℝ := (2 : ℝ) ^ n
  let k : ℕ := Nat.ceil (η * (n : ℝ))
  let j : ℕ := Nat.ceil ((η / 2) * (n : ℝ))
  let m : ℕ := k - j
  have hnR : (n₀ : ℝ) ≤ rn := by dsimp [rn]; exact_mod_cast hn0
  have hn_4η : (4 / η) ≤ rn := le_trans h4η hnR
  have hrn8 : (8 : ℝ) ≤ rn := le_trans h84 hn_4η
  have hrn0 : 0 < rn := by dsimp [rn]; exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans hn0one hn0))
  have hrnP0 : 0 ≤ rnP := by
    dsimp [rnP]
    exact Real.rpow_nonneg (le_of_lt hrn0) ((5 : ℝ) / 2)
  have hηn4 : (4 : ℝ) ≤ η * rn := by
    dsimp [rn]
    calc
      4 = η * (4 / η) := by field_simp [ne_of_gt hη0]
      _ ≤ η * (n : ℝ) := mul_le_mul_of_nonneg_left hn_4η (le_of_lt hη0)
  have hmge : a * rn ≤ (m : ℝ) := by
    dsimp [a, m, k, j]
    simpa using (ceil_gap_lower hη0 hηn4)
  -- base comparisons
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hN2sq : (N : ℝ) ^ 2 ≤ T ^ 2 := by
    have hle : |(N : ℝ)| ≤ |T| := by
      rw [abs_of_nonneg hN0, abs_of_nonneg hT0]
      simpa [T] using hN2
    exact (sq_le_sq).2 hle
  have hC_le : (ℓ.choose k : ℝ) ≤ (2 : ℝ) ^ ℓ := by
    exact_mod_cast (Nat.choose_le_two_pow ℓ k)
  have h2l : (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hℓle
  have hp0 : 0 ≤ cQ / L := div_nonneg (le_of_lt hcQ) (le_of_lt hLpos)
  have hpm : (cQ / L) ^ m ≤ q ^ m := pow_le_pow_left₀ hp0 hp_le_q m
  -- q^m ≤ exp(-K a rn)
  have hqm_eq : q ^ m = Real.exp (-K * (m : ℝ)) := by
    dsimp [q]
    rw [← Real.exp_nat_mul (-K) m]
    congr 1
    ring
  have hqexp : q ^ m ≤ Real.exp (-K * (a * rn)) := by
    rw [hqm_eq]
    apply Real.exp_le_exp.mpr
    have hKm : K * (a * rn) ≤ K * (m : ℝ) := mul_le_mul_of_nonneg_left hmge hK0
    nlinarith
  -- step 1
  have hstep1 :
      5 * (N : ℝ) ^ 2 * rnP * (2 : ℝ) ^ ℓ * (ℓ.choose k : ℝ) * (cQ / L) ^ m
        ≤ 5 * T ^ 2 * rnP * (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * q ^ m := by
    dsimp [T]
    gcongr
  -- step 2
  have hstep2 :
      5 * T ^ 2 * rnP * (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ * q ^ m
        ≤ 5 * T ^ 2 * rnP * T * T * q ^ m := by
    gcongr
  have hstep3 :
      5 * T ^ 2 * rnP * T * T * q ^ m
        = 5 * rnP * (2 : ℝ) ^ (4 * n) * q ^ m := by
    dsimp [T]
    ring_nf
  have hpre1 :
      5 * (N : ℝ) ^ 2 * rnP * (2 : ℝ) ^ ℓ * (ℓ.choose k : ℝ) * (cQ / L) ^ m
        ≤ 5 * rnP * (2 : ℝ) ^ (4 * n) * q ^ m := by
    exact le_trans hstep1 (le_trans hstep2 hstep3.le)
  have hnonneg : 0 ≤ 5 * rnP * (2 : ℝ) ^ (4 * n) := by positivity
  have hpre2 :
      5 * rnP * (2 : ℝ) ^ (4 * n) * q ^ m
        ≤ 5 * rnP * (2 : ℝ) ^ (4 * n) * Real.exp (-K * (a * rn)) := by
    exact mul_le_mul_of_nonneg_left hqexp hnonneg
  -- exp identities
  have h2pow : (2 : ℝ) ^ (4 * n) = Real.exp ((4 * rn) * Real.log 2) := by
    dsimp [rn]
    rw [show (4 * (n : ℝ)) * Real.log 2 = ((4 * n : ℕ) : ℝ) * Real.log 2 by norm_num]
    rw [Real.exp_nat_mul (Real.log 2) (4 * n)]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hArg : (4 * rn) * Real.log 2 + -K * (a * rn) = -(M + 3) * rn := by
    calc
      (4 * rn) * Real.log 2 + -K * (a * rn)
          = (4 * Real.log 2) * rn + -(K * a) * rn := by ring
      _ = (4 * Real.log 2 - K * a) * rn := by ring
      _ = (4 * Real.log 2 - (M + 3 + 4 * Real.log 2)) * rn := by rw [hKa]
      _ = -(M + 3) * rn := by ring
  have hExp : Real.exp ((4 * rn) * Real.log 2) * Real.exp (-K * (a * rn)) =
      Real.exp (-(M + 3) * rn) := by
    rw [← Real.exp_add]
    exact congrArg Real.exp hArg
  have hExpCombine :
      5 * rnP * (2 : ℝ) ^ (4 * n) * Real.exp (-K * (a * rn))
        = 5 * rnP * Real.exp (-(M + 3) * rn) := by
    rw [h2pow]
    rw [mul_assoc (5 * rnP) (Real.exp ((4 * rn) * Real.log 2))
      (Real.exp (-K * (a * rn)))]
    rw [hExp]
  have hpre3 :
      5 * rnP * (2 : ℝ) ^ (4 * n) * q ^ m
        ≤ 5 * rnP * Real.exp (-(M + 3) * rn) := by
    exact le_trans hpre2 hExpCombine.le
  -- final
  have hSplit : Real.exp (-(M + 3) * rn) = Real.exp (-M * rn) * Real.exp (-3 * rn) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hFactor :
      5 * rnP * Real.exp (-(M + 3) * rn)
        = Real.exp (-M * rn) * (5 * rnP * Real.exp (-3 * rn)) := by
    rw [hSplit]
    ring_nf
  have hA : 5 * rnP * Real.exp (-3 * rn) ≤ 1 := by
    dsimp [rnP]
    exact five_sq_rpow52_exp_neg_three_le_one hrn8
  have hMexp0 : 0 ≤ Real.exp (-M * rn) := le_of_lt (Real.exp_pos (-M * rn))
  have hfinal :
      5 * rnP * Real.exp (-(M + 3) * rn) ≤ Real.exp (-M * rn) := by
    rw [hFactor]
    calc
      Real.exp (-M * rn) * (5 * rnP * Real.exp (-3 * rn))
          ≤ Real.exp (-M * rn) * 1 := by
              exact mul_le_mul_of_nonneg_left hA hMexp0
      _ = Real.exp (-M * rn) := by rw [mul_one]
  -- assemble
  have hpre4 : 5 * rnP * (2 : ℝ) ^ (4 * n) * q ^ m ≤ Real.exp (-M * rn) :=
    le_trans hpre3 hfinal
  have hgoal : 5 * (N : ℝ)^2 * rnP * (2 : ℝ)^ℓ * (ℓ.choose k : ℝ) * (cQ / L)^m
      ≤ Real.exp (-M * rn) := le_trans hpre1 hpre4
  constructor
  · exact hcQ_div_L_le_one
  · simpa [rn, rnP, k, j, m] using hgoal

end Commons.Analysis.Real