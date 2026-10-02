import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundKeptUnactDefs

/-!
# `Work.Deep.Kahn.keptUnactThresh`

The comparison between the (exact) mean `D * (1 - 1/K) * (1 - 1/(KΛ))^((C-1)(D-1))` of
`keptUnactCount ω x γ` and the threshold `(1 - 1/K) * retentionU Λ C D K * D + ηD/4` of the bad
event `badKeptSet`:

  `mean + ηD/8 ≤ threshold`.

The exact blocker count is `(C-1)(D-1)` while `retentionU` uses the larger exponent
`D(C-1) = (C-1)(D-1) + (C-1)`; Bernoulli's inequality bounds the difference by
`(C-1)/(KΛ) ≤ η/8` in the regime `C ≤ D^{1/9}`, `K ≥ 2`, `Λ ≥ D`, `η ≥ D^{-1/9}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Deep.Kahn

noncomputable section

/-- `10^a ≤ 10^b` for `a ≤ b` (real exponents). -/
lemma ten_rpow_mono'' {a b : ℝ} (h : a ≤ b) : (10 : ℝ) ^ a ≤ (10 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr h

/-- `((10:ℝ)^100)^c = 10^{100 c}`. -/
lemma ten_pow_rpow'' (c : ℝ) : ((10 : ℝ) ^ 100) ^ c = (10 : ℝ) ^ (100 * c) := by
  rw [← Real.rpow_natCast (10 : ℝ) 100, ← Real.rpow_mul (x := (10 : ℝ)) (by norm_num)]
  norm_num

/-- In the regime `D ≥ 10^100`, `t ≤ D^c` whenever `t ≤ 10^{100 c}`. -/
lemma rpow_ge_of_ten'' {D : ℕ} {c t : ℝ} (hc : 0 ≤ c) (hD : (10 : ℝ) ^ 100 ≤ (D : ℝ))
    (ht : t ≤ (10 : ℝ) ^ (100 * c)) : t ≤ (D : ℝ) ^ c := by
  refine le_trans ht ?_
  rw [← ten_pow_rpow'' c]
  exact Real.rpow_le_rpow (by positivity) hD hc

theorem keptUnactThresh {C D Λ K : ℕ} {ε η : ℝ}
    (hC : 2 ≤ C) (hε : 0 < ε) (hη : 0 < η) (hD1 : 1 ≤ D) (hΛ1 : 1 ≤ Λ) (hK2 : 2 ≤ K)
    (hηK : η * (K : ℝ) ≤ 1)
    (hDΛ : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (hD : (10 : ℝ) ^ 100 ≤ (D : ℝ))
    (hCK : ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9)) :
    (D : ℝ) * (1 - 1 / (K : ℝ)) * (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ ((C - 1) * (D - 1))
        + η * (D : ℝ) / 8
      ≤ (1 - 1 / (K : ℝ)) * retentionU Λ C D K * (D : ℝ) + η * (D : ℝ) / 4 := by
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le (by positivity) hD
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := hDpos.le
  have hD1' : (1 : ℝ) ≤ (D : ℝ) :=
    le_trans (by norm_num : (1 : ℝ) ≤ (10 : ℝ) ^ 100) hD
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
    linarith
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := lt_of_lt_of_le (mul_pos (by linarith) hDpos) hDΛ
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hKLpos : (0 : ℝ) < (K : ℝ) * (Λ : ℝ) := mul_pos hKpos hΛpos
  have hΛD : (D : ℝ) ≤ (Λ : ℝ) := by
    have h1 : (D : ℝ) ≤ (1 + ε) * (D : ℝ) := by
      have h2 : (1 : ℝ) ≤ 1 + ε := by linarith
      nlinarith
    linarith
  -- the base `1 - q`
  set q : ℝ := 1 / ((K : ℝ) * (Λ : ℝ)) with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hKLpos]
    exact one_le_mul_of_one_le_of_one_le hK1 (by exact_mod_cast hΛ1)
  have hb0 : (0 : ℝ) ≤ 1 - q := by linarith
  have hb1 : 1 - q ≤ 1 := by linarith
  have hbase : 1 - (1 / (K : ℝ)) / (Λ : ℝ) = 1 - q := by rw [hqdef, div_div]
  have hret : retentionU Λ C D K = (1 - q) ^ (D * (C - 1)) := by rw [retentionU, hbase]
  have hexp : D * (C - 1) = (C - 1) * (D - 1) + (C - 1) := by
    have h : D = (D - 1) + 1 := by omega
    have h2 : (C - 1) * D = (C - 1) * ((D - 1) + 1) := congrArg (fun m => (C - 1) * m) h
    rw [Nat.mul_comm D (C - 1), h2, Nat.mul_succ]
  -- `η ≥ D^{-1/9}`
  have heta : (D : ℝ) ^ (-((1 : ℝ) / 9)) ≤ η := by
    have h1 : η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
      have h2 : (0 : ℝ) ≤ (C : ℝ) + (K : ℝ) := by positivity
      linarith
    have hXpos : (0 : ℝ) < (D : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hDpos _
    have h2 : ((D : ℝ) ^ ((1 : ℝ) / 9))⁻¹ ≤ η := (inv_le_comm₀ hXpos hη).mpr h1
    calc (D : ℝ) ^ (-((1 : ℝ) / 9)) = ((D : ℝ) ^ ((1 : ℝ) / 9))⁻¹ := by
          rw [Real.rpow_neg hDpos.le]
      _ ≤ η := h2
  -- `4 ≤ D^{7/9}`
  have hD79 : (4 : ℝ) ≤ (D : ℝ) ^ ((7 : ℝ) / 9) := by
    refine rpow_ge_of_ten'' (by norm_num) hD ?_
    have h2 : (4 : ℝ) ≤ (10 : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    exact le_trans h2 (ten_rpow_mono'' (by norm_num))
  -- `(C-1) q ≤ η/8`
  have hCkey : ((C - 1 : ℕ) : ℝ) * q ≤ η / 8 := by
    have hCle : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
      have h2 : (0 : ℝ) ≤ (K : ℝ) + η⁻¹ := by positivity
      linarith
    have hC1le : ((C - 1 : ℕ) : ℝ) ≤ (C : ℝ) := by
      exact_mod_cast (Nat.sub_le C 1)
    have hD19pos : (0 : ℝ) < (D : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hDpos _
    have h2Dpos : (0 : ℝ) < 2 * (D : ℝ) := by positivity
    have hqle : q ≤ (2 * (D : ℝ))⁻¹ := by
      rw [hqdef, inv_eq_one_div, div_le_div_iff₀ hKLpos h2Dpos]
      have h2 : 2 * (D : ℝ) ≤ (K : ℝ) * (Λ : ℝ) :=
        calc 2 * (D : ℝ) ≤ (K : ℝ) * (D : ℝ) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hK2 : (2 : ℝ) ≤ (K : ℝ)) hDnn
          _ ≤ (K : ℝ) * (Λ : ℝ) := mul_le_mul_of_nonneg_left hΛD hKpos.le
      linarith
    have hstep1 : ((C - 1 : ℕ) : ℝ) * q ≤ (D : ℝ) ^ ((1 : ℝ) / 9) * (2 * (D : ℝ))⁻¹ :=
      mul_le_mul (le_trans hC1le hCle) hqle hq0 hD19pos.le
    have heq : 8 * ((D : ℝ) ^ ((1 : ℝ) / 9) * (2 * (D : ℝ))⁻¹)
        = 4 * (D : ℝ) ^ (-((8 : ℝ) / 9)) := by
      have h2 : (D : ℝ) ^ (-((8 : ℝ) / 9)) * (D : ℝ) = (D : ℝ) ^ ((1 : ℝ) / 9) := by
        have h3 : (D : ℝ) ^ (-((8 : ℝ) / 9)) * (D : ℝ)
            = (D : ℝ) ^ (-((8 : ℝ) / 9)) * (D : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        rw [h3, ← Real.rpow_add hDpos]
        norm_num
      rw [← h2]
      field_simp
      ring
    have hmain : 8 * ((D : ℝ) ^ ((1 : ℝ) / 9) * (2 * (D : ℝ))⁻¹) ≤ η := by
      rw [heq]
      have h5 : 4 * (D : ℝ) ^ (-((8 : ℝ) / 9))
          ≤ (D : ℝ) ^ ((7 : ℝ) / 9) * (D : ℝ) ^ (-((8 : ℝ) / 9)) :=
        mul_le_mul_of_nonneg_right hD79 (Real.rpow_nonneg hDnn _)
      have h6 : (D : ℝ) ^ ((7 : ℝ) / 9) * (D : ℝ) ^ (-((8 : ℝ) / 9))
          = (D : ℝ) ^ (-((1 : ℝ) / 9)) := by
        rw [← Real.rpow_add hDpos]; norm_num
      linarith [h5, h6, heta]
    linarith [hstep1, hmain]
  -- Bernoulli: `1 - (1-q)^{C-1} ≤ (C-1) q`
  have hbern : (1 : ℝ) - (1 - q) ^ (C - 1) ≤ ((C - 1 : ℕ) : ℝ) * q := by
    have h1 : (1 : ℝ) + ((C - 1 : ℕ) : ℝ) * (-q) ≤ (1 + (-q)) ^ (C - 1) :=
      one_add_mul_le_pow (a := -q) (by linarith : -2 ≤ -q) (C - 1)
    have h2 : (1 : ℝ) + (-q) = 1 - q := by ring
    rw [h2] at h1
    linarith
  have hbC1 : (1 - q) ^ (C - 1) ≤ 1 := pow_le_one₀ hb0 hb1
  have hY0 : (0 : ℝ) ≤ (1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)) := by
    have hpow : (1 - q) ^ (D * (C - 1)) ≤ (1 - q) ^ ((C - 1) * (D - 1)) := by
      have h1 : (1 - q) ^ (D * (C - 1))
          = (1 - q) ^ ((C - 1) * (D - 1)) * (1 - q) ^ (C - 1) := by rw [hexp, pow_add]
      rw [h1]
      calc (1 - q) ^ ((C - 1) * (D - 1)) * (1 - q) ^ (C - 1)
          ≤ (1 - q) ^ ((C - 1) * (D - 1)) * 1 :=
            mul_le_mul_of_nonneg_left hbC1 (pow_nonneg hb0 _)
        _ = (1 - q) ^ ((C - 1) * (D - 1)) := by ring
    linarith
  have hΔ : (1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))
      ≤ ((C - 1 : ℕ) : ℝ) * q := by
    have h1 : (1 - q) ^ (D * (C - 1))
        = (1 - q) ^ ((C - 1) * (D - 1)) * (1 - q) ^ (C - 1) := by rw [hexp, pow_add]
    have h2 : (0 : ℝ) ≤ 1 - (1 - q) ^ (C - 1) := by linarith
    have h3 : (1 - q) ^ ((C - 1) * (D - 1)) ≤ 1 := pow_le_one₀ hb0 hb1
    calc (1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))
        = (1 - q) ^ ((C - 1) * (D - 1)) * (1 - (1 - q) ^ (C - 1)) := by rw [h1]; ring
      _ ≤ 1 * (((C - 1 : ℕ) : ℝ) * q) := mul_le_mul h3 hbern h2 (by norm_num)
      _ = ((C - 1 : ℕ) : ℝ) * q := by ring
  -- the three-step gap
  have hX0 : (0 : ℝ) ≤ 1 - 1 / (K : ℝ) := by
    rw [sub_nonneg]; exact (div_le_one hKpos).mpr hK1
  have hX1 : 1 - 1 / (K : ℝ) ≤ 1 := by
    rw [sub_le_self_iff]; exact div_nonneg (by norm_num) hKpos.le
  have hgap : (D : ℝ) * (1 - 1 / (K : ℝ))
        * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)))
      ≤ η * (D : ℝ) / 8 := by
    have h1 : (D : ℝ) * (1 - 1 / (K : ℝ))
          * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)))
        ≤ (D : ℝ) * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))) := by
      have h2 := mul_le_mul_of_nonneg_left hX1 hDnn
      calc (D : ℝ) * (1 - 1 / (K : ℝ))
            * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)))
          = ((D : ℝ) * (1 - 1 / (K : ℝ)))
            * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))) := by ring
        _ ≤ ((D : ℝ) * 1)
            * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))) :=
              mul_le_mul_of_nonneg_right h2 hY0
        _ = (D : ℝ) * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1))) := by ring
    have h3 : (D : ℝ) * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)))
        ≤ (D : ℝ) * (((C - 1 : ℕ) : ℝ) * q) := mul_le_mul_of_nonneg_left hΔ hDnn
    have h4 : (D : ℝ) * (((C - 1 : ℕ) : ℝ) * q) ≤ η * (D : ℝ) / 8 := by
      have h5 := mul_le_mul_of_nonneg_left hCkey hDnn
      linarith
    linarith [h1, h3, h4]
  -- conclude
  have hid : (D : ℝ) * (1 - 1 / (K : ℝ))
        * ((1 - q) ^ ((C - 1) * (D - 1)) - (1 - q) ^ (D * (C - 1)))
      = (D : ℝ) * (1 - 1 / (K : ℝ)) * (1 - q) ^ ((C - 1) * (D - 1))
        - (1 - 1 / (K : ℝ)) * (1 - q) ^ (D * (C - 1)) * (D : ℝ) := by ring
  rw [hret]
  rw [hqdef] at hgap hid ⊢
  linarith [hgap, hid]

end

end Work.Deep.Kahn
