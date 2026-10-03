import Mathlib

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset

/-- The number of divisors of `c` is at most `2√c`. -/
lemma divisors_card_le_two_sqrt (c : ℕ) :
    ((c.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (c : ℝ) := by
  have hnat : c.divisors.card ≤ 2 * c.sqrt := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have hcard : c.divisors.card
          = (c.divisors.filter (fun d => d * d ≤ c)).card
            + (c.divisors.filter (fun d => ¬ d * d ≤ c)).card := by
        rw [Finset.card_filter_add_card_filter_not]
      have hBA : (c.divisors.filter (fun d => ¬ d * d ≤ c)).card
          ≤ (c.divisors.filter (fun d => d * d ≤ c)).card := by
        refine Finset.card_le_card_of_injOn (fun d => c / d) ?_ ?_
        · intro d hd
          simp only [Finset.mem_coe, Finset.mem_filter] at hd ⊢
          obtain ⟨hdmem, hd2⟩ := hd
          have hdvd : d ∣ c := (Nat.mem_divisors.mp hdmem).1
          have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
          have hdle : d ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hdvd
          have heq : d * (c / d) = c := Nat.mul_div_cancel' hdvd
          have hcd : c < d * d := Nat.lt_of_not_le hd2
          refine ⟨Nat.mem_divisors.mpr ⟨⟨d, (Nat.div_mul_cancel hdvd).symm⟩, hc0⟩, ?_⟩
          have hlt : c / d < d := by
            have h : d * (c / d) < d * d := by rw [heq]; exact hcd
            exact Nat.lt_of_mul_lt_mul_left h
          have hpos2 : 0 < c / d := Nat.div_pos hdle hdpos
          have hlt2 : (c / d) * (c / d) < d * (c / d) :=
            Nat.mul_lt_mul_of_pos_right hlt hpos2
          rw [heq] at hlt2
          omega
        · intro d hd e he heqe
          simp only [Finset.mem_coe, Finset.mem_filter] at hd he
          change c / d = c / e at heqe
          have hdvd : d ∣ c := (Nat.mem_divisors.mp hd.1).1
          have hevd : e ∣ c := (Nat.mem_divisors.mp he.1).1
          rw [← Nat.div_div_self hdvd hc0, ← Nat.div_div_self hevd hc0, heqe]
      have hAle : (c.divisors.filter (fun d => d * d ≤ c)).card ≤ c.sqrt := by
        have hsub : c.divisors.filter (fun d => d * d ≤ c) ⊆ Finset.Icc 1 c.sqrt := by
          intro d hd
          simp only [Finset.mem_filter] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_sqrt.mpr hd.2⟩
        calc (c.divisors.filter (fun d => d * d ≤ c)).card
            ≤ (Finset.Icc 1 c.sqrt).card := Finset.card_le_card hsub
          _ = c.sqrt := by rw [Nat.card_Icc]; omega
      omega
  calc ((c.divisors.card : ℕ) : ℝ) ≤ ((2 * c.sqrt : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 2 * (c.sqrt : ℝ) := by push_cast; ring
    _ ≤ 2 * Real.sqrt (c : ℝ) := by
        have hs : ((c.sqrt : ℕ) : ℝ) ≤ Real.sqrt (c : ℝ) := by
          rw [Real.le_sqrt (by positivity) (by positivity)]
          have h := Nat.sqrt_le c
          have hcast : ((c.sqrt : ℕ) : ℝ) ^ 2 = ((c.sqrt * c.sqrt : ℕ) : ℝ) := by
            push_cast; ring
          rw [hcast]; exact_mod_cast h
        linarith

/-- `τ(c)·log(c+2)·z` is dominated by `19·c·T^(76/77+2/r²)`. -/
lemma nc_log_z_le (c r T z : ℕ) (hc : 1 ≤ c) (hT : 1 ≤ T) (hr : 2 ≤ r)
    (hzle : (z : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2)) :
    ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
      ≤ 19 * ((c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)) := by
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hnc : ((c.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt (c : ℝ) :=
    divisors_card_le_two_sqrt c
  have hlog : Real.log ((c : ℝ) + 2) ≤ 2 * Real.sqrt 3 * Real.sqrt (c : ℝ) := by
    have hstep1 : Real.log ((c : ℝ) + 2) ≤ 2 * Real.sqrt ((c : ℝ) + 2) := by
      have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ (c : ℝ) + 2 by positivity)
        (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)
      have he : ((c : ℝ) + 2) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * Real.sqrt ((c : ℝ) + 2) := by
        rw [Real.sqrt_eq_rpow]; ring
      rwa [he] at h
    have hstep2 : Real.sqrt ((c : ℝ) + 2) ≤ Real.sqrt 3 * Real.sqrt (c : ℝ) := by
      have hle : (c : ℝ) + 2 ≤ 3 * (c : ℝ) := by linarith
      calc Real.sqrt ((c : ℝ) + 2) ≤ Real.sqrt (3 * (c : ℝ)) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt 3 * Real.sqrt (c : ℝ) := Real.sqrt_mul (by norm_num) (c : ℝ)
    calc Real.log ((c : ℝ) + 2) ≤ 2 * Real.sqrt ((c : ℝ) + 2) := hstep1
      _ ≤ 2 * (Real.sqrt 3 * Real.sqrt (c : ℝ)) := by linarith [hstep2]
      _ = 2 * Real.sqrt 3 * Real.sqrt (c : ℝ) := by ring
  have hnclog : ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) ≤ 4 * Real.sqrt 3 * (c : ℝ) := by
    have hlog_nn : 0 ≤ Real.log ((c : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ 2 * Real.sqrt (c : ℝ) := by positivity
    calc ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2)
        ≤ (2 * Real.sqrt (c : ℝ)) * (2 * Real.sqrt 3 * Real.sqrt (c : ℝ)) :=
          mul_le_mul hnc hlog hlog_nn h2
      _ = 4 * Real.sqrt 3 * (c : ℝ) := by
          rw [show (2:ℝ) * Real.sqrt (c:ℝ) * (2 * Real.sqrt 3 * Real.sqrt (c:ℝ))
                = 4 * Real.sqrt 3 * ((Real.sqrt (c:ℝ))^2) by ring]
          rw [Real.sq_sqrt (by positivity)]
  have hzle' : (z : ℝ) ≤ (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := by
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hpow : (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) ≤ (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hT1
      have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
      have h1 : (1 : ℝ) / (r : ℝ) ^ 2 ≤ 2 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hr2.le
      linarith
    exact le_trans hzle hpow
  have hz_nn : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  have hsqrt3_nn : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  calc ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
      ≤ (4 * Real.sqrt 3 * (c : ℝ)) * (z : ℝ) := mul_le_mul_of_nonneg_right hnclog hz_nn
    _ ≤ (4 * Real.sqrt 3 * (c : ℝ)) * ((T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hzle' (by positivity)
    _ = (4 * Real.sqrt 3) * ((c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)) := by ring
    _ ≤ 19 * ((c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)) := by
        have h419 : (4:ℝ) * Real.sqrt 3 ≤ 19 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hsqrt3_nn,
            sq_nonneg (Real.sqrt 3 - 2)]
        exact mul_le_mul_of_nonneg_right h419
          (mul_nonneg (Nat.cast_nonneg c) (Real.rpow_nonneg (Nat.cast_nonneg T) _))

/-- `T·z^(-1/12) ≤ 2^(1/12)·T^(1-1/(12r²))`. -/
lemma t_mul_zinv_le (r T z : ℕ) (hT : 1 ≤ T) (hr : 2 ≤ r)
    (hzle : (z : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2))
    (hzge : (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) / 2 ≤ (z : ℝ)) :
    (T : ℝ) * (z : ℝ) ^ (-(1 : ℝ) / 12)
      ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) * (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := by omega
    exact_mod_cast this
  have hrz : (0 : ℝ) < (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) := Real.rpow_pos_of_pos hTpos _
  have hx : (0 : ℝ) < (T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) / 2 :=
    div_pos hrz (by norm_num)
  have hstep1 : (z : ℝ) ^ (-(1 : ℝ) / 12)
      ≤ ((T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) / 2) ^ (-(1 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_nonpos hx hzge (by norm_num)
  have hstep2 : ((T : ℝ) ^ ((1 : ℝ) / (r : ℝ) ^ 2) / 2) ^ (-(1 : ℝ) / 12)
      = (2 : ℝ) ^ ((1 : ℝ) / 12) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2)) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (x := (T:ℝ)) (le_of_lt hTpos) ((1 : ℝ) / (r : ℝ) ^ 2) (-(1 : ℝ) / 12)]
    rw [← Real.rpow_neg_one (2:ℝ)]
    rw [← Real.rpow_mul (x := (2:ℝ)) (by norm_num : (0:ℝ) ≤ 2) (-(1:ℝ)) (-(1 : ℝ) / 12)]
    rw [show (1 : ℝ) / (r : ℝ) ^ 2 * (-(1 : ℝ) / 12) = -(1 : ℝ) / (12 * (r : ℝ) ^ 2) by
          field_simp,
        show (-(1 : ℝ)) * (-(1 : ℝ) / 12) = (1 : ℝ) / 12 by ring]
    ring
  calc (T : ℝ) * (z : ℝ) ^ (-(1 : ℝ) / 12)
      ≤ (T : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 12) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (le_trans hstep1 (le_of_eq hstep2)) (le_of_lt hTpos)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 12) * (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := by
        rw [show (T : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 12) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2)))
              = (2 : ℝ) ^ ((1 : ℝ) / 12) * ((T : ℝ) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2))) by ring]
        rw [show (T : ℝ) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2))
              = (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ (-(1 : ℝ) / (12 * (r : ℝ) ^ 2)) by
                rw [Real.rpow_one]]
        rw [← Real.rpow_add hTpos]
        rw [show (1 : ℝ) + (-(1 : ℝ) / (12 * (r : ℝ) ^ 2)) = 1 - 1 / (12 * (r : ℝ) ^ 2) by ring]

/-- `T^(23/24)·D^(1/12) ≤ c·T^(76/77+2/r²) + T^(23/24) + T^(1-1/(12r²))`. -/
lemma t23_D12_le (c r T D : ℕ) (hT : 1 ≤ T) (hr : 2 ≤ r) (hc : 1 ≤ c)
    (hDpow : (D : ℝ) ^ ((1 : ℝ) / 12) ≤ (T : ℝ) ^ ((1 : ℝ) / (6 * (r : ℝ)))) :
    (T : ℝ) ^ ((23 : ℝ) / 24) * (D : ℝ) ^ ((1 : ℝ) / 12)
      ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) + (T : ℝ) ^ ((23 : ℝ) / 24)
          + (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := by omega
    exact_mod_cast this
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hstep1 : (T : ℝ) ^ ((23 : ℝ) / 24) * (D : ℝ) ^ ((1 : ℝ) / 12)
      ≤ (T : ℝ) ^ ((23 : ℝ) / 24 + 1 / (6 * (r : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hDpow (Real.rpow_nonneg hTpos.le ((23 : ℝ) / 24))
    rwa [← Real.rpow_add hTpos] at h
  have hexp : (23 : ℝ) / 24 + 1 / (6 * (r : ℝ)) ≤ (76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2 := by
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    field_simp
    nlinarith [sq_nonneg ((r : ℝ) - 3), sq_nonneg (r : ℝ)]
  have hstep2 : (T : ℝ) ^ ((23 : ℝ) / 24 + 1 / (6 * (r : ℝ)))
      ≤ (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have hstep3 : (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)
      ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := by
    have hnn := Real.rpow_nonneg hTpos.le ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2)
    simpa using mul_le_mul_of_nonneg_right hcR hnn
  have h1 : (0 : ℝ) ≤ (T : ℝ) ^ ((23 : ℝ) / 24) := Real.rpow_nonneg hTpos.le _
  have h2 : (0 : ℝ) ≤ (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := Real.rpow_nonneg hTpos.le _
  calc (T : ℝ) ^ ((23 : ℝ) / 24) * (D : ℝ) ^ ((1 : ℝ) / 12)
      ≤ (T : ℝ) ^ ((23 : ℝ) / 24 + 1 / (6 * (r : ℝ))) := hstep1
    _ ≤ (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := hstep2
    _ ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := hstep3
    _ ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) + (T : ℝ) ^ ((23 : ℝ) / 24)
          + (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := by linarith

/-- `c·T^(76/77)·z² ≤ c·T^(76/77+2/r²) + T^(23/24) + T^(1-1/(12r²))`. -/
lemma c_T76_z2_le (c r T z : ℕ) (hT : 1 ≤ T) (hr : 2 ≤ r)
    (hzsq : (z : ℝ) ^ 2 ≤ (T : ℝ) ^ ((2 : ℝ) / (r : ℝ) ^ 2)) :
    (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
      ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) + (T : ℝ) ^ ((23 : ℝ) / 24)
          + (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := by omega
    exact_mod_cast this
  have hstep : (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
      ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := by
    have hbase : (0 : ℝ) ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) :=
      mul_nonneg (Nat.cast_nonneg c) (Real.rpow_nonneg hTpos.le _)
    have h1 : (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
        ≤ (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) * (T : ℝ) ^ ((2 : ℝ) / (r : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hzsq hbase
    have h2 : (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77) * (T : ℝ) ^ ((2 : ℝ) / (r : ℝ) ^ 2)
        = (c : ℝ) * (T : ℝ) ^ ((76 : ℝ) / 77 + 2 / (r : ℝ) ^ 2) := by
      rw [mul_assoc, ← Real.rpow_add hTpos]
    linarith [h1, h2.le, h2.ge]
  have h1 : (0 : ℝ) ≤ (T : ℝ) ^ ((23 : ℝ) / 24) := Real.rpow_nonneg hTpos.le _
  have h2 : (0 : ℝ) ≤ (T : ℝ) ^ (1 - 1 / (12 * (r : ℝ) ^ 2)) := Real.rpow_nonneg hTpos.le _
  linarith [hstep, h1, h2]

theorem bound_combine (c d r T z D : ℕ) (k : ℤ) (b a K : ℝ)
    (C1 A1 C2 A2 C3 A3 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hA3 : 0 < A3)
    (hT : 1 ≤ T) (hr : 2 ≤ r) (hc : 1 ≤ c) (hd : 1 ≤ d) (hK : 0 ≤ K)
    (hzle : (z:ℝ) ≤ (T:ℝ)^((1:ℝ)/(r:ℝ)^2))
    (hzge : (T:ℝ)^((1:ℝ)/(r:ℝ)^2) / 2 ≤ (z:ℝ))
    (hzsq : (z:ℝ)^2 ≤ (T:ℝ)^((2:ℝ)/(r:ℝ)^2))
    (hDpow : (D:ℝ)^((1:ℝ)/12) ≤ (T:ℝ)^((1:ℝ)/(6*(r:ℝ)))) :
    C1 * ((c.divisors.card : ℕ) : ℝ) * (T:ℝ)^((23:ℝ)/24) * (D:ℝ)^((1:ℝ)/12)
        * (Real.log ((T:ℝ)+2))^A1 * (K * |b-a| + 1)
    + C3 * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ) * (|(k:ℝ)|+1)
        * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77) * (z:ℝ)^2
            + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c:ℝ)+2) * (z:ℝ))
        * (Real.log ((T:ℝ)+2))^A3 * (K * |b-a| + 1)
    + C2 * ((c.divisors.card : ℕ) : ℝ) * (T:ℝ) * (z:ℝ)^(-(1:ℝ)/12)
        * (Real.log ((T:ℝ)+2))^A2 * (K * |b-a| + 1)
    ≤ (C1 + C2 * (2:ℝ)^((1:ℝ)/12) + 20*C3) * (d:ℝ) * (((c*d).divisors.card : ℕ) : ℝ)
        * (|(k:ℝ)|+1)
        * ((c:ℝ) * (T:ℝ)^((76:ℝ)/77 + 2/(r:ℝ)^2) + (T:ℝ)^((23:ℝ)/24)
            + (T:ℝ)^(1 - 1/(12*(r:ℝ)^2)))
        * (Real.log ((T:ℝ)+2))^(max A1 (max A2 A3) + 1) * (K * |b-a| + 1) := by
  set nc : ℝ := ((c.divisors.card : ℕ) : ℝ) with hnc
  set ncd : ℝ := (((c*d).divisors.card : ℕ) : ℝ) with hncd
  set dd : ℝ := (d : ℝ) with hdd
  set bd : ℝ := (|(k:ℝ)| + 1) with hbd
  set L : ℝ := Real.log ((T:ℝ) + 2) with hL
  set Pv : ℝ := K * |b-a| + 1 with hPv
  set T23 : ℝ := (T:ℝ)^((23:ℝ)/24) with hT23
  set D12 : ℝ := (D:ℝ)^((1:ℝ)/12) with hD12
  set T76 : ℝ := (T:ℝ)^((76:ℝ)/77) with hT76
  set TB : ℝ := (T:ℝ)^((76:ℝ)/77 + 2/(r:ℝ)^2) with hTB
  set TC : ℝ := (T:ℝ)^(1 - 1/(12*(r:ℝ)^2)) with hTC
  set zinv : ℝ := (z:ℝ)^(-(1:ℝ)/12) with hzinv
  set zsqv : ℝ := (z:ℝ)^2 with hzsqv
  set lc : ℝ := Real.log ((c:ℝ) + 2) with hlc
  set two12 : ℝ := (2:ℝ)^((1:ℝ)/12) with htwo12
  set Bv : ℝ := (c:ℝ) * TB + T23 + TC with hBv
  set MM : ℝ := max A1 (max A2 A3) with hMM
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := by omega
    exact_mod_cast this
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hd1 : (1 : ℝ) ≤ dd := by rw [hdd]; exact_mod_cast hd
  -- nonnegativity facts
  have hnc_nn : 0 ≤ nc := by rw [hnc]; positivity
  have hncd_nn : 0 ≤ ncd := by rw [hncd]; positivity
  have hdd_nn : 0 ≤ dd := by rw [hdd]; positivity
  have hbd_nn : 0 ≤ bd := by rw [hbd]; positivity
  have hPv_nn : 0 ≤ Pv := by rw [hPv]; positivity
  have hbd1 : (1 : ℝ) ≤ bd := by rw [hbd]; have := abs_nonneg (k:ℝ); linarith
  have hT23_nn : 0 ≤ T23 := by rw [hT23]; exact Real.rpow_nonneg hT0 _
  have hD12_nn : 0 ≤ D12 := by rw [hD12]; exact Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hT76_nn : 0 ≤ T76 := by rw [hT76]; exact Real.rpow_nonneg hT0 _
  have hTB_nn : 0 ≤ TB := by rw [hTB]; exact Real.rpow_nonneg hT0 _
  have hTC_nn : 0 ≤ TC := by rw [hTC]; exact Real.rpow_nonneg hT0 _
  have hzinv_nn : 0 ≤ zinv := by rw [hzinv]; exact Real.rpow_nonneg (Nat.cast_nonneg z) _
  have hlc_nn : 0 ≤ lc := by rw [hlc]; exact Real.log_nonneg (by linarith)
  have htwo12_nn : 0 ≤ two12 := by rw [htwo12]; exact Real.rpow_nonneg (by norm_num) _
  have hL_nn : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity : (0:ℝ) < (T:ℝ) + 2)]
    have h3 : (3:ℝ) ≤ (T:ℝ) + 2 := by linarith
    linarith [Real.exp_one_lt_three]
  have hBv_nn : 0 ≤ Bv := by
    rw [hBv]
    exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg c) hTB_nn) hT23_nn) hTC_nn
  have hT23D12_nn : 0 ≤ T23 * D12 := mul_nonneg hT23_nn hD12_nn
  have hddncdbd_nn : 0 ≤ dd * ncd * bd := mul_nonneg (mul_nonneg hdd_nn hncd_nn) hbd_nn
  have hA1le : A1 ≤ MM + 1 := by rw [hMM]; linarith [le_max_left A1 (max A2 A3)]
  have hA2le : A2 ≤ MM + 1 := by
    rw [hMM]
    have h1 := le_max_right A1 (max A2 A3)
    have h2 := le_max_left A2 A3
    linarith
  have hA3le : A3 ≤ MM + 1 := by
    rw [hMM]
    have h1 := le_max_right A1 (max A2 A3)
    have h2 := le_max_right A2 A3
    linarith
  have hLpA1 : L^A1 ≤ L^(MM+1) := Real.rpow_le_rpow_of_exponent_le hL1 hA1le
  have hLpA2 : L^A2 ≤ L^(MM+1) := Real.rpow_le_rpow_of_exponent_le hL1 hA2le
  have hLpA3 : L^A3 ≤ L^(MM+1) := Real.rpow_le_rpow_of_exponent_le hL1 hA3le
  have hLpA1_nn : 0 ≤ L^A1 := Real.rpow_nonneg hL_nn _
  have hLpA2_nn : 0 ≤ L^A2 := Real.rpow_nonneg hL_nn _
  have hLpA3_nn : 0 ≤ L^A3 := Real.rpow_nonneg hL_nn _
  -- divisor monotonicity
  have hncd : nc ≤ ncd := by
    rw [hnc, hncd]
    have hcdvd : c ∣ c * d := ⟨d, by ring⟩
    have hcd0 : c * d ≠ 0 := by
      have hc0 : c ≠ 0 := by omega
      have hd0 : d ≠ 0 := by omega
      exact Nat.mul_ne_zero hc0 hd0
    have hsub : c.divisors ⊆ (c*d).divisors := Nat.divisors_subset_of_dvd hcd0 hcdvd
    have h := Finset.card_le_card hsub
    exact_mod_cast h
  have hnc_le : nc ≤ dd * ncd * bd := by
    have h1 : ncd ≤ dd * ncd := by simpa using mul_le_mul_of_nonneg_right hd1 hncd_nn
    have h2 : dd * ncd ≤ dd * ncd * bd := by
      simpa using mul_le_mul_of_nonneg_left hbd1 (mul_nonneg hdd_nn hncd_nn)
    linarith [hncd, h1, h2]
  -- core arithmetic
  have hTD : T23 * D12 ≤ Bv := by
    rw [hT23, hD12, hBv, hTB, hT23, hTC]
    exact t23_D12_le c r T D hT hr hc hDpow
  have hCT : (c:ℝ) * T76 * zsqv ≤ Bv := by
    rw [hT76, hzsqv, hBv, hTB, hT23, hTC]
    exact c_T76_z2_le c r T z hT hr hzsq
  have hTzi : (T:ℝ) * zinv ≤ two12 * TC := by
    rw [hzinv, htwo12, hTC]
    exact t_mul_zinv_le r T z hT hr hzle hzge
  have hTC_le_Bv : TC ≤ Bv := by
    rw [hBv]; linarith [hT23_nn, mul_nonneg (by positivity : (0:ℝ) ≤ (c:ℝ)) hTB_nn]
  have hTz_nn : 0 ≤ (T:ℝ) * zinv := mul_nonneg hTpos.le hzinv_nn
  have hTz : (T:ℝ) * zinv ≤ two12 * Bv :=
    le_trans hTzi (mul_le_mul_of_nonneg_left hTC_le_Bv htwo12_nn)
  have hNCL0 : nc * lc * (z:ℝ) ≤ 19 * ((c:ℝ) * TB) := by
    rw [hnc, hlc, hTB]
    exact nc_log_z_le c r T z hc hT hr hzle
  have hcTB_le : (c:ℝ) * TB ≤ Bv := by rw [hBv]; linarith [hT23_nn, hTC_nn]
  have hNCLz : nc * lc * (z:ℝ) ≤ 19 * Bv :=
    le_trans hNCL0 (mul_le_mul_of_nonneg_left hcTB_le (by norm_num : (0:ℝ) ≤ 19))
  -- term bounds
  have hcore1 : nc * T23 * D12 * L^A1 * Pv ≤ dd * ncd * bd * Bv * L^(MM+1) * Pv := by
    calc nc * T23 * D12 * L^A1 * Pv
        = (nc * (T23 * D12)) * (L^A1 * Pv) := by ring
      _ ≤ ((dd * ncd * bd) * Bv) * (L^(MM+1) * Pv) := by
          apply mul_le_mul
          · exact mul_le_mul hnc_le hTD hT23D12_nn hddncdbd_nn
          · exact mul_le_mul_of_nonneg_right hLpA1 hPv_nn
          · exact mul_nonneg hLpA1_nn hPv_nn
          · exact mul_nonneg hddncdbd_nn hBv_nn
      _ = dd * ncd * bd * Bv * L^(MM+1) * Pv := by ring
  have hcore2 : dd * ncd * bd * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ)) * L^A3 * Pv
      ≤ 20 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by
    have hsum20 : (c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ) ≤ 20 * Bv := by
      linarith [hCT, hNCLz]
    calc dd * ncd * bd * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ)) * L^A3 * Pv
        = ((dd * ncd * bd) * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ))) * (L^A3 * Pv) := by ring
      _ ≤ ((dd * ncd * bd) * (20 * Bv)) * (L^(MM+1) * Pv) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hsum20 hddncdbd_nn
          · exact mul_le_mul_of_nonneg_right hLpA3 hPv_nn
          · exact mul_nonneg hLpA3_nn hPv_nn
          · exact mul_nonneg hddncdbd_nn (by linarith [hBv_nn])
      _ = 20 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by ring
  have hcore3 : nc * (T:ℝ) * zinv * L^A2 * Pv ≤ two12 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by
    calc nc * (T:ℝ) * zinv * L^A2 * Pv
        = (nc * ((T:ℝ) * zinv)) * (L^A2 * Pv) := by ring
      _ ≤ (dd * ncd * bd * (two12 * Bv)) * (L^(MM+1) * Pv) := by
          apply mul_le_mul
          · exact mul_le_mul hnc_le hTz hTz_nn hddncdbd_nn
          · exact mul_le_mul_of_nonneg_right hLpA2 hPv_nn
          · exact mul_nonneg hLpA2_nn hPv_nn
          · exact mul_nonneg hddncdbd_nn (mul_nonneg htwo12_nn hBv_nn)
      _ = two12 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by ring
  have ht1 : C1 * nc * T23 * D12 * L^A1 * Pv ≤ C1 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by
    rw [show C1 * nc * T23 * D12 * L^A1 * Pv = C1 * (nc * T23 * D12 * L^A1 * Pv) by ring]
    exact mul_le_mul_of_nonneg_left hcore1 (le_of_lt hC1)
  have ht2 : C3 * dd * ncd * bd * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ)) * L^A3 * Pv
      ≤ 20 * C3 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by
    rw [show C3 * dd * ncd * bd * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ)) * L^A3 * Pv
          = C3 * (dd * ncd * bd * ((c:ℝ) * T76 * zsqv + nc * lc * (z:ℝ)) * L^A3 * Pv) by ring]
    have h := mul_le_mul_of_nonneg_left hcore2 (le_of_lt hC3)
    refine le_trans h (le_of_eq ?_)
    ring
  have ht3 : C2 * nc * (T:ℝ) * zinv * L^A2 * Pv
      ≤ C2 * two12 * (dd * ncd * bd * Bv * L^(MM+1) * Pv) := by
    rw [show C2 * nc * (T:ℝ) * zinv * L^A2 * Pv
          = C2 * (nc * (T:ℝ) * zinv * L^A2 * Pv) by ring]
    have h := mul_le_mul_of_nonneg_left hcore3 (le_of_lt hC2)
    refine le_trans h (le_of_eq ?_)
    ring
  have hsum := add_le_add (add_le_add ht1 ht2) ht3
  refine le_trans hsum (le_of_eq ?_)
  ring

end Work.FIArea7.smallCInner2EpsAux
