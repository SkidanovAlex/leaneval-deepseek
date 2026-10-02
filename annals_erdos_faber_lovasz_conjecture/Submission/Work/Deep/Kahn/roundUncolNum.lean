import Submission.Work.ConeSwitch.MathlibNoHG

/-!
# `Work.Deep.Kahn.num_eta`, `Work.Deep.Kahn.num_exc`

The two numeric lemmas behind the concentration argument for `uncolActCount`, in the regime
`D ≥ 10^1000`:

* `num_eta`: with `c = C + ℓ + 2 ≤ 3 D^{1/4}` and `D^{-1/9} ≤ η`, the deviation level
  `t = ηD/4` satisfies `50 c √(4D) < t` and `D^{1/4} + log 16 ≤ t²/(16 c² (4D))`;
* `num_exc`: `D Λ (1/32)^ℓ ≤ exp(-D^{1/4})/16` and `exp(-D^{1/4})/16 ≤ 1/D²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators

namespace Work.Deep.Kahn

noncomputable section

/-! ## Elementary bounds -/

lemma exp_two_lt_ten : Real.exp 2 < 10 := by
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h2]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

lemma log_ten_ge_two : (2 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10)]
  exact le_of_lt exp_two_lt_ten

lemma log_thirtytwo_ge_three : (3 : ℝ) ≤ Real.log 32 := by
  have h : (3 : ℝ) ≤ Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    have h2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    push_cast
    linarith
  exact h

/-- `log D ≥ 2000` in the regime `D ≥ 10^1000`. -/
lemma log_D_ge {D : ℕ} (h : (10 : ℝ) ^ 1000 ≤ (D : ℝ)) : (2000 : ℝ) ≤ Real.log (D : ℝ) := by
  have hDpos : (0 : ℝ) < (D : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (10 : ℝ) ^ 1000) h
  have h1 : Real.log ((10 : ℝ) ^ 1000) ≤ Real.log (D : ℝ) :=
    Real.log_le_log (by positivity) h
  have h2 : Real.log ((10 : ℝ) ^ 1000) = 1000 * Real.log 10 := by
    rw [Real.log_pow]; push_cast; ring
  rw [h2] at h1
  have h3 : (2000 : ℝ) ≤ 1000 * Real.log 10 := by
    have := log_ten_ge_two
    linarith
  linarith

/-- The logarithm grows at most like `x^{1/8}`. -/
lemma log_le_eight_rpow {x : ℝ} (hx : 0 < x) : Real.log x ≤ 8 * x ^ ((1 : ℝ) / 8) := by
  have h1 : Real.log (x ^ ((1 : ℝ) / 8)) = (1 / 8) * Real.log x := Real.log_rpow hx _
  have h2 : Real.log (x ^ ((1 : ℝ) / 8)) ≤ x ^ ((1 : ℝ) / 8) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx _)
  rw [h1] at h2
  have h3 : (0 : ℝ) < x ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hx _
  nlinarith

/-- `(10^1000)^c = 10^{1000 c}`. -/
lemma ten_pow_rpow (c : ℝ) : ((10 : ℝ) ^ 1000) ^ c = (10 : ℝ) ^ (1000 * c) := by
  rw [← Real.rpow_natCast (10 : ℝ) 1000, ← Real.rpow_mul (x := (10 : ℝ)) (by norm_num)]
  norm_num

/-- In the regime `D ≥ 10^1000`, `t < D^c` whenever `t < 10^{1000 c}`. -/
lemma rpow_lt_of_ten {D : ℕ} {c t : ℝ} (hc : 0 ≤ c) (hD : (10 : ℝ) ^ 1000 ≤ (D : ℝ))
    (ht : t < (10 : ℝ) ^ (1000 * c)) : t < (D : ℝ) ^ c := by
  refine lt_of_lt_of_le ht ?_
  rw [← ten_pow_rpow c]
  exact Real.rpow_le_rpow (by positivity) hD hc

/-- In the regime `D ≥ 10^1000`, `t ≤ D^c` whenever `t ≤ 10^{1000 c}`. -/
lemma rpow_ge_of_ten {D : ℕ} {c t : ℝ} (hc : 0 ≤ c) (hD : (10 : ℝ) ^ 1000 ≤ (D : ℝ))
    (ht : t ≤ (10 : ℝ) ^ (1000 * c)) : t ≤ (D : ℝ) ^ c := by
  refine le_trans ht ?_
  rw [← ten_pow_rpow c]
  exact Real.rpow_le_rpow (by positivity) hD hc

/-- `10^a ≤ 10^b` for `a ≤ b`. -/
lemma ten_rpow_mono {a b : ℝ} (h : a ≤ b) : (10 : ℝ) ^ a ≤ (10 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr h

/-! ## The two numeric bounds -/

/-- **The deviation level beats the Bruhn--Joos thresholds.** -/
theorem num_eta {C D K ℓ : ℕ} {η : ℝ} (hC : 2 ≤ C) (hη : 0 < η) (hK : 2 ≤ K)
    (hηK : η * (K : ℝ) ≤ 1) (hDmin : (10 : ℝ) ^ 1000 ≤ (D : ℝ))
    (hlogK : Real.log (D : ℝ) ≤ (K : ℝ))
    (hKlog : (K : ℝ) ≤ (Real.log (D : ℝ)) ^ 2)
    (hCKη : (C : ℝ) + (K : ℝ) + η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9))
    (hcu : (C : ℝ) + (ℓ : ℝ) + 2 ≤ 3 * (D : ℝ) ^ ((1 : ℝ) / 4))
    (hℓ : (D : ℝ) ^ ((1 : ℝ) / 4) ≤ (ℓ : ℝ)) :
    (50 * ((C : ℝ) + (ℓ : ℝ) + 2) * Real.sqrt (4 * (D : ℝ)) < η * (D : ℝ) / 4) ∧
    ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16 ≤
      (η * (D : ℝ) / 4) ^ 2 / (16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)))) := by
  have hDpos : (0 : ℝ) < (D : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (10 : ℝ) ^ 1000) hDmin
  -- lower bound for `η` and hence for `t = ηD/4`
  have heta : (D : ℝ) ^ (-((1 : ℝ) / 9)) ≤ η := by
    have h1 : η⁻¹ ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
      have hCK : (0 : ℝ) ≤ (C : ℝ) + (K : ℝ) := by positivity
      linarith
    have hXpos : (0 : ℝ) < (D : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_pos_of_pos hDpos _
    have h2 : ((D : ℝ) ^ ((1 : ℝ) / 9))⁻¹ ≤ η := (inv_le_comm₀ hXpos hη).mpr h1
    calc (D : ℝ) ^ (-((1 : ℝ) / 9)) = ((D : ℝ) ^ ((1 : ℝ) / 9))⁻¹ := by
          rw [Real.rpow_neg hDpos.le]
      _ ≤ η := h2
  have ht_ge : (D : ℝ) ^ ((8 : ℝ) / 9) / 4 ≤ η * (D : ℝ) / 4 := by
    have h1 : (D : ℝ) ^ (-((1 : ℝ) / 9)) * (D : ℝ) ≤ η * (D : ℝ) :=
      mul_le_mul_of_nonneg_right heta hDpos.le
    have h2 : (D : ℝ) ^ (-((1 : ℝ) / 9)) * (D : ℝ) = (D : ℝ) ^ ((8 : ℝ) / 9) := by
      have h3 := Real.rpow_add hDpos (-((1 : ℝ) / 9)) (1 : ℝ)
      rw [Real.rpow_one] at h3
      rw [← h3]
      norm_num
    rw [h2] at h1
    linarith
  -- the two lower bounds `D^{5/36} ≥ 1200` and `D^{1/36} ≥ 18432`
  have h536 : (1200 : ℝ) < (D : ℝ) ^ ((5 : ℝ) / 36) := by
    refine rpow_lt_of_ten (by norm_num) hDmin ?_
    have h1 : (1200 : ℝ) < (10 : ℝ) ^ (4 : ℝ) := by norm_num
    exact lt_of_lt_of_le h1 (ten_rpow_mono (a := (4 : ℝ)) (b := 1000 * ((5 : ℝ) / 36)) (by norm_num))
  have h136 : (18432 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 36) := by
    refine rpow_ge_of_ten (by norm_num) hDmin ?_
    have h1 : (18432 : ℝ) ≤ (10 : ℝ) ^ (5 : ℝ) := by norm_num
    refine le_trans h1 (ten_rpow_mono ?_)
    norm_num
  have hsqrt : Real.sqrt (4 * (D : ℝ)) = 2 * Real.sqrt (D : ℝ) := by
    have h1 : (2 * Real.sqrt (D : ℝ)) ^ 2 = 4 * (D : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hDpos.le]; norm_num
    rw [← h1, Real.sqrt_sq (by positivity)]
  constructor
  · -- the Bruhn--Joos time threshold
    have h1 : 50 * ((C : ℝ) + (ℓ : ℝ) + 2) * Real.sqrt (4 * (D : ℝ))
        ≤ 50 * (3 * (D : ℝ) ^ ((1 : ℝ) / 4)) * (2 * Real.sqrt (D : ℝ)) := by
      rw [hsqrt]
      have h2 : (0 : ℝ) ≤ 2 * Real.sqrt (D : ℝ) := by positivity
      have h3 : 50 * ((C : ℝ) + (ℓ : ℝ) + 2) ≤ 50 * (3 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
        linarith
      exact mul_le_mul_of_nonneg_right h3 h2
    refine lt_of_le_of_lt h1 ?_
    -- `300 D^{1/4} √D < D^{8/9}/4`
    have h4 : (D : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (D : ℝ) ≤ (D : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hDpos]
      norm_num
    have h5 : 300 * ((D : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (D : ℝ))
        ≤ 300 * (D : ℝ) ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    have heq : 50 * (3 * (D : ℝ) ^ ((1 : ℝ) / 4)) * (2 * Real.sqrt (D : ℝ))
        = 300 * ((D : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (D : ℝ)) := by ring
    rw [heq]
    have h8 : 300 * (D : ℝ) ^ ((3 : ℝ) / 4) < (D : ℝ) ^ ((8 : ℝ) / 9) / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h6 : 300 * (D : ℝ) ^ ((3 : ℝ) / 4) * 4 = 1200 * (D : ℝ) ^ ((3 : ℝ) / 4) := by ring
      rw [h6]
      have h7 : (D : ℝ) ^ ((8 : ℝ) / 9) = (D : ℝ) ^ ((3 : ℝ) / 4) * (D : ℝ) ^ ((5 : ℝ) / 36) := by
        rw [← Real.rpow_add hDpos]; norm_num
      rw [h7]
      nlinarith [h536, Real.rpow_pos_of_pos hDpos ((3 : ℝ) / 4)]
    exact lt_of_le_of_lt h5 (lt_of_lt_of_le h8 ht_ge)
  · -- the exponent of the Bruhn--Joos bound
    have hlog16 : Real.log 16 ≤ 4 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      push_cast
      linarith
    have hD14 : (4 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := by
      refine rpow_ge_of_ten (c := (1 : ℝ) / 4) (by norm_num) hDmin ?_
      have h2 : 1000 * ((1 : ℝ) / 4) = (250 : ℝ) := by norm_num
      rw [h2]
      refine le_trans (by norm_num : (4 : ℝ) ≤ 10) ?_
      have h5 : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (250 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr (by norm_num)
      rwa [Real.rpow_one] at h5
    -- `t² ≥ D^{16/9}/16`
    have ht2 : (D : ℝ) ^ ((16 : ℝ) / 9) / 16 ≤ (η * (D : ℝ) / 4) ^ 2 := by
      have h1 : ((D : ℝ) ^ ((8 : ℝ) / 9) / 4) ^ 2 = (D : ℝ) ^ ((16 : ℝ) / 9) / 16 := by
        have h3 : ((D : ℝ) ^ ((8 : ℝ) / 9)) ^ (2 : ℕ) = (D : ℝ) ^ ((16 : ℝ) / 9) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; norm_num
        rw [div_pow, h3]; norm_num
      rw [← h1]
      refine pow_le_pow_left₀ (by positivity) ht_ge 2
    -- `c² ≤ 9 D^{1/2}` and `D^{1/4} + log 16 ≤ 2 D^{1/4}`
    have hc2 : ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 ≤ 9 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
      have h1 : ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 ≤ (3 * (D : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcu 2
      have h2 : (3 * (D : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = 9 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
        have h3 : ((D : ℝ) ^ ((1 : ℝ) / 4)) ^ (2 : ℕ) = (D : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; norm_num
        rw [mul_pow, h3]; norm_num
      linarith
    have hnum : (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16 ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 4) := by
      linarith
    -- the crucial estimate `64 c² D (D^{1/4} + log 16) ≤ D^{16/9}/16`
    have hkey : 64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ)
        * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) ≤ (D : ℝ) ^ ((16 : ℝ) / 9) / 16 := by
      have hA : 64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ)
          ≤ 576 * ((D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ)) := by
        nlinarith [hc2, hDpos.le]
      have hCeq : 576 * ((D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4))
          = 1152 * (D : ℝ) ^ ((7 : ℝ) / 4) := by
        have h1 : (D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ) = (D : ℝ) ^ ((3 : ℝ) / 2) := by
          have h := Real.rpow_add hDpos ((1 : ℝ) / 2) (1 : ℝ)
          rw [Real.rpow_one] at h
          rw [← h]
          norm_num
        have h2 : (D : ℝ) ^ ((3 : ℝ) / 2) * (D : ℝ) ^ ((1 : ℝ) / 4)
            = (D : ℝ) ^ ((7 : ℝ) / 4) := by
          rw [← Real.rpow_add hDpos]; norm_num
        calc 576 * ((D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4))
            = 1152 * ((D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ) * (D : ℝ) ^ ((1 : ℝ) / 4)) := by ring
          _ = 1152 * ((D : ℝ) ^ ((3 : ℝ) / 2) * (D : ℝ) ^ ((1 : ℝ) / 4)) := by rw [h1]
          _ = 1152 * (D : ℝ) ^ ((7 : ℝ) / 4) := by rw [h2]
      have hstep : 64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ)
          * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) ≤ 1152 * (D : ℝ) ^ ((7 : ℝ) / 4) := by
        calc 64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ)
            * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)
            ≤ 576 * ((D : ℝ) ^ ((1 : ℝ) / 2) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
              refine mul_le_mul hA hnum (by positivity) (by positivity)
          _ = 1152 * (D : ℝ) ^ ((7 : ℝ) / 4) := hCeq
      refine le_trans hstep ?_
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
      have h7 : (D : ℝ) ^ ((16 : ℝ) / 9) = (D : ℝ) ^ ((7 : ℝ) / 4) * (D : ℝ) ^ ((1 : ℝ) / 36) := by
        rw [← Real.rpow_add hDpos]; norm_num
      rw [h7]
      nlinarith [h136, Real.rpow_pos_of_pos hDpos ((7 : ℝ) / 4)]
    -- conclude
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ)))]
    have hden : 16 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (4 * (D : ℝ))
        = 64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ) := by ring
    rw [hden]
    rw [mul_comm (64 * ((C : ℝ) + (ℓ : ℝ) + 2) ^ 2 * (D : ℝ))
      ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)] at hkey
    exact le_trans hkey ht2


/-- **The exceptional probability is small.** -/
theorem num_exc {C D Λ ℓ : ℕ} (hC : 2 ≤ C) (hΛ1 : 1 ≤ Λ)
    (hΛD : (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ)) (hDmin : (10 : ℝ) ^ 1000 ≤ (D : ℝ))
    (hCD : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9)) (hℓ : (D : ℝ) ^ ((1 : ℝ) / 4) ≤ (ℓ : ℝ)) :
    ((D : ℝ) * (Λ : ℝ) * ((1 / 32 : ℝ) ^ ℓ) ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16) ∧
    (Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16 ≤ 1 / (D : ℝ) ^ 2) := by
  have hDpos : (0 : ℝ) < (D : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < (10 : ℝ) ^ 1000) hDmin
  have hlogD8 : Real.log (D : ℝ) ≤ 8 * (D : ℝ) ^ ((1 : ℝ) / 8) := log_le_eight_rpow hDpos
  have hD18 : (18 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 8) := by
    refine rpow_ge_of_ten (c := (1 : ℝ) / 8) (by norm_num) hDmin ?_
    have h2 : 1000 * ((1 : ℝ) / 8) = (125 : ℝ) := by norm_num
    rw [h2]
    refine le_trans (by norm_num : (18 : ℝ) ≤ 100) ?_
    have h5 : (10 : ℝ) ^ (2 : ℕ) ≤ (10 : ℝ) ^ (125 : ℝ) := by
      have h6 : (10 : ℝ) ^ (2 : ℕ) = (10 : ℝ) ^ (2 : ℝ) := (Real.rpow_natCast (10 : ℝ) 2).symm
      rw [h6]
      exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr (by norm_num)
    have h7 : (10 : ℝ) ^ (2 : ℕ) = 100 := by norm_num
    rwa [h7] at h5
  have hlog16 : Real.log 16 ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    push_cast
    linarith
  have hlog10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    linarith
  -- the exponent comparison
  have hexp_le : Real.log 10 + Real.log (D : ℝ) * ((19 : ℝ) / 9) + Real.log 16
      ≤ (Real.log 32 - 1) * (D : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : Real.log (D : ℝ) * ((19 : ℝ) / 9) ≤ 17 * (D : ℝ) ^ ((1 : ℝ) / 8) := by
      nlinarith [hlogD8, Real.rpow_pos_of_pos hDpos ((1 : ℝ) / 8)]
    have h2 : 13 + 17 * (D : ℝ) ^ ((1 : ℝ) / 8)
        ≤ (Real.log 32 - 1) * (D : ℝ) ^ ((1 : ℝ) / 4) := by
      have h3 : (2 : ℝ) ≤ Real.log 32 - 1 := by linarith [log_thirtytwo_ge_three]
      have h4 : (2 : ℝ) * (D : ℝ) ^ ((1 : ℝ) / 4)
          ≤ (Real.log 32 - 1) * (D : ℝ) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      have h5 : (D : ℝ) ^ ((1 : ℝ) / 4)
          = (D : ℝ) ^ ((1 : ℝ) / 8) * (D : ℝ) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_add hDpos]; norm_num
      rw [h5] at h4
      nlinarith [h4, hD18, Real.rpow_pos_of_pos hDpos ((1 : ℝ) / 8)]
    nlinarith [h1, h2, hlog10, hlog16]
  constructor
  · -- first conjunct
    have hDL : (D : ℝ) * (Λ : ℝ) ≤ 10 * (D : ℝ) ^ ((19 : ℝ) / 9) := by
      have h1 : (D : ℝ) * (Λ : ℝ) ≤ (D : ℝ) * (10 * (C : ℝ) * (D : ℝ)) :=
        mul_le_mul_of_nonneg_left hΛD hDpos.le
      have h2 : (D : ℝ) * (10 * (C : ℝ) * (D : ℝ))
          ≤ (D : ℝ) * (10 * ((D : ℝ) ^ ((1 : ℝ) / 9)) * (D : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hDpos.le
        nlinarith [hCD, hDpos.le]
      have h3 : (D : ℝ) * (10 * ((D : ℝ) ^ ((1 : ℝ) / 9)) * (D : ℝ))
          = 10 * (D : ℝ) ^ ((19 : ℝ) / 9) := by
        have hA : (D : ℝ) * (((D : ℝ) ^ ((1 : ℝ) / 9)) * (D : ℝ))
            = (D : ℝ) ^ (1 + ((1 : ℝ) / 9 + 1)) := by
          have hA1 : (D : ℝ) ^ ((1 : ℝ) / 9) * (D : ℝ) = (D : ℝ) ^ ((1 : ℝ) / 9 + 1) := by
            have h := Real.rpow_add hDpos ((1 : ℝ) / 9) (1 : ℝ)
            rw [Real.rpow_one] at h
            exact h.symm
          have hA2 : (D : ℝ) ^ (1 : ℝ) * (D : ℝ) ^ ((1 : ℝ) / 9 + 1)
              = (D : ℝ) ^ (1 + ((1 : ℝ) / 9 + 1)) := by
            rw [← Real.rpow_add hDpos]
          rw [hA1, ← hA2, Real.rpow_one]
        rw [show (D : ℝ) * (10 * ((D : ℝ) ^ ((1 : ℝ) / 9)) * (D : ℝ))
            = 10 * ((D : ℝ) * (((D : ℝ) ^ ((1 : ℝ) / 9)) * (D : ℝ))) from by ring, hA]
        congr 1
        norm_num
      linarith [h1, h2, h3]
    have hpow : (1 / 32 : ℝ) ^ ℓ ≤ Real.exp (-(Real.log 32 * (D : ℝ) ^ ((1 : ℝ) / 4))) := by
      have h1 : (1 / 32 : ℝ) ^ ℓ = Real.exp (ℓ * Real.log (1 / 32)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 32)]
      rw [h1]
      refine Real.exp_le_exp.mpr ?_
      have h2 : Real.log (1 / 32) = -Real.log 32 := by
        rw [one_div, Real.log_inv]
      rw [h2]
      have h3 : Real.log 32 * (D : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.log 32 * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hℓ (by linarith [log_thirtytwo_ge_three])
      nlinarith [h3]
    have h1 : (D : ℝ) * (Λ : ℝ) * (1 / 32 : ℝ) ^ ℓ
        ≤ (10 * (D : ℝ) ^ ((19 : ℝ) / 9))
          * Real.exp (-(Real.log 32 * (D : ℝ) ^ ((1 : ℝ) / 4))) :=
      mul_le_mul hDL hpow (by positivity) (by positivity)
    refine le_trans h1 ?_
    have h2 : (10 : ℝ) * (D : ℝ) ^ ((19 : ℝ) / 9)
        = Real.exp (Real.log 10 + Real.log (D : ℝ) * ((19 : ℝ) / 9)) := by
      have h20 : (10 : ℝ) = Real.exp (Real.log 10) :=
        (Real.exp_log (by norm_num : (0 : ℝ) < 10)).symm
      have h21 : (D : ℝ) ^ ((19 : ℝ) / 9)
          = Real.exp (Real.log (D : ℝ) * ((19 : ℝ) / 9)) := Real.rpow_def_of_pos hDpos _
      conv_lhs => rw [h20, h21]
      rw [← Real.exp_add]
    rw [h2]
    have h3 : Real.exp (Real.log 10 + Real.log (D : ℝ) * ((19 : ℝ) / 9))
          * Real.exp (-(Real.log 32 * (D : ℝ) ^ ((1 : ℝ) / 4)))
        = Real.exp (Real.log 10 + Real.log (D : ℝ) * ((19 : ℝ) / 9)
            - Real.log 32 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
      rw [← Real.exp_add]
      first | rfl | (congr 1; ring)
    rw [h3]
    have h4 : Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16
        = Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4)) - Real.log 16) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    rw [h4]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hexp_le]
  · -- second conjunct
    have h2log : 2 * Real.log (D : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16 := by
      have h3 : 2 * Real.log (D : ℝ) ≤ 16 * (D : ℝ) ^ ((1 : ℝ) / 8) := by nlinarith [hlogD8]
      have h4 : 16 * (D : ℝ) ^ ((1 : ℝ) / 8) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := by
        have h5 : (D : ℝ) ^ ((1 : ℝ) / 4)
            = (D : ℝ) ^ ((1 : ℝ) / 8) * (D : ℝ) ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_add hDpos]; norm_num
        rw [h5]
        nlinarith [hD18, Real.rpow_pos_of_pos hDpos ((1 : ℝ) / 8)]
      have h16 : (0 : ℝ) ≤ Real.log 16 := Real.log_nonneg (by norm_num)
      linarith
    have h5 : 1 / (D : ℝ) ^ 2 = Real.exp (-(2 * Real.log (D : ℝ))) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 1 / (D : ℝ) ^ 2)]
      congr 1
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
      push_cast
      ring
    have h6 : Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4))) / 16
        = Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4)) - Real.log 16) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    rw [h6, h5]
    exact Real.exp_le_exp.mpr (by linarith)

end

end Work.Deep.Kahn
