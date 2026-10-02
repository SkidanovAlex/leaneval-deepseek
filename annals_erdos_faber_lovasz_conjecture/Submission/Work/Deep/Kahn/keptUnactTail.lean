import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundKeptUnactDefs

/-!
# `Work.Deep.Kahn.keptUnactTail`

The two numeric side conditions of the Bruhn--Joos argument for the statistic
`keptUnactCount ω x γ`, in the regime `D ≥ 10^100`, `C + K + η⁻¹ ≤ D^{1/9}`.

With `c := C + 2` (the "change" of a coordinate), `s := 2D` (the certificate size) and
`t := ηD/8` (the deviation level), the Bruhn--Joos theorem requires

* `50 c √s < t`, and
* the exponent condition `D^{1/4} + log 16 ≤ t²/(16 c² s)`, which is exactly the statement
  that the tail `4 exp(-t²/(16 c² s))` is at most `exp(-D^{1/4})/2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Deep.Kahn

noncomputable section

/-- `10^a ≤ 10^b` for `a ≤ b` (real exponents). -/
lemma ten_rpow_mono' {a b : ℝ} (h : a ≤ b) : (10 : ℝ) ^ a ≤ (10 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).mpr h

/-- `((10:ℝ)^100)^c = 10^{100 c}`. -/
lemma ten_pow_rpow' (c : ℝ) : ((10 : ℝ) ^ 100) ^ c = (10 : ℝ) ^ (100 * c) := by
  rw [← Real.rpow_natCast (10 : ℝ) 100, ← Real.rpow_mul (x := (10 : ℝ)) (by norm_num)]
  norm_num

/-- In the regime `D ≥ 10^100`, `t ≤ D^c` whenever `t ≤ 10^{100 c}`. -/
lemma rpow_ge_of_ten' {D : ℕ} {c t : ℝ} (hc : 0 ≤ c) (hD : (10 : ℝ) ^ 100 ≤ (D : ℝ))
    (ht : t ≤ (10 : ℝ) ^ (100 * c)) : t ≤ (D : ℝ) ^ c := by
  refine le_trans ht ?_
  rw [← ten_pow_rpow' c]
  exact Real.rpow_le_rpow (by positivity) hD hc

/-- In the regime `D ≥ 10^100`, `t < D^c` whenever `t < 10^{100 c}`. -/
lemma rpow_lt_of_ten' {D : ℕ} {c t : ℝ} (hc : 0 ≤ c) (hD : (10 : ℝ) ^ 100 ≤ (D : ℝ))
    (ht : t < (10 : ℝ) ^ (100 * c)) : t < (D : ℝ) ^ c := by
  refine lt_of_lt_of_le ht ?_
  rw [← ten_pow_rpow' c]
  exact Real.rpow_le_rpow (by positivity) hD hc

/-- `Real.log 16 ≤ 4`. -/
lemma log16_le_four : Real.log 16 ≤ 4 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  push_cast
  linarith

/-- **The two numeric side conditions of the Bruhn--Joos bound for `keptUnactCount`.** -/
theorem keptUnactTail {C D K : ℕ} {η : ℝ} (hη : 0 < η) (hD1 : 1 ≤ D) (hK2 : 2 ≤ K)
    (hD : (10 : ℝ) ^ 100 ≤ (D : ℝ))
    (hCK : ((C : ℝ) + (K : ℝ) + η⁻¹) ≤ (D : ℝ) ^ ((1 : ℝ) / 9)) :
    50 * ((C : ℝ) + 2) * Real.sqrt (2 * (D : ℝ)) < η * (D : ℝ) / 8 ∧
    4 * Real.exp (-((η * (D : ℝ) / 8) ^ 2 /
        (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)))))
      ≤ Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 2 := by
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le (by positivity) hD
  have hD1' : (1 : ℝ) ≤ (D : ℝ) :=
    le_trans (by norm_num : (1 : ℝ) ≤ (10 : ℝ) ^ 100) hD
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
  -- `C ≤ D^{1/9}` and `C + 2 ≤ 3 D^{1/9}`
  have hCle : (C : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := by
    have h2 : (0 : ℝ) ≤ (K : ℝ) + η⁻¹ := by positivity
    linarith
  have hD19 : (1 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 9) := Real.one_le_rpow hD1' (by norm_num)
  have hC2 : (C : ℝ) + 2 ≤ 3 * (D : ℝ) ^ ((1 : ℝ) / 9) := by nlinarith [hCle, hD19]
  -- `η D / 8 ≥ D^{8/9}/8`
  have ht_ge : (D : ℝ) ^ ((8 : ℝ) / 9) / 8 ≤ η * (D : ℝ) / 8 := by
    have h1 : (D : ℝ) ^ (-((1 : ℝ) / 9)) * (D : ℝ) ≤ η * (D : ℝ) :=
      mul_le_mul_of_nonneg_right heta hDpos.le
    have h2 : (D : ℝ) ^ (-((1 : ℝ) / 9)) * (D : ℝ) = (D : ℝ) ^ ((8 : ℝ) / 9) := by
      have h3 := Real.rpow_add hDpos (-((1 : ℝ) / 9)) (1 : ℝ)
      rw [Real.rpow_one] at h3
      rw [← h3]
      norm_num
    rw [h2] at h1
    linarith
  -- `D^{5/18} ≥ 2000` and `D^{11/36} ≥ 40000`
  have h518 : (2000 : ℝ) ≤ (D : ℝ) ^ ((5 : ℝ) / 18) := by
    refine rpow_ge_of_ten' (by norm_num) hD ?_
    have h1 : (2000 : ℝ) ≤ (10 : ℝ) ^ (4 : ℝ) := by norm_num
    refine le_trans h1 (ten_rpow_mono' ?_)
    norm_num
  have h1136 : (40000 : ℝ) ≤ (D : ℝ) ^ ((11 : ℝ) / 36) := by
    refine rpow_ge_of_ten' (by norm_num) hD ?_
    have h1 : (40000 : ℝ) ≤ (10 : ℝ) ^ (5 : ℝ) := by norm_num
    refine le_trans h1 (ten_rpow_mono' ?_)
    norm_num
  have h14 : (4 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := by
    refine rpow_ge_of_ten' (by norm_num) hD ?_
    have h1 : (4 : ℝ) ≤ (10 : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]; norm_num
    refine le_trans h1 (ten_rpow_mono' ?_)
    norm_num
  have hsqrt : Real.sqrt (2 * (D : ℝ)) = Real.sqrt 2 * Real.sqrt (D : ℝ) :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
  constructor
  · -- the Bruhn--Joos time threshold
    have h1 : 50 * ((C : ℝ) + 2) * Real.sqrt (2 * (D : ℝ))
        ≤ 50 * (3 * (D : ℝ) ^ ((1 : ℝ) / 9)) * (Real.sqrt 2 * Real.sqrt (D : ℝ)) := by
      rw [hsqrt]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hC2 (by norm_num)
    refine lt_of_le_of_lt h1 ?_
    have h2 : (D : ℝ) ^ ((1 : ℝ) / 9) * Real.sqrt (D : ℝ) = (D : ℝ) ^ ((11 : ℝ) / 18) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hDpos]
      norm_num
    have h3 : 50 * (3 * (D : ℝ) ^ ((1 : ℝ) / 9)) * (Real.sqrt 2 * Real.sqrt (D : ℝ))
        = 150 * Real.sqrt 2 * ((D : ℝ) ^ ((1 : ℝ) / 9) * Real.sqrt (D : ℝ)) := by ring
    rw [h3, h2]
    have hs2 : Real.sqrt 2 < (3 : ℝ) / 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (3 : ℝ) / 2)]
      norm_num
    have h4 : 150 * Real.sqrt 2 * (D : ℝ) ^ ((11 : ℝ) / 18)
        < 225 * (D : ℝ) ^ ((11 : ℝ) / 18) := by
      have h5 : (0 : ℝ) < (D : ℝ) ^ ((11 : ℝ) / 18) := Real.rpow_pos_of_pos hDpos _
      nlinarith [hs2, h5]
    refine lt_of_lt_of_le h4 ?_
    refine le_trans ?_ ht_ge
    have h6 : (D : ℝ) ^ ((8 : ℝ) / 9)
        = (D : ℝ) ^ ((11 : ℝ) / 18) * (D : ℝ) ^ ((5 : ℝ) / 18) := by
      rw [← Real.rpow_add hDpos]; norm_num
    rw [h6, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    have h7 : (0 : ℝ) < (D : ℝ) ^ ((11 : ℝ) / 18) := Real.rpow_pos_of_pos hDpos _
    have h8 : (1800 : ℝ) ≤ (D : ℝ) ^ ((5 : ℝ) / 18) := le_trans (by norm_num) h518
    calc 225 * (D : ℝ) ^ ((11 : ℝ) / 18) * 8
        = 1800 * (D : ℝ) ^ ((11 : ℝ) / 18) := by ring
      _ ≤ (D : ℝ) ^ ((5 : ℝ) / 18) * (D : ℝ) ^ ((11 : ℝ) / 18) :=
          mul_le_mul_of_nonneg_right h8 h7.le
      _ = (D : ℝ) ^ ((11 : ℝ) / 18) * (D : ℝ) ^ ((5 : ℝ) / 18) := by ring
  · -- the exponent of the Bruhn--Joos bound
    have ht2 : (D : ℝ) ^ ((16 : ℝ) / 9) / 64 ≤ (η * (D : ℝ) / 8) ^ 2 := by
      have h1 : ((D : ℝ) ^ ((8 : ℝ) / 9) / 8) ^ 2 = (D : ℝ) ^ ((16 : ℝ) / 9) / 64 := by
        have h3 : ((D : ℝ) ^ ((8 : ℝ) / 9)) ^ (2 : ℕ) = (D : ℝ) ^ ((16 : ℝ) / 9) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; norm_num
        rw [div_pow, h3]; norm_num
      rw [← h1]
      exact pow_le_pow_left₀ (by positivity) ht_ge 2
    have hc2 : ((C : ℝ) + 2) ^ 2 ≤ 9 * (D : ℝ) ^ ((2 : ℝ) / 9) := by
      have h1 : ((C : ℝ) + 2) ^ 2 ≤ (3 * (D : ℝ) ^ ((1 : ℝ) / 9)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hC2 2
      have h2 : (3 * (D : ℝ) ^ ((1 : ℝ) / 9)) ^ 2 = 9 * (D : ℝ) ^ ((2 : ℝ) / 9) := by
        have h3 : ((D : ℝ) ^ ((1 : ℝ) / 9)) ^ (2 : ℕ) = (D : ℝ) ^ ((2 : ℝ) / 9) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; norm_num
        rw [mul_pow, h3]; norm_num
      linarith
    -- `D^{1/4} + log 16 ≤ 2 D^{1/4}`
    have hnum : (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16 ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 4) := by
      have := log16_le_four
      have h2 : (0 : ℝ) < (D : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hDpos _
      linarith
    -- the key estimate `32 c² D (D^{1/4} + log 16) ≤ D^{16/9}/64`
    have hkey : 32 * ((C : ℝ) + 2) ^ 2 * (D : ℝ)
        * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) ≤ (D : ℝ) ^ ((16 : ℝ) / 9) / 64 := by
      have hA : 32 * ((C : ℝ) + 2) ^ 2 * (D : ℝ)
          ≤ 288 * ((D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ)) := by
        nlinarith [hc2, hDpos.le]
      have hCeq : 288 * ((D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4))
          = 576 * (D : ℝ) ^ ((53 : ℝ) / 36) := by
        have h1 : (D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ) = (D : ℝ) ^ ((11 : ℝ) / 9) := by
          have h := Real.rpow_add hDpos ((2 : ℝ) / 9) (1 : ℝ)
          rw [Real.rpow_one] at h
          rw [← h]
          norm_num
        have h2 : (D : ℝ) ^ ((11 : ℝ) / 9) * (D : ℝ) ^ ((1 : ℝ) / 4)
            = (D : ℝ) ^ ((53 : ℝ) / 36) := by
          rw [← Real.rpow_add hDpos]; norm_num
        calc 288 * ((D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4))
            = 576 * ((D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ) * (D : ℝ) ^ ((1 : ℝ) / 4)) := by ring
          _ = 576 * ((D : ℝ) ^ ((11 : ℝ) / 9) * (D : ℝ) ^ ((1 : ℝ) / 4)) := by rw [h1]
          _ = 576 * (D : ℝ) ^ ((53 : ℝ) / 36) := by rw [h2]
      have hstep : 32 * ((C : ℝ) + 2) ^ 2 * (D : ℝ)
          * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) ≤ 576 * (D : ℝ) ^ ((53 : ℝ) / 36) := by
        calc 32 * ((C : ℝ) + 2) ^ 2 * (D : ℝ)
            * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)
            ≤ 288 * ((D : ℝ) ^ ((2 : ℝ) / 9) * (D : ℝ)) * (2 * (D : ℝ) ^ ((1 : ℝ) / 4)) := by
              refine mul_le_mul hA hnum (by positivity) (by positivity)
          _ = 576 * (D : ℝ) ^ ((53 : ℝ) / 36) := hCeq
      refine le_trans hstep ?_
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
      have h7 : (D : ℝ) ^ ((16 : ℝ) / 9)
          = (D : ℝ) ^ ((53 : ℝ) / 36) * (D : ℝ) ^ ((11 : ℝ) / 36) := by
        rw [← Real.rpow_add hDpos]; norm_num
      rw [h7]
      nlinarith [h1136, Real.rpow_pos_of_pos hDpos ((53 : ℝ) / 36)]
    -- conclude
    have hden : (0 : ℝ) < 16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)) := by positivity
    have hgoal : (D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16
        ≤ (η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ))) := by
      rw [le_div_iff₀ hden]
      rw [mul_comm ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)
        (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)))]
      have hswap : 16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ))
            * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)
          = 32 * ((C : ℝ) + 2) ^ 2 * (D : ℝ)
            * ((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16) := by ring
      rw [hswap]
      exact le_trans hkey ht2
    have hexp : Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16))
        = Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) / 16 := by
      have harg : -((D : ℝ) ^ ((1 : ℝ) / 4) + Real.log 16)
          = -(D : ℝ) ^ ((1 : ℝ) / 4) - Real.log 16 := by ring
      rw [harg, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    have h1 : Real.exp (-((η * (D : ℝ) / 8) ^ 2 / (16 * ((C : ℝ) + 2) ^ 2 * (2 * (D : ℝ)))))
        ≤ Real.exp (-((D : ℝ) ^ ((1 : ℝ) / 4)) ) / 16 := by
      refine le_trans (Real.exp_le_exp.mpr (neg_le_neg hgoal)) (le_of_eq hexp)
    have h3 : (0 : ℝ) < Real.exp (-(D : ℝ) ^ ((1 : ℝ) / 4)) := Real.exp_pos _
    nlinarith [h1, h3]

end

end Work.Deep.Kahn
