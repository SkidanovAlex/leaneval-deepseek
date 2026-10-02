import Mathlib
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.RepulsionSizes
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesReal
import Submission.Work.LinnikAreas.BGTZ.E.LogConstLeRpow
import Submission.Work.LinnikAreas.BGTZ.E.RpowNegNatLe

namespace Work.LinnikAreas.BGTZ.E

set_option maxHeartbeats 4000000

/-- Elementary auxiliary: `(log q)^n ≤ q^{1/100}` for every `n ≤ 28`, as soon as `log q ≥ 10^12`
(a consequence of `(log q)^28·2^48 ≤ q^{1/100}`, proved in `Work.LinnikAreas.BGTZ.RepulsionSizes`). -/
lemma logPowLeRpow {q : ℝ} (hq : 0 < q) (hL : (10 : ℝ) ^ 12 ≤ Real.log q) {n : ℕ}
    (hn : n ≤ 28) : (Real.log q) ^ n ≤ q ^ (1 / 100 : ℝ) := by
  have hXn : Real.exp 100000000 ≤ q := by
    have h1 : Real.exp 100000000 ≤ Real.exp ((10 : ℝ) ^ 12) := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp ((10 : ℝ) ^ 12) ≤ q := (Real.le_log_iff_exp_le hq).mp hL
    linarith
  have hmul := Work.LinnikAreas.BGTZ.repulsionSizesLogPow28Le hXn
  have hL1 : (1 : ℝ) ≤ Real.log q := by linarith
  have hLnn : (0 : ℝ) ≤ Real.log q := by linarith
  have h1 : (Real.log q) ^ n ≤ (Real.log q) ^ 28 := pow_le_pow_right₀ hL1 hn
  have h2 : (Real.log q) ^ 28 ≤ (Real.log q) ^ 28 * (2 : ℝ) ^ 48 := by
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ 48 := one_le_pow₀ (by norm_num)
    calc (Real.log q) ^ 28 = (Real.log q) ^ 28 * 1 := by ring
      _ ≤ (Real.log q) ^ 28 * (2 : ℝ) ^ 48 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hLnn 28)
  linarith

/-- **The sifting level of the `E`-interface.**  Under the standing hypotheses (Landau--Siegel
input `hlam`, `log A, log CR ≤ log q/10000`, `log q ≥ 10^12`) there is an integer `R` with
`CR·sieveX A q β₁ ≤ R ≤ 2·CR·sieveX A q β₁`, `R ≥ 200`, and `(1 + log R)^18 ≤ q^{1/100}` (the
last being what the detection-length estimate needs). -/
lemma exists_sifting_level {q : ℕ} [NeZero q] {A CR β₁ : ℝ}
    (hA1 : 1 ≤ A) (hCR : 1 ≤ CR) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log (q : ℝ)) < β₁)
    (hlam : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < (1 - β₁) * Real.log (q : ℝ))
    (hlogq : (10 : ℝ) ^ 12 ≤ Real.log (q : ℝ))
    (hlogA : Real.log A ≤ Real.log (q : ℝ) / 10000)
    (hlogCR : Real.log CR ≤ Real.log (q : ℝ) / 10000) :
    ∃ R : ℕ, 200 ≤ R ∧
      CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ ≤ (R : ℝ) ∧
      (R : ℝ) ≤ 2 * CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ ∧
      (1 + Real.log (R : ℝ)) ^ 18 ≤ (q : ℝ) ^ (1 / 100 : ℝ) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hx1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hLpos : 0 < Real.log (q : ℝ) := by linarith [hlogq]
  have hXe : Real.exp ((10 : ℝ) ^ 12) ≤ (q : ℝ) := (Real.le_log_iff_exp_le hxpos).mp hlogq
  have hXe8 : Real.exp 100000000 ≤ (q : ℝ) := by
    have h : Real.exp 100000000 ≤ Real.exp ((10 : ℝ) ^ 12) := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA2ge1 : (1 : ℝ) ≤ A ^ 2 := one_le_pow₀ hA1
  have hβ1pos : 0 < β₁ := by
    have h2 : (0 : ℝ) < 10 * Real.log (q : ℝ) := by linarith
    have h3 : 1 / (10 * Real.log (q : ℝ)) ≤ 1 := by
      rw [div_le_one h2]; linarith
    linarith
  have hδpos : 0 < 1 - β₁ := by linarith
  have hδ1 : (1 : ℝ) ≤ (1 - β₁) ^ (-2 : ℝ) := by
    have hle1 : 1 - β₁ ≤ 1 := by linarith
    have hinv : (1 : ℝ) ≤ (1 - β₁)⁻¹ := (one_le_inv₀ hδpos).mpr hle1
    have hsplit : (1 - β₁) ^ (-2 : ℝ) = (1 - β₁) ^ (-1 : ℝ) * (1 - β₁) ^ (-1 : ℝ) := by
      rw [show (-2 : ℝ) = (-1) + (-1) by norm_num, Real.rpow_add hδpos]
    rw [hsplit, Real.rpow_neg_one]
    exact le_trans hinv (le_mul_of_one_le_right (by linarith only [hinv]) hinv)
  have hδQ : (1 - β₁)⁻¹ ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    have hlam' : (1 : ℝ) / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2) < 1 - β₁ := by
      have h1 : (1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))) / Real.log (q : ℝ) < 1 - β₁ := by
        have h2 := div_lt_div_of_pos_right hlam hLpos
        rwa [mul_div_cancel_right₀ _ (ne_of_gt hLpos)] at h2
      have h3 : (1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))) / Real.log (q : ℝ)
          = 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2) := by
        rw [div_div]; ring_nf
      linarith only [h1, h3]
    exact (Work.LinnikAreas.BGTZ.repulsionSizesSiegelInv (le_refl 1) (by
      have h1 : (1 : ℝ) < Real.exp ((10 : ℝ) ^ 12) := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
      linarith) hlam').2
  have hA_le : A ≤ (q : ℝ) ^ (1 / 10000 : ℝ) :=
    LogConstLeRpow hxpos hA0 (by norm_num) hlogA
  have hCR_le : CR ≤ (q : ℝ) ^ (1 / 10000 : ℝ) :=
    LogConstLeRpow hxpos (lt_of_lt_of_le zero_lt_one hCR) (by norm_num) hlogCR
  have hA2_le : A ^ 2 ≤ (q : ℝ) ^ (1 / 500 : ℝ) := by
    have h1 : A ^ 2 ≤ ((q : ℝ) ^ (1 / 10000 : ℝ)) ^ 2 := pow_le_pow_left₀ hA0.le hA_le 2
    have h2 : ((q : ℝ) ^ (1 / 10000 : ℝ)) ^ 2 = (q : ℝ) ^ (1 / 5000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    have h3 : (q : ℝ) ^ (1 / 5000 : ℝ) ≤ (q : ℝ) ^ (1 / 500 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    linarith
  have hL4 : (Real.log (q : ℝ)) ^ 4 ≤ (q : ℝ) ^ (1 / 100 : ℝ) :=
    Work.LinnikAreas.BGTZ.repulsionSizesLogPow4LeRpow hXe8
  have hexp2 : Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) ≤ (q : ℝ) ^ (1 / 50 : ℝ) := by
    have h100 : (100 : ℝ) ≤ (Real.log (q : ℝ)) ^ (1 / 4 : ℝ) :=
      Work.LinnikAreas.BGTZ.repulsionSizesHundredLeRpowQuarter (by linarith [hlogq])
    have h34 : (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (q : ℝ) / 100 :=
      Work.LinnikAreas.BGTZ.repulsionSizesThreeQuartersLe hLpos h100
    have h1 : 2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (q : ℝ) * (1 / 50) := by
      have h2 : Real.log (q : ℝ) / 100 = Real.log (q : ℝ) * (1 / 100) := by ring
      linarith only [h34, h2]
    calc Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        ≤ Real.exp (Real.log (q : ℝ) * (1 / 50)) := Real.exp_le_exp.mpr h1
      _ = (q : ℝ) ^ (1 / 50 : ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hδ2 : (1 - β₁) ^ (-2 : ℝ) ≤ (q : ℝ) ^ (1 / 50 : ℝ) * (Real.log (q : ℝ)) ^ 4 := by
    have h1 := RpowNegNatLe hxpos hδpos 2 hδQ
    have h2 : (1 - β₁) ^ (-(2 : ℝ)) ≤ (q : ℝ) ^ ((2 : ℝ) / 100) * (Real.log (q : ℝ)) ^ (2 * 2) := by
      simpa only [Nat.cast_ofNat] using h1
    rw [show ((2 : ℝ) / 100) = (1 / 50 : ℝ) by norm_num] at h2
    simpa using h2
  have hRB : A ^ 2 * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
      ≤ (q : ℝ) ^ (53 / 1000 : ℝ) := by
    have h := Work.LinnikAreas.BGTZ.repulsionSizesRBound hxpos hδpos
      (Real.one_le_rpow hx1 (by norm_num)) hA2_le hexp2 hδ2 hL4
    simpa using h
  have hsieveX : Work.LinnikAreas.BGTZ.sieveX A q β₁
      = A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        * (1 - β₁) ^ (-2 : ℝ) := by
    simp only [Work.LinnikAreas.BGTZ.sieveX, Work.LinnikAreas.BGTZ.thA]
    norm_num
  have hLRub0 : CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ ≤ (q : ℝ) ^ (3 / 5 : ℝ) := by
    rw [hsieveX]
    have hinner : A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
        ≤ (q : ℝ) ^ (13 / 25 : ℝ) * (q : ℝ) ^ (53 / 1000 : ℝ) := by
      calc A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)
          = (q : ℝ) ^ (13 / 25 : ℝ) * (A ^ 2
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)) := by ring
        _ ≤ (q : ℝ) ^ (13 / 25 : ℝ) * (q : ℝ) ^ (53 / 1000 : ℝ) :=
            mul_le_mul_of_nonneg_left hRB (Real.rpow_nonneg hxpos.le _)
    calc CR * (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ))
        ≤ (q : ℝ) ^ (1 / 10000 : ℝ) * ((q : ℝ) ^ (13 / 25 : ℝ) * (q : ℝ) ^ (53 / 1000 : ℝ)) :=
          mul_le_mul hCR_le hinner (by positivity) (by positivity)
      _ = (q : ℝ) ^ (1 / 10000 + 13 / 25 + 53 / 1000 : ℝ) := by
          rw [Real.rpow_add hxpos, Real.rpow_add hxpos]; ring
      _ ≤ (q : ℝ) ^ (3 / 5 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hx1; norm_num
  have hqhalf : (200 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by
    have hq40000 : ((200 : ℝ) ^ 2) ≤ (q : ℝ) := by
      have h1 : (40000 : ℝ) ≤ Real.exp ((10 : ℝ) ^ 12) := by
        have h2 : (40000 : ℝ) ≤ Real.exp 40000 := by
          have := Real.add_one_le_exp (40000 : ℝ); linarith
        exact le_trans h2 (Real.exp_le_exp.mpr (by norm_num))
      have h3 : ((200 : ℝ) ^ 2) = (40000 : ℝ) := by norm_num
      linarith only [h1, h3, hXe]
    have h3 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (200 : ℝ) ^ 2) hq40000
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h4 : (((200 : ℝ) ^ 2)) ^ (1 / 2 : ℝ) = 200 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 200)]; norm_num
    linarith only [h3, h4]
  have hLRge0 : (200 : ℝ) ≤ CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ := by
    rw [hsieveX]
    have hqP : (200 : ℝ) ≤ (q : ℝ) ^ (13 / 25 : ℝ) :=
      le_trans hqhalf (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
    have hexp1 : (1 : ℝ) ≤ Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
      Real.one_le_exp (by positivity)
    have hqPnn : (0 : ℝ) ≤ (q : ℝ) ^ (13 / 25 : ℝ) := Real.rpow_nonneg hxpos.le _
    have h1 : (q : ℝ) ^ (13 / 25 : ℝ) ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) := by
      calc (q : ℝ) ^ (13 / 25 : ℝ) = 1 * (q : ℝ) ^ (13 / 25 : ℝ) := by ring
        _ ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) := mul_le_mul_of_nonneg_right hA2ge1 hqPnn
    have h2 : A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
        ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := by
      calc A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) = (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)) * 1 := by ring
        _ ≤ (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ))
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
    have h3 : A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) := by
      calc A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          = (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))) * 1 := by ring
        _ ≤ (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
              * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))) * (1 - β₁) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left hδ1 (by positivity)
    calc (200 : ℝ) ≤ (q : ℝ) ^ (13 / 25 : ℝ) := hqP
      _ ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ) := h1
      _ ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := h2
      _ ≤ A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) := h3
      _ = 1 * (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)) := by ring
      _ ≤ CR * (A ^ 2 * (q : ℝ) ^ (13 / 25 : ℝ)
            * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCR (by positivity)
  set LR : ℝ := CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ with hLRdef
  have hLRub : LR ≤ (q : ℝ) ^ (3 / 5 : ℝ) := by rw [hLRdef]; exact hLRub0
  have hLRge : (200 : ℝ) ≤ LR := by rw [hLRdef]; exact hLRge0
  have hLRpos : (0 : ℝ) < LR := by linarith only [hLRge]
  set R : ℕ := ⌈max 200 LR⌉₊ with hRdef
  have hmaxeq : max 200 LR = LR := max_eq_right hLRge
  have hR200 : 200 ≤ R := by
    rw [hRdef]
    have h1 : (200 : ℝ) ≤ ((⌈max 200 LR⌉₊ : ℕ) : ℝ) :=
      le_trans (le_max_left _ _) (Nat.le_ceil _)
    exact_mod_cast h1
  have hRlb : LR ≤ (R : ℝ) := by
    rw [hRdef]; exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  have hRub : (R : ℝ) ≤ 2 * LR := by
    rw [hRdef, hmaxeq]
    have h1 : ((⌈LR⌉₊ : ℕ) : ℝ) < LR + 1 := Nat.ceil_lt_add_one hLRpos.le
    linarith only [h1, hLRge]
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have h2 : (200 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR200
    linarith only [h2]
  have hRle : (R : ℝ) ≤ 202 * (q : ℝ) ^ (3 / 5 : ℝ) := by
    rw [hRdef, hmaxeq]
    have h1 : ((⌈LR⌉₊ : ℕ) : ℝ) < LR + 1 := Nat.ceil_lt_add_one hLRpos.le
    have h2 : (202 : ℝ) ≤ 202 * (q : ℝ) ^ (3 / 5 : ℝ) := by
      have hqP1 : (1 : ℝ) ≤ (q : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
      linarith only [hqP1]
    linarith only [h1, h2, hLRub]
  have hlogR18 : (1 + Real.log (R : ℝ)) ^ 18 ≤ (q : ℝ) ^ (1 / 100 : ℝ) := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
      have h2 : (200 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR200
      linarith only [h2]
    have hlogbound : Real.log (R : ℝ) + 1 ≤ Real.log (q : ℝ) := by
      have h1 : Real.log (R : ℝ) ≤ Real.log (202 * (q : ℝ) ^ (3 / 5 : ℝ)) :=
        Real.log_le_log hRpos hRle
      have h2 : Real.log (202 * (q : ℝ) ^ (3 / 5 : ℝ))
          = Real.log 202 + (3 / 5) * Real.log (q : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hxpos]
      have h3 : Real.log (202 : ℝ) ≤ 201 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 202 by norm_num); linarith only [this]
      have h4 : (202 : ℝ) ≤ (2 / 5) * Real.log (q : ℝ) := by linarith only [hlogq]
      linarith only [h1, h2, h3, h4]
    have hL18 : (Real.log (q : ℝ)) ^ 18 ≤ (q : ℝ) ^ (1 / 100 : ℝ) :=
      logPowLeRpow hxpos hlogq (by norm_num)
    have h1 : (1 + Real.log (R : ℝ)) ^ 18 ≤ (Real.log (q : ℝ)) ^ 18 := by
      have h0 := pow_le_pow_left₀ (by have := Real.log_nonneg hR1; linarith only [this]) hlogbound 18
      simpa only [add_comm] using h0
    linarith only [h1, hL18]
  exact ⟨R, hR200, hRlb, by
    calc (R : ℝ) ≤ 2 * LR := hRub
      _ = 2 * CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ := by rw [hLRdef]; ring, hlogR18⟩

/-- **The detection length of the `E`-interface.**  Under the standing hypotheses plus
`(1 + log R)^18 ≤ q^{1/100}` there is an integer `N` with `N ≥ 2`, `N(1-β₁) ≥ 1`,
`CN·detNE A q β₁ (5+|γ|) R ≤ N`, and `log N ≤ log q·(11/5 + (11/10)·log(5+|γ|)/log q)`. -/
lemma exists_detection_length {q : ℕ} [NeZero q] {A CN β₁ γ : ℝ} {R : ℕ}
    (hA1 : 1 ≤ A) (hCN : 0 < CN) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log (q : ℝ)) < β₁)
    (hlam : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < (1 - β₁) * Real.log (q : ℝ))
    (hlogq : (10 : ℝ) ^ 12 ≤ Real.log (q : ℝ))
    (hlogA : Real.log A ≤ Real.log (q : ℝ) / 10000)
    (hlogCN : Real.log CN ≤ Real.log (q : ℝ) / 10000)
    (hlogR18 : (1 + Real.log (R : ℝ)) ^ 18 ≤ (q : ℝ) ^ (1 / 100 : ℝ)) :
    ∃ N : ℕ, 2 ≤ N ∧ 1 ≤ (N : ℝ) * (1 - β₁) ∧
      CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.log (q : ℝ)
          * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hx1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hLpos : 0 < Real.log (q : ℝ) := by linarith [hlogq]
  have hXe : Real.exp ((10 : ℝ) ^ 12) ≤ (q : ℝ) := (Real.le_log_iff_exp_le hxpos).mp hlogq
  have hXe8 : Real.exp 100000000 ≤ (q : ℝ) := by
    have h : Real.exp 100000000 ≤ Real.exp ((10 : ℝ) ^ 12) := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hβ1pos : 0 < β₁ := by
    have h2 : (0 : ℝ) < 10 * Real.log (q : ℝ) := by linarith
    have h3 : 1 / (10 * Real.log (q : ℝ)) ≤ 1 := by
      rw [div_le_one h2]; linarith
    linarith
  have hδpos : 0 < 1 - β₁ := by linarith
  have hδQ : (1 - β₁)⁻¹ ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    have hlam' : (1 : ℝ) / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2) < 1 - β₁ := by
      have h1 : (1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))) / Real.log (q : ℝ) < 1 - β₁ := by
        have h2 := div_lt_div_of_pos_right hlam hLpos
        rwa [mul_div_cancel_right₀ _ (ne_of_gt hLpos)] at h2
      have h3 : (1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))) / Real.log (q : ℝ)
          = 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2) := by
        rw [div_div]; ring_nf
      linarith only [h1, h3]
    exact (Work.LinnikAreas.BGTZ.repulsionSizesSiegelInv (le_refl 1) (by
      have h1 : (1 : ℝ) < Real.exp ((10 : ℝ) ^ 12) := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
      linarith) hlam').2
  have hA_le : A ≤ (q : ℝ) ^ (1 / 10000 : ℝ) :=
    LogConstLeRpow hxpos hA0 (by norm_num) hlogA
  have hCN_le : CN ≤ (q : ℝ) ^ (1 / 10000 : ℝ) := LogConstLeRpow hxpos hCN (by norm_num) hlogCN
  have hL4 : (Real.log (q : ℝ)) ^ 4 ≤ (q : ℝ) ^ (1 / 100 : ℝ) :=
    Work.LinnikAreas.BGTZ.repulsionSizesLogPow4LeRpow hXe8
  have hA8_le : A ^ 8 ≤ (q : ℝ) ^ (8 / 10000 : ℝ) := by
    have h1 : A ^ 8 ≤ ((q : ℝ) ^ (1 / 10000 : ℝ)) ^ 8 := pow_le_pow_left₀ hA0.le hA_le 8
    have h2 : ((q : ℝ) ^ (1 / 10000 : ℝ)) ^ 8 = (q : ℝ) ^ (8 / 10000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith only [h1, h2]
  have hexp8 : Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) ≤ (q : ℝ) ^ (8 / 1000 : ℝ) := by
    have h1000 : (1000 : ℝ) ≤ (Real.log (q : ℝ)) ^ (1 / 4 : ℝ) := by
      have h1 : ((1000 : ℝ) ^ 4) ≤ Real.log (q : ℝ) := by
        have h2 : ((1000 : ℝ) ^ 4) = (10 : ℝ) ^ 12 := by norm_num
        linarith only [h2, hlogq]
      have h3 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (1000 : ℝ) ^ 4) h1
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have h4 : (((1000 : ℝ) ^ 4)) ^ (1 / 4 : ℝ) = 1000 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]; norm_num
      linarith only [h3, h4]
    have hsplit : (Real.log (q : ℝ)) ^ (1 / 4 : ℝ) * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)
        = Real.log (q : ℝ) := by
      calc (Real.log (q : ℝ)) ^ (1 / 4 : ℝ) * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)
          = (Real.log (q : ℝ)) ^ ((1 : ℝ) / 4 + 3 / 4) := (Real.rpow_add hLpos (1 / 4) (3 / 4)).symm
        _ = Real.log (q : ℝ) := by rw [show ((1 : ℝ) / 4 + 3 / 4) = 1 by norm_num, Real.rpow_one]
    have h34 : (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (q : ℝ) / 1000 := by
      have hEq : (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)
          = Real.log (q : ℝ) / (Real.log (q : ℝ)) ^ (1 / 4 : ℝ) := by
        rw [eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hLpos _)), mul_comm]
        exact hsplit
      rw [hEq]
      exact div_le_div_of_nonneg_left hLpos.le (by norm_num) h1000
    have h1 : 8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) ≤ Real.log (q : ℝ) * (8 / 1000) := by
      have h2 : (8 : ℝ) * (Real.log (q : ℝ) / 1000) = Real.log (q : ℝ) * (8 / 1000) := by ring
      linarith only [h34, h2]
    calc Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
        ≤ Real.exp (Real.log (q : ℝ) * (8 / 1000)) := Real.exp_le_exp.mpr h1
      _ = (q : ℝ) ^ (8 / 1000 : ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hδ6 : (1 - β₁) ^ (-6 : ℝ) ≤ (q : ℝ) ^ (7 / 100 : ℝ) := by
    have h1 := RpowNegNatLe hxpos hδpos 6 hδQ
    have h2 : (1 - β₁) ^ (-(6 : ℝ)) ≤ (q : ℝ) ^ ((6 : ℝ) / 100)
        * (Real.log (q : ℝ)) ^ (2 * 6) := by
      simpa only [Nat.cast_ofNat] using h1
    have h12 : (Real.log (q : ℝ)) ^ (2 * 6) ≤ (q : ℝ) ^ (1 / 100 : ℝ) := by
      simpa using logPowLeRpow hxpos hlogq (n := 12) (by norm_num)
    have h3 : (q : ℝ) ^ ((6 : ℝ) / 100) * (Real.log (q : ℝ)) ^ (2 * 6)
        ≤ (q : ℝ) ^ (6 / 100 : ℝ) * (q : ℝ) ^ (1 / 100 : ℝ) := by
      rw [show ((6 : ℝ) / 100) = (6 / 100 : ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left h12 (Real.rpow_nonneg hxpos.le _)
    have h4 : (q : ℝ) ^ (6 / 100 : ℝ) * (q : ℝ) ^ (1 / 100 : ℝ) = (q : ℝ) ^ (7 / 100 : ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    linarith only [h2, h3, h4]
  have hδ50 : (1 - β₁)⁻¹ ≤ (q : ℝ) ^ (1 / 50 : ℝ) := by
    have hLsq : (1 : ℝ) ≤ (Real.log (q : ℝ)) ^ 2 := one_le_pow₀ (by linarith only [hlogq])
    have hLs : (Real.log (q : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 4 := by
      calc (Real.log (q : ℝ)) ^ 2 = (Real.log (q : ℝ)) ^ 2 * 1 := by ring
        _ ≤ (Real.log (q : ℝ)) ^ 2 * (Real.log (q : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq (by positivity)
        _ = (Real.log (q : ℝ)) ^ 4 := by ring
    have h1 : (q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2
        ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (q : ℝ) ^ (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left (le_trans hLs hL4) (Real.rpow_nonneg hxpos.le _)
    have h2 : (q : ℝ) ^ (1 / 100 : ℝ) * (q : ℝ) ^ (1 / 100 : ℝ) = (q : ℝ) ^ (1 / 50 : ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    linarith only [hδQ, h1, h2]
  have hLNub : CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R
      ≤ (q : ℝ) ^ (2199 / 1000 : ℝ) * (5 + |γ|) ^ (26 / 25 : ℝ) := by
    have hdet : Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R
        = A ^ 8 * (q : ℝ) ^ (52 / 25 : ℝ) * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (5 + |γ|) ^ (26 / 25 : ℝ) * (1 - β₁) ^ (-6 : ℝ) * (1 + Real.log (R : ℝ)) ^ 18 := by
      simp only [Work.LinnikAreas.BGTZ.detNE, Work.LinnikAreas.BGTZ.thA]
      norm_num
    rw [hdet]
    have hmain : CN * (A ^ 8 * (q : ℝ) ^ (52 / 25 : ℝ)
          * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (5 + |γ|) ^ (26 / 25 : ℝ)
          * (1 - β₁) ^ (-6 : ℝ) * (1 + Real.log (R : ℝ)) ^ 18)
        ≤ (q : ℝ) ^ (1 / 10000 : ℝ) * ((q : ℝ) ^ (8 / 10000 : ℝ) * (q : ℝ) ^ (52 / 25 : ℝ)
          * (q : ℝ) ^ (8 / 1000 : ℝ) * (5 + |γ|) ^ (26 / 25 : ℝ) * (q : ℝ) ^ (7 / 100 : ℝ)
          * (q : ℝ) ^ (1 / 100 : ℝ)) := by
      gcongr
    calc CN * (A ^ 8 * (q : ℝ) ^ (52 / 25 : ℝ)
          * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (5 + |γ|) ^ (26 / 25 : ℝ)
          * (1 - β₁) ^ (-6 : ℝ) * (1 + Real.log (R : ℝ)) ^ 18)
        ≤ (q : ℝ) ^ (1 / 10000 : ℝ) * ((q : ℝ) ^ (8 / 10000 : ℝ) * (q : ℝ) ^ (52 / 25 : ℝ)
          * (q : ℝ) ^ (8 / 1000 : ℝ) * (5 + |γ|) ^ (26 / 25 : ℝ) * (q : ℝ) ^ (7 / 100 : ℝ)
          * (q : ℝ) ^ (1 / 100 : ℝ)) := hmain
      _ = ((q : ℝ) ^ (1 / 10000 : ℝ) * (q : ℝ) ^ (8 / 10000 : ℝ) * (q : ℝ) ^ (52 / 25 : ℝ)
          * (q : ℝ) ^ (8 / 1000 : ℝ) * (q : ℝ) ^ (7 / 100 : ℝ) * (q : ℝ) ^ (1 / 100 : ℝ))
          * (5 + |γ|) ^ (26 / 25 : ℝ) := by ring
      _ ≤ (q : ℝ) ^ (2199 / 1000 : ℝ) * (5 + |γ|) ^ (26 / 25 : ℝ) := by
          have h : ((q : ℝ) ^ (1 / 10000 : ℝ) * (q : ℝ) ^ (8 / 10000 : ℝ)
              * (q : ℝ) ^ (52 / 25 : ℝ) * (q : ℝ) ^ (8 / 1000 : ℝ) * (q : ℝ) ^ (7 / 100 : ℝ)
              * (q : ℝ) ^ (1 / 100 : ℝ)) ≤ (q : ℝ) ^ (2199 / 1000 : ℝ) := by
            rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
              ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
            apply Real.rpow_le_rpow_of_exponent_le hx1
            norm_num
          exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by positivity) _)
  have hq3th : (3 : ℝ) ≤ (q : ℝ) ^ (1 / 1000 : ℝ) := by
    rw [Real.rpow_def_of_pos hxpos]
    have h1 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith only [this]
    have h2 : Real.exp 2 ≤ Real.exp (Real.log (q : ℝ) * (1 / 1000)) :=
      Real.exp_le_exp.mpr (by linarith only [hlogq])
    linarith only [h1, h2]
  set NN : ℕ := ⌈max (max 2 (CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R))
    ((1 - β₁)⁻¹)⌉₊ with hNNdef
  have hNub : (NN : ℝ) ≤ (q : ℝ) ^ (11 / 5 : ℝ) * (5 + |γ|) ^ (11 / 10 : ℝ) := by
    rw [hNNdef]
    exact Work.LinnikAreas.BGTZArith.repulsionSizesNHeightAux hx1 hq3th
      (le_of_lt (inv_pos.mpr hδpos)) hLNub hδ50
  have hN2 : 2 ≤ NN := by
    rw [hNNdef]
    have h1 : (2 : ℝ) ≤ ((⌈max (max 2 (CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R))
        ((1 - β₁)⁻¹)⌉₊ : ℕ) : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (Nat.le_ceil _)
    exact_mod_cast h1
  have hNδ : 1 ≤ (NN : ℝ) * (1 - β₁) := by
    rw [hNNdef]
    have hNge : (1 - β₁)⁻¹ ≤ ((⌈max (max 2 (CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R))
        ((1 - β₁)⁻¹)⌉₊ : ℕ) : ℝ) := le_trans (le_max_right _ _) (Nat.le_ceil _)
    have hmul := mul_le_mul_of_nonneg_right hNge hδpos.le
    have hone : (1 - β₁)⁻¹ * (1 - β₁) = 1 := inv_mul_cancel₀ hδpos.ne'
    linarith only [hmul, hone]
  have hLNlb : CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R ≤ (NN : ℝ) := by
    rw [hNNdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_ceil _)
  have hlogNub : Real.log (NN : ℝ) ≤ Real.log (q : ℝ)
      * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
    have hpos : (0 : ℝ) < (NN : ℝ) := by
      have h2 : (2 : ℝ) ≤ (NN : ℝ) := by exact_mod_cast hN2
      linarith only [h2]
    have hlogN := Real.log_le_log hpos hNub
    have hval : Real.log ((q : ℝ) ^ (11 / 5 : ℝ) * (5 + |γ|) ^ (11 / 10 : ℝ))
        = Real.log (q : ℝ) * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hxpos,
        Real.log_rpow (by have := abs_nonneg γ; linarith only [this] : (0 : ℝ) < 5 + |γ|)]
      have hc : Real.log (q : ℝ) * (Real.log (5 + |γ|) / Real.log (q : ℝ)) = Real.log (5 + |γ|) := by
        rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (ne_of_gt hLpos)
      linear_combination (-(11 / 10 : ℝ)) * hc
    linarith only [hlogN, hval]
  exact ⟨NN, hN2, hNδ, hLNlb, hlogNub⟩

theorem RepulsionSizesE {q : ℕ} [NeZero q] {A CR CN β₁ γ : ℝ}
    (hA1 : 1 ≤ A) (hCR : 1 ≤ CR) (hCN : 0 < CN) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log (q : ℝ)) < β₁)
    (hlam : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < (1 - β₁) * Real.log (q : ℝ))
    (hlogq : (10 : ℝ) ^ 12 ≤ Real.log (q : ℝ))
    (hlogA : Real.log A ≤ Real.log (q : ℝ) / 10000)
    (hlogCR : Real.log CR ≤ Real.log (q : ℝ) / 10000)
    (hlogCN : Real.log CN ≤ Real.log (q : ℝ) / 10000) :
    ∃ R N : ℕ, 200 ≤ R ∧ 2 ≤ N ∧ 1 ≤ (N : ℝ) * (1 - β₁) ∧
      CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ ≤ (R : ℝ) ∧
      (R : ℝ) ≤ 2 * CR * Work.LinnikAreas.BGTZ.sieveX A q β₁ ∧
      CN * Work.LinnikAreas.BGTZ.detNE A q β₁ (5 + |γ|) R ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.log (q : ℝ)
          * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
  obtain ⟨R, hR200, hRlb, hRub, hlogR18⟩ :=
    exists_sifting_level hA1 hCR hβ₁lt hβ₁big hlam hlogq hlogA hlogCR
  obtain ⟨N, hN2, hNδ, hLNlb, hlogNub⟩ :=
    exists_detection_length (R := R) hA1 hCN hβ₁lt hβ₁big hlam hlogq hlogA hlogCN hlogR18
  exact ⟨R, N, hR200, hN2, hNδ, hRlb, hRub, hLNlb, hlogNub⟩

end Work.LinnikAreas.BGTZ.E
