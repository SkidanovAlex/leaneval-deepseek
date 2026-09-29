import Mathlib
import Submission.Work.Recursion.defs
import Submission.Work.Recursion.sizeProduct
import Submission.Work.Recursion.pparSqrtBound
import Submission.Work.Recursion.aparBound

namespace Work.Recursion

open HvdH

/- Helper namespace for the §5.1 parameter estimates. -/
namespace ParamsProofAux

/-- `Nat.clog 2 m = ⌈logb 2 m⌉₊`. -/
lemma clog_eq_ceil_logb (m : ℕ) : Nat.clog 2 m = ⌈Real.logb 2 (m : ℝ)⌉₊ :=
  (Real.natCeil_logb_natCast 2 m).symm

/-- `Nat.log 2 m = ⌊logb 2 m⌋₊`. -/
lemma log_eq_floor_logb (m : ℕ) : Nat.log 2 m = ⌊Real.logb 2 (m : ℝ)⌋₊ :=
  (Real.natFloor_logb_natCast 2 m).symm

/-- `⌈log₂ m⌉ ≤ log₂ m + 1`. -/
lemma clog_le_logb_add_one (m : ℕ) (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have h1 : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have h2 : ((⌈Real.logb 2 (m : ℝ)⌉₊ : ℕ) : ℝ) < Real.logb 2 (m : ℝ) + 1 :=
    Nat.ceil_lt_add_one h1
  rw [← clog_eq_ceil_logb m] at h2
  linarith

/-- For `1 ≤ m`, the bit size is `⌊log₂ m⌋ + 1`. -/
lemma size_eq_log_add_one {m : ℕ} (hm : 1 ≤ m) : m.size = Nat.log 2 m + 1 := by
  have h1 : Nat.log 2 m < m.size := by
    rw [Nat.lt_size]; exact Nat.pow_log_le_self 2 (by omega)
  have h2 : m.size ≤ Nat.log 2 m + 1 := by
    rw [Nat.size_le]; exact Nat.lt_pow_succ_log_self (by norm_num) m
  omega

/-- `size m ≤ log₂ m + 1` for `1 ≤ m`. -/
lemma size_le_logb_add_one {m : ℕ} (hm : 1 ≤ m) :
    (m.size : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have h3 := size_eq_log_add_one hm
  have h1 : 0 ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  have h2 : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 (m : ℝ) := by
    rw [log_eq_floor_logb m]; exact Nat.floor_le h1
  rw [h3]; push_cast; linarith

/-- `log₂ m ≤ size m` for `1 ≤ m`. -/
lemma logb_le_size {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 (m : ℝ) ≤ (m.size : ℝ) := by
  have h3 := size_eq_log_add_one hm
  have h2 : Real.logb 2 (m : ℝ) < ((Nat.log 2 m : ℕ) : ℝ) + 1 := by
    rw [log_eq_floor_logb m]; exact Nat.lt_floor_add_one _
  rw [h3]; push_cast; linarith

end ParamsProofAux

open ParamsProofAux

/-- Paper §5.1 parameter estimates, for `n ≥ 2`. -/
theorem params (n : ℕ) (hn : 2 ≤ n) :
    (1 ≤ HvdH.bpar n ∧ (HvdH.bpar n : ℝ) ≤ Real.logb 2 (n : ℝ) + 1) ∧
    (1 ≤ HvdH.Tpar n ∧ (HvdH.Tpar n : ℝ) = 2 ^ (HvdH.kTpar n : ℝ) ∧
      (HvdH.Tpar n : ℝ) * (HvdH.bpar n : ℝ) < 8 * (n : ℝ) ∧
      (HvdH.kTpar n : ℝ) ≤ Real.logb 2 (n : ℝ) + 3) ∧
    (1 ≤ HvdH.rpar n ∧ HvdH.ppar n = 6 * HvdH.bpar n) ∧
    (((3 * HvdH.rpar n * HvdH.ppar n).size : ℝ) ≤
        (HvdH.kTpar n : ℝ) / (HvdH.D : ℝ) + Real.logb 2 (18 * (HvdH.bpar n : ℝ)) + 3) ∧
    (((Nat.sqrt (HvdH.ppar n) : ℝ) + 1) ≤ 4 * Real.sqrt (HvdH.bpar n : ℝ)) ∧
    ((HvdH.apar n : ℝ) ≤
        ((12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) + 1) * (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (Real.logb 2 (n : ℝ) ≤ (n.size : ℝ)) ∧
    (∀ m : ℕ, 1 ≤ m → (m.size : ℝ) ≤ Real.logb 2 (m : ℝ) + 1) := by
  have hb1 : 1 ≤ HvdH.bpar n := by
    show 1 ≤ Nat.clog 2 n
    exact Nat.clog_pos (by norm_num) (by omega)
  have hbpos : 0 < HvdH.bpar n := hb1
  have hq2 : 2 ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by
    rw [Nat.le_div_iff_mul_le hbpos]
    have hbn : HvdH.bpar n ≤ n := by
      show Nat.clog 2 n ≤ n
      rw [Nat.clog_le_iff_le_pow (by norm_num)]
      exact le_of_lt Nat.lt_two_pow_self
    omega
  have hq1 : 1 ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by omega
  have hq4n : (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ 4 * n := by
    rw [Nat.div_le_iff_le_mul_add_pred hbpos]
    have h1 : 4 * n ≤ HvdH.bpar n * (4 * n) := by
      have := Nat.mul_le_mul_right (4 * n) hb1
      simpa using this
    omega
  have hk_eq : HvdH.kTpar n = Nat.clog 2 ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) := rfl
  have hk1 : 1 ≤ HvdH.kTpar n := by
    rw [hk_eq]; exact Nat.clog_pos (by norm_num) hq2
  have hpow : 2 ^ (HvdH.kTpar n - 1) < (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hq2
    rw [← hk_eq, Nat.pred_eq_sub_one] at h
    exact h
  have hpred : 2 ^ (HvdH.kTpar n - 1) * HvdH.bpar n ≤ 4 * n - 1 := by
    have hle : 2 ^ (HvdH.kTpar n - 1) ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n - 1 := by
      have h := Nat.le_pred_of_lt hpow
      rwa [Nat.pred_eq_sub_one] at h
    have hmul := Nat.mul_le_mul_right (HvdH.bpar n) hle
    have hqmul : ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) * HvdH.bpar n ≤
        4 * n + HvdH.bpar n - 1 := Nat.div_mul_le_self _ _
    have hsub : ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n - 1) * HvdH.bpar n
        = ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) * HvdH.bpar n - HvdH.bpar n := by
      rw [Nat.sub_mul, Nat.one_mul]
    omega
  have hTb_nat : HvdH.Tpar n * HvdH.bpar n < 8 * n := by
    show 2 ^ HvdH.kTpar n * HvdH.bpar n < 8 * n
    rw [show HvdH.kTpar n = (HvdH.kTpar n - 1) + 1 by omega, Nat.pow_succ]
    have h2 : 2 ^ (HvdH.kTpar n - 1) * 2 * HvdH.bpar n
        = 2 * (2 ^ (HvdH.kTpar n - 1) * HvdH.bpar n) := by ring
    rw [h2]
    omega
  refine ⟨⟨hb1, clog_le_logb_add_one n (by omega)⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, rfl⟩, ?_, ?_, ?_,
    logb_le_size (by omega), fun m hm => size_le_logb_add_one hm⟩
  · show 1 ≤ (2 : ℕ) ^ _
    exact Nat.one_le_two_pow
  · unfold HvdH.Tpar
    push_cast
    rw [Real.rpow_natCast]
  · exact_mod_cast hTb_nat
  · rw [hk_eq] at *
    have hclog := clog_le_logb_add_one ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) hq1
    have hlogle : Real.logb 2 ((((4 * n + HvdH.bpar n - 1) / HvdH.bpar n : ℕ) : ℝ)) ≤
        Real.logb 2 ((4 * n : ℕ) : ℝ) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact_mod_cast hq1
      · exact_mod_cast hq4n
    have hlog4 : Real.logb 2 ((4 * n : ℕ) : ℝ) = Real.logb 2 (n : ℝ) + 2 := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      rw [show ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) by push_cast; ring]
      rw [Real.logb_mul (by norm_num : (4 : ℝ) ≠ 0) hn0]
      have h4 : Real.logb 2 (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        norm_num
      rw [h4]; ring
    linarith
  · show 1 ≤ HvdH.rpar n
    exact Nat.one_le_two_pow
  · exact sizeProduct n hn
  · exact pparSqrtBound n hn
  · exact aparBound n hn

end Work.Recursion
