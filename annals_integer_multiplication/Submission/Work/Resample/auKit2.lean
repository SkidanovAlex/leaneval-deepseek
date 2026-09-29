import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Fx.expRec

set_option autoImplicit false
set_option maxHeartbeats 100000000

namespace Work.Resample
open HvdH Work.Fx

theorem habs_cast (z : ℤ) : |((z : ℤ) : ℝ)| = (z.natAbs : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

theorem tdiv_abs_le (a b : ℤ) : |((a.tdiv b : ℤ) : ℝ)| ≤ |(a : ℝ)| / |(b : ℝ)| := by
  rw [habs_cast (a.tdiv b), habs_cast a, habs_cast b, Int.natAbs_tdiv]
  exact Nat.cast_div_le

theorem auH_succ (p : ℕ) (Z : ℤ) (j : ℕ) :
    auH p Z (j + 1) = (2 : ℤ) ^ auPrec p +
      Int.tdiv (Int.tdiv (Z * auH p Z j) ((2 : ℤ) ^ auPrec p))
        ((auNstep p : ℤ) - (j : ℤ)) := rfl

theorem auHSize (p : ℕ) (Z : ℤ) (hZ0 : 0 ≤ Z) (hZ : Z ≤ auBnd p) (i : ℕ)
    (hi : i ≤ auNstep p) : (auH p (-Z) i).natAbs ≤ 2 ^ (5 * p + 130) := by
  set m : ℕ := auNstep p with hm
  set ER : ℝ := (2 : ℝ) ^ auPrec p with hER
  set q : ℝ := (Z : ℝ) / ER with hq
  have hERpos : 0 < ER := by rw [hER]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hZnn : (0 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ0
  have hZR : (Z : ℝ) ≤ ((p : ℝ) + 10) * ER := by
    have h1 : (Z : ℝ) ≤ (auBnd p : ℝ) := by exact_mod_cast hZ
    have h2 : (auBnd p : ℝ) = ((p : ℝ) + 10) * ER := by
      rw [auBnd, auEn, hER]; push_cast; ring
    rwa [h2] at h1
  have hqle : q ≤ (p : ℝ) + 10 := by rw [hq, div_le_iff₀ hERpos]; exact hZR
  have hE : (((2 : ℤ) ^ auPrec p : ℤ) : ℝ) = ER := by rw [hER]; push_cast; ring
  have key : ∀ j ≤ m, |((auH p (-Z) j : ℤ) : ℝ)| ≤ (ER + 2) * Work.Fx.pot q (m - j) (j + 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : ((auH p (-Z) 0 : ℤ) : ℝ) = ER := by
        show (((2 : ℤ) ^ auPrec p : ℤ) : ℝ) = ER
        exact hE
      rw [h0, abs_of_pos hERpos]
      have hp1 : Work.Fx.pot q (m - 0) (0 + 1) = 1 := by
        rw [show m - 0 = m by omega, show 0 + 1 = 1 by omega, Work.Fx.pot,
          Finset.sum_range_one, pow_zero, one_mul, Nat.add_zero]
        exact div_self (by exact_mod_cast Nat.factorial_ne_zero m)
      rw [hp1, mul_one]
      linarith
    | succ j ih =>
      intro hj
      have hjm : j < m := by omega
      have ihj := ih (show j ≤ m by omega)
      have hMj : 1 ≤ m - j := by omega
      have hMpos : (0 : ℝ) < ((m - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - j)
      have hsub : (m : ℤ) - (j : ℤ) = ((m - j : ℕ) : ℤ) := (Nat.cast_sub (le_of_lt hjm)).symm
      have h0 := auH_succ p (-Z) j
      have hrec : ((auH p (-Z) (j + 1) : ℤ) : ℝ)
          = ER + ((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
              ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ) := by
        rw [h0, Int.cast_add, hE]
      have h1 : |((Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p) : ℤ) : ℝ)|
          ≤ (Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER := by
        calc |((Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p) : ℤ) : ℝ)|
            ≤ |((((-Z) * auH p (-Z) j) : ℤ) : ℝ)| / |((((2 : ℤ) ^ auPrec p) : ℤ) : ℝ)| :=
              tdiv_abs_le _ _
          _ = (Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER := by
              rw [hE, abs_of_pos hERpos,
                show (((-Z) * auH p (-Z) j : ℤ)) = -(Z * auH p (-Z) j) by ring,
                Int.cast_neg, abs_neg, Int.cast_mul, abs_mul, abs_of_nonneg hZnn]
      have hinner : |((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
            ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ)|
          ≤ ((Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER) / ((m - j : ℕ) : ℝ) := by
        rw [hsub]
        have hD : |(((m - j : ℕ) : ℤ) : ℝ)| = ((m - j : ℕ) : ℝ) := by
          rw [habs_cast]
          simp
        have h := tdiv_abs_le (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
          (((m - j : ℕ) : ℤ))
        rw [hD] at h
        exact le_trans h (div_le_div_of_nonneg_right h1 hMpos.le)
      have h2 : |ER + ((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
              ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ)|
          ≤ ER + ((Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER) / ((m - j : ℕ) : ℝ) := by
        calc |ER + ((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
                ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ)|
            ≤ |ER| + |((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
                ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ)| := abs_add_le _ _
          _ = ER + |((Int.tdiv (Int.tdiv ((-Z) * auH p (-Z) j) ((2 : ℤ) ^ auPrec p))
                ((m : ℤ) - (j : ℤ)) : ℤ) : ℝ)| := by rw [abs_of_pos hERpos]
          _ ≤ ER + ((Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER) / ((m - j : ℕ) : ℝ) :=
              add_le_add le_rfl hinner
      have hrec2 : Work.Fx.pot q (m - j - 1) (j + 2)
          = 1 + (q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1) := by
        have h := (Work.Fx.expRec).2.1 q (m - j) (j + 1) hMj hq0
        rw [show j + 1 + 1 = j + 2 by omega] at h
        exact h
      have hstep : ER + ((Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER) / ((m - j : ℕ) : ℝ)
          ≤ (ER + 2) * Work.Fx.pot q (m - (j + 1)) (j + 1 + 1) := by
        have h3 : (Z : ℝ) * |((auH p (-Z) j : ℤ) : ℝ)| / ER
            = q * |((auH p (-Z) j : ℤ) : ℝ)| := by rw [hq]; ring
        have hgoal : Work.Fx.pot q (m - (j + 1)) (j + 1 + 1) = Work.Fx.pot q (m - j - 1) (j + 2) := by
          rw [show m - (j + 1) = m - j - 1 by omega, show j + 1 + 1 = j + 2 by omega]
        rw [hgoal, hrec2, h3]
        have h5 : q * |((auH p (-Z) j : ℤ) : ℝ)| / ((m - j : ℕ) : ℝ)
            ≤ (ER + 2) * ((q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) := by
          have h4 : q * |((auH p (-Z) j : ℤ) : ℝ)|
              ≤ q * ((ER + 2) * Work.Fx.pot q (m - j) (j + 1)) :=
            mul_le_mul_of_nonneg_left ihj hq0
          have h4' : q * ((ER + 2) * Work.Fx.pot q (m - j) (j + 1)) / ((m - j : ℕ) : ℝ)
              = (ER + 2) * ((q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) := by
            rw [div_eq_mul_inv]
            ring
          calc q * |((auH p (-Z) j : ℤ) : ℝ)| / ((m - j : ℕ) : ℝ)
              ≤ q * ((ER + 2) * Work.Fx.pot q (m - j) (j + 1)) / ((m - j : ℕ) : ℝ) :=
                div_le_div_of_nonneg_right h4 hMpos.le
            _ = (ER + 2) * ((q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) := h4'
        calc ER + q * |((auH p (-Z) j : ℤ) : ℝ)| / ((m - j : ℕ) : ℝ)
            ≤ ER + (ER + 2) * ((q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) :=
              add_le_add le_rfl h5
          _ ≤ (ER + 2) + (ER + 2) * ((q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) :=
              add_le_add (by linarith) le_rfl
          _ = (ER + 2) * (1 + (q / ((m - j : ℕ) : ℝ)) * Work.Fx.pot q (m - j) (j + 1)) := by
              ring
      rw [hrec]
      exact le_trans h2 hstep
  have hi' := key i hi
  have hpot := (Work.Fx.expRec).2.2.1 q hq0 (m - i) (i + 1)
  have hE2 : ER + 2 ≤ 2 ^ (3 * p + 102) := by
    have h1 : ER = (2 : ℝ) ^ (3 * p + 100) := by rw [hER, show auPrec p = 3 * p + 100 from rfl]
    rw [h1]
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (3 * p + 100) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (3 * p + 100) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ (3 * p + 100) + 2 ≤ 2 ^ (3 * p + 100) + 2 ^ (3 * p + 100) := by linarith
      _ = 2 * 2 ^ (3 * p + 100) := by ring
      _ = 2 ^ (3 * p + 101) := by
          rw [show 3 * p + 101 = 3 * p + 100 + 1 by omega, pow_succ]; ring
      _ ≤ 2 ^ (3 * p + 102) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hexp : Real.exp q ≤ 2 ^ (2 * p + 20) := by
    calc Real.exp q ≤ Real.exp ((p : ℝ) + 10) := Real.exp_le_exp_of_le hqle
      _ = Real.exp 1 ^ (p + 10) := by
          rw [show ((p : ℝ) + 10) = ((p + 10 : ℕ) : ℝ) * 1 by push_cast; ring, Real.exp_nat_mul]
      _ ≤ (4 : ℝ) ^ (p + 10) :=
          pow_le_pow_left₀ (Real.exp_nonneg 1)
            (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ (4 : ℝ)) (p + 10)
      _ = 2 ^ (2 * p + 20) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
            show 2 * (p + 10) = 2 * p + 20 by ring]
  have hfin : |((auH p (-Z) i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (5 * p + 130) := by
    calc |((auH p (-Z) i : ℤ) : ℝ)| ≤ (ER + 2) * Work.Fx.pot q (m - i) (i + 1) := hi'
      _ ≤ (ER + 2) * Real.exp q := mul_le_mul_of_nonneg_left hpot (by linarith)
      _ ≤ 2 ^ (3 * p + 102) * 2 ^ (2 * p + 20) :=
          mul_le_mul hE2 hexp (Real.exp_nonneg q) (by positivity)
      _ = 2 ^ (5 * p + 122) := by
          rw [← pow_add, show 3 * p + 102 + (2 * p + 20) = 5 * p + 122 by omega]
      _ ≤ 2 ^ (5 * p + 130) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (((auH p (-Z) i).natAbs : ℕ) : ℝ) ≤ ((2 ^ (5 * p + 130) : ℕ) : ℝ) := by
    rw [← habs_cast]
    push_cast
    exact hfin
  exact_mod_cast h2


/-! ### size helper -/

theorem isz_of_natAbs_le {p m : ℕ} {z : ℤ} (h : z.natAbs ≤ 2 ^ m) (hm : m + 3 ≤ auSZ p) :
    isz z ≤ auSZ p := by
  have h1 : z.natAbs.size ≤ m + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt h
      (Nat.pow_lt_pow_right one_lt_two (by omega : m < m + 1)))
  rw [isz]
  omega

/-- `K * u ≤ auSB p KS`. -/
theorem au_le_mone {K KS p : ℕ} (hK : K ≤ KS) {u : ℕ} (hu : u ≤ auSZ p) :
    K * u ≤ auSB p KS := by
  rw [auSB]
  calc K * u ≤ KS * auSZ p := Nat.mul_le_mul hK hu
    _ ≤ KS * (auSZ p + 8) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith [auSZ_ge p])

/-- `K * u * v ≤ auSB p KS`. -/
theorem au_le_mul {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ auSZ p) (hv : v ≤ auSZ p) :
    K * u * v ≤ auSB p KS := by
  rw [auSB]
  have h1 : K * u * v ≤ KS * auSZ p * auSZ p :=
    Nat.mul_le_mul (Nat.mul_le_mul hK hu) hv
  have h2 : KS * auSZ p * auSZ p ≤ KS * (auSZ p + 8) ^ 2 := by
    have h : auSZ p * auSZ p ≤ (auSZ p + 8) ^ 2 := by nlinarith [auSZ_ge p]
    calc KS * auSZ p * auSZ p = KS * (auSZ p * auSZ p) := by ring
      _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left KS h
  exact le_trans h1 h2

theorem tdiv_zero' (a : ℤ) : a.tdiv 0 = 0 := by
  rw [Int.tdiv_eq_ediv, Int.ediv_zero, zero_add]
  split <;> rfl


/-! ## The assembly -/

theorem auWt_zero (p t : ℕ) (N : ℤ) : auWt p 0 t N = 0 := by
  have hZ : auZ p 0 t N = 0 := by
    rw [auZ]
    have hd : (((0 : ℕ) : ℤ)) ^ 2 * ((t : ℤ)) ^ 2 = 0 := by norm_num
    rw [hd, tdiv_zero']
  rw [auWt]
  rw [if_pos (by rw [hZ]; positivity)]
  have hd : (2 : ℤ) ^ (auPrec p - p) * (2 * ((0 : ℕ) : ℤ)) = 0 := by norm_num
  rw [hd, tdiv_zero']

theorem auWt_eq_zero_of_not_guard (p α t : ℕ) (N : ℤ) (h : ¬ (auZ p α t N ≤ auBnd p)) :
    auWt p α t N = 0 := by
  rw [auWt]
  exact if_neg (by simpa only [auBnd, auEn] using h)

theorem auWt_eq_of_guard (p α t : ℕ) (N : ℤ) (h : auZ p α t N ≤ auBnd p) :
    auWt p α t N = Int.tdiv (auH p (-(auZ p α t N)) (auNstep p)) (auEn2 p α) := by
  rw [auWt]
  rw [if_pos (by simpa only [auBnd, auEn] using h)]
  rw [auEn2, auEnP]

theorem auEn2_ne_zero (p α : ℕ) (hα : α ≠ 0) : auEn2 p α ≠ 0 := by
  rw [auEn2, auEnP]
  have h1 : (0 : ℤ) < (2 : ℤ) ^ (auPrec p - p) := pow_pos (by norm_num) _
  have h2 : (0 : ℤ) < 2 * (α : ℤ) := by
    have : (0 : ℤ) < (α : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hα
    linarith
  exact ne_of_gt (mul_pos h1 h2)

theorem auFlg_eq_zero_iff (p α t : ℕ) (N : ℤ) :
    auFlg p α t N = 0 ↔ auZ p α t N ≤ auBnd p := by
  rw [auFlg]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rw [if_pos hc] at h
    norm_num at h
  · intro h
    rw [if_neg (not_lt.mpr h)]

theorem auFlg_ne_zero_iff (p α t : ℕ) (N : ℤ) :
    auFlg p α t N ≠ 0 ↔ auBnd p < auZ p α t N := by
  rw [auFlg]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rw [if_neg (not_lt.mpr hc)] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    norm_num

theorem eq_zero_flag (α : ℕ) : (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0) = 0 ↔ α ≠ 0 := by
  constructor
  · intro h hα
    rw [hα] at h
    norm_num at h
  · intro hα
    rw [if_neg]
    intro hc
    exact hα (by exact_mod_cast hc.symm)

theorem eq_zero_flag_ne (α : ℕ) : (if (0 : ℤ) = (α : ℤ) then (1 : ℤ) else 0) ≠ 0 ↔ α = 0 := by
  constructor
  · intro h
    by_contra hc
    exact h ((eq_zero_flag α).mpr hc)
  · intro h
    rw [h]
    norm_num
end Work.Resample
