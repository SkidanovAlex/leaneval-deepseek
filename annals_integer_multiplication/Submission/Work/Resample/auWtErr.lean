import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.fxPotSucc
import Submission.Work.Resample.auTailExp
import Submission.Work.Resample.auZ_y_close
import Submission.Work.Resample.auZ_y_far
import Submission.Work.Resample.auH_err
import Submission.Work.Fx.expStepErr
import Submission.Work.Fx.expRec

namespace Work.Resample


private lemma exp_abs_sub_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have key : ∀ x y : ℝ, x ≤ y → y ≤ 0 → Real.exp y - Real.exp x ≤ y - x := by
    intro x y hxy hy
    have h0 : 0 ≤ y - x := by linarith
    have hstep : Real.exp (y - x) - 1 ≤ (y - x) * Real.exp (y - x) := by
      have h1 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by
        linarith [Real.add_one_le_exp (-(y - x))]
      have h2 : (1 - (y - x)) * Real.exp (y - x) ≤ Real.exp (-(y - x)) * Real.exp (y - x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      have h3 : Real.exp (-(y - x)) * Real.exp (y - x) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [h3] at h2
      nlinarith [h2, Real.exp_pos (y - x)]
    have hfac : Real.exp y - Real.exp x = Real.exp x * (Real.exp (y - x) - 1) := by
      rw [Real.exp_sub, mul_sub, mul_div_cancel₀ _ (Real.exp_ne_zero x), mul_one]
    rw [hfac]
    have h4 : Real.exp x * (Real.exp (y - x) - 1) ≤ Real.exp x * ((y - x) * Real.exp (y - x)) :=
      mul_le_mul_of_nonneg_left hstep (Real.exp_pos x).le
    have h5 : Real.exp x * ((y - x) * Real.exp (y - x)) = (y - x) * Real.exp y := by
      rw [Real.exp_sub]; field_simp; try ring
    rw [h5] at h4
    have h6 : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy
    nlinarith [h4, h6, Real.exp_pos y, h0]
  rcases le_total a b with hab | hba
  · have h1 : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hab))]; ring
    have h2 : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab)]; ring
    rw [h1, h2]
    linarith [key a b hab hb]
  · have h1 : |Real.exp a - Real.exp b| = Real.exp a - Real.exp b := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba))]
    have h2 : |a - b| = a - b := by
      rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    rw [h1, h2]
    linarith [key b a hba ha]

private lemma numcore (p : ℕ) (a : ℝ) (ha : 2 ≤ a) :
    (2:ℝ)^p/(2*a) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20) + 1/(2:ℝ)^(2*p+160) + ((p:ℝ)+13)/(2:ℝ)^(auPrec p)) ≤ 1 := by
  have hc4 : (2:ℝ)^p/(2*a) ≤ (2:ℝ)^p/4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hPv : (2:ℝ)^(auPrec p) = (2:ℝ)^(3*p+100) := by simp only [auPrec]
  have hnum1 : (2:ℝ)^p/(2*a) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20)) ≤ 1/4 := by
    have hs : (2:ℝ)^p/(2*a) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20))
        ≤ ((2:ℝ)^p/4) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20)) :=
      mul_le_mul_of_nonneg_right hc4 (by positivity)
    refine hs.trans ?_
    have he : ((2:ℝ)^p/4) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20)) = (1:ℝ)/(2:ℝ)^81 := by
      rw [hPv]
      have h1 : (2:ℝ)^p ≠ 0 := by positivity
      have h2 : (2:ℝ)^(3*p+100) ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    exact one_div_le_one_div_of_le (by norm_num) (by norm_num : (4:ℝ) ≤ (2:ℝ)^81)
  have hnum2 : (2:ℝ)^p/(2*a) * (1/(2:ℝ)^(2*p+160)) ≤ 1/4 := by
    have hs : (2:ℝ)^p/(2*a) * (1/(2:ℝ)^(2*p+160)) ≤ ((2:ℝ)^p/4) * (1/(2:ℝ)^(2*p+160)) :=
      mul_le_mul_of_nonneg_right hc4 (by positivity)
    refine hs.trans ?_
    have he : ((2:ℝ)^p/4) * (1/(2:ℝ)^(2*p+160)) = (1:ℝ)/(2:ℝ)^(p+162) := by
      have h2 : (2:ℝ)^(2*p+160) ≠ 0 := by positivity
      have h3 : (2:ℝ)^(p+162) ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    exact one_div_le_one_div_of_le (by norm_num) (by
      have : (4:ℝ) = (2:ℝ)^2 := by norm_num
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) (by omega))
  have hnum3 : (2:ℝ)^p/(2*a) * (((p:ℝ)+13)/(2:ℝ)^(auPrec p)) ≤ 1/4 := by
    have hs : (2:ℝ)^p/(2*a) * (((p:ℝ)+13)/(2:ℝ)^(auPrec p))
        ≤ ((2:ℝ)^p/4) * (((p:ℝ)+13)/(2:ℝ)^(auPrec p)) :=
      mul_le_mul_of_nonneg_right hc4 (by positivity)
    refine hs.trans ?_
    have he : ((2:ℝ)^p/4) * (((p:ℝ)+13)/(2:ℝ)^(auPrec p)) = ((p:ℝ)+13)/(2:ℝ)^(2*p+102) := by
      rw [hPv]
      have h1 : (2:ℝ)^p ≠ 0 := by positivity
      have h2 : (2:ℝ)^(3*p+100) ≠ 0 := by positivity
      have h3 : (2:ℝ)^(2*p+102) ≠ 0 := by positivity
      field_simp
      ring
    rw [he, div_le_iff₀ (by positivity)]
    have h2 : ((p:ℝ)+13) ≤ (1/4) * (2:ℝ)^(2*p+102) := by
      have h4 : (1/4) * (2:ℝ)^(2*p+102) = (2:ℝ)^(2*p+100) := by
        rw [show 2*p+102 = 2*p+100+2 by omega, pow_add]; norm_num; ring
      rw [h4]
      have hl : ((p+13:ℕ):ℝ) < (2:ℝ)^(p+13) := by exact_mod_cast Nat.lt_two_pow_self (n := p+13)
      have hp13 : ((p+13:ℕ):ℝ) = (p:ℝ)+13 := by push_cast; ring
      rw [hp13] at hl
      have h3 : (2:ℝ)^(p+13) ≤ (2:ℝ)^(2*p+100) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    linarith
  calc (2:ℝ)^p/(2*a) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20) + 1/(2:ℝ)^(2*p+160) + ((p:ℝ)+13)/(2:ℝ)^(auPrec p))
      = (2:ℝ)^p/(2*a) * ((2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20)) + (2:ℝ)^p/(2*a) * (1/(2:ℝ)^(2*p+160)) + (2:ℝ)^p/(2*a) * (((p:ℝ)+13)/(2:ℝ)^(auPrec p)) := by ring
    _ ≤ 1/4 + 1/4 + 1/4 := by linarith
    _ ≤ 1 := by norm_num

private lemma compute_case (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi| ≤ 1)
    (hg : auZ p α t (N:ℤ) ≤ ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p)) :
    |((Int.tdiv (auH p (-(auZ p α t (N:ℤ))) (auNstep p)) ((2:ℤ)^(auPrec p - p) * (2*(α:ℤ))) : ℤ) : ℝ)
      - (2:ℝ)^p * (1/(2*(α:ℝ))) * Real.exp (-(Real.pi*(N:ℝ)/((α:ℝ)^2*(t:ℝ)^2)))| ≤ 2 := by
  have hpR : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hαR : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
  have hPpos : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  have hPi_pos : (0:ℝ) < (auPi p : ℝ) := by
    have h1 : -1 ≤ (auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi := (abs_le.mp hpi).1
    have h2 : 1 < (2:ℝ)^(auPrec p) * Real.pi := by
      have hp2 : (1:ℝ) ≤ (2:ℝ)^(auPrec p) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      have h3 : (1:ℝ) * 3 ≤ (2:ℝ)^(auPrec p) * Real.pi :=
        mul_le_mul hp2 (le_of_lt Real.pi_gt_three) (by norm_num) hPpos.le
      linarith
    linarith
  have haz0 : (0:ℤ) ≤ auZ p α t (N:ℤ) := by
    rw [auZ]
    apply Int.tdiv_nonneg
    · have : (0:ℤ) < auPi p := by exact_mod_cast hPi_pos
      exact mul_nonneg this.le (by exact_mod_cast Nat.zero_le N)
    · positivity
  set y : ℝ := Real.pi * (N:ℝ) / ((α:ℝ)^2 * (t:ℝ)^2) with hy
  set T : ℝ := (2:ℝ)^p * (1/(2*(α:ℝ))) * Real.exp (-y) with hT
  set az : ℤ := auZ p α t (N:ℤ) with haz
  set U : ℤ := auH p (-az) (auNstep p) with hU
  set D : ℤ := (2:ℤ)^(auPrec p - p) * (2*(α:ℤ)) with hD
  have hDpos : (0:ℤ) < D := by rw [hD]; positivity
  have hfloor : |((Int.tdiv U D : ℤ) : ℝ) - (U:ℝ)/(D:ℝ)| ≤ 1 :=
    Work.Fx.tdiv_abs_le_one U D hDpos
  have hDcast : (D:ℝ) = (2:ℝ)^(auPrec p - p) * (2*(α:ℝ)) := by rw [hD]; push_cast; ring
  have hpp : (2:ℝ)^(auPrec p - p) * (2:ℝ)^p = (2:ℝ)^(auPrec p) := by
    rw [← pow_add, Nat.sub_add_cancel (by simp [auPrec]; omega)]
  have hUfrac : (U:ℝ)/(D:ℝ) = ((2:ℝ)^p/(2*(α:ℝ))) * ((U:ℝ)/(2:ℝ)^(auPrec p)) := by
    rw [hDcast]
    have h1 : (2:ℝ)^(auPrec p - p) ≠ 0 := by positivity
    have h2 : (2*(α:ℝ)) ≠ 0 := by positivity
    have h3 : (2:ℝ)^(auPrec p) ≠ 0 := by positivity
    field_simp
    rw [mul_assoc, hpp]
  have hT' : T = ((2:ℝ)^p/(2*(α:ℝ))) * Real.exp (-y) := by rw [hT]; ring
  have hc0 : (0:ℝ) ≤ (2:ℝ)^p/(2*(α:ℝ)) := by positivity
  have htR00 : (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) = -((az:ℝ)/(2:ℝ)^(auPrec p)) := by
    push_cast; ring
  have htRabs : |((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)| ≤ (p:ℝ) + 10 := by
    rw [htR00, abs_neg, abs_div, abs_of_pos hPpos, abs_of_nonneg (by exact_mod_cast haz0)]
    rw [div_le_iff₀ hPpos]
    have hgR : (az:ℝ) ≤ ((p+10:ℕ):ℝ) * (2:ℝ)^(auPrec p) := by exact_mod_cast hg
    have hcast : ((p+10:ℕ):ℝ) = (p:ℝ) + 10 := by push_cast; ring
    rw [hcast] at hgR
    linarith
  have hAB : |(U:ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)|
      ≤ (2/(2:ℝ)^(auPrec p)) * Real.exp |((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)| := by
    have h := auH_err p (-az) (auNstep p) le_rfl
    rw [Nat.sub_self, ← hU] at h
    exact h
  have hBC : |Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)
      - Real.exp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p))| ≤ 1/(2:ℝ)^(2*p+160) := by
    have h := auTailExp p hp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) htRabs
    rw [Work.Fx.expRec.2.2.2.2]
    exact h
  have hexp_le : Real.exp |((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)| ≤ (2:ℝ)^(2*p+20) := by
    have h1 : Real.exp |((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)| ≤ Real.exp ((p:ℝ)+10) :=
      Real.exp_le_exp.mpr htRabs
    have h2 : Real.exp ((p:ℝ)+10) ≤ (2:ℝ)^(2*p+20) := by
      have he : Real.exp ((p:ℝ)+10) = Real.exp 1 ^ (p+10) := by
        rw [show (p:ℝ)+10 = ((p+10:ℕ):ℝ) by push_cast; ring]
        simpa using Real.exp_nat_mul (1:ℝ) (p+10)
      rw [he]
      have h4 : Real.exp 1 ≤ (2:ℝ)^2 := by
        have h3 := Real.exp_one_lt_three
        have h5 : (2:ℝ)^2 = 4 := by norm_num
        rw [h5]; linarith
      calc Real.exp 1 ^ (p+10) ≤ ((2:ℝ)^2)^(p+10) := pow_le_pow_left₀ (Real.exp_pos 1).le h4 _
        _ = (2:ℝ)^(2*p+20) := by rw [show 2*p+20 = 2*(p+10) by ring, ← pow_mul]
    linarith
  have hCD : |Real.exp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) - Real.exp (-y)| ≤ ((p:ℝ)+13)/(2:ℝ)^(auPrec p) := by
    have hazR : (0:ℝ) ≤ (az:ℝ) := by exact_mod_cast haz0
    have htRnonpos : ((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p) ≤ 0 := by
      rw [htR00]
      exact neg_nonpos.mpr (div_nonneg hazR hPpos.le)
    have hny : -y ≤ 0 := by
      have h : 0 ≤ y := by
        rw [hy]
        apply div_nonneg
        · exact mul_nonneg Real.pi_pos.le (Nat.cast_nonneg N)
        · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith
    have h3 := exp_abs_sub_le htRnonpos hny
    refine h3.trans ?_
    have hcl := (auZ_y_close p α t N hp hα ht hpi hg).1
    have h4 : (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) - (-y) = - (((az:ℝ)/(2:ℝ)^(auPrec p)) - y) := by
      rw [htR00]; ring
    rw [h4, abs_neg, haz, hy]
    exact hcl
  have htri : |(U:ℝ)/(2:ℝ)^(auPrec p) - Real.exp (-y)|
      ≤ |(U:ℝ)/(2:ℝ)^(auPrec p) - Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)|
        + |Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)
            - Real.exp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p))|
        + |Real.exp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) - Real.exp (-y)| := by
    have h1 := abs_sub_le ((U:ℝ)/(2:ℝ)^(auPrec p))
        (Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1)) (Real.exp (-y))
    have h2 := abs_sub_le (Work.Fx.pot (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)) 0 (auNstep p + 1))
        (Real.exp (((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p))) (Real.exp (-y))
    linarith
  have hAD : |(U:ℝ)/(2:ℝ)^(auPrec p) - Real.exp (-y)|
      ≤ (2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20) + 1/(2:ℝ)^(2*p+160) + ((p:ℝ)+13)/(2:ℝ)^(auPrec p) := by
    refine htri.trans ?_
    have h1 : (2/(2:ℝ)^(auPrec p)) * Real.exp |((-az : ℤ) : ℝ)/(2:ℝ)^(auPrec p)|
        ≤ (2/(2:ℝ)^(auPrec p)) * (2:ℝ)^(2*p+20) :=
      mul_le_mul_of_nonneg_left hexp_le (by positivity)
    linarith [hAB, hBC, hCD, h1]
  have hmain : |(U:ℝ)/(D:ℝ) - T| ≤ 1 := by
    rw [hUfrac, hT', ← mul_sub, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hAD hc0).trans (numcore p (α:ℝ) hαR)
  calc |((Int.tdiv U D : ℤ) : ℝ) - T|
      ≤ |((Int.tdiv U D : ℤ) : ℝ) - (U:ℝ)/(D:ℝ)| + |(U:ℝ)/(D:ℝ) - T| := abs_sub_le _ _ _
    _ ≤ 1 + 1 := add_le_add hfloor hmain
    _ = 2 := by norm_num

private lemma guard_case (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi| ≤ 1)
    (hg : ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) < auZ p α t (N:ℤ)) :
    (2:ℝ)^p * (1/(2*(α:ℝ))) * Real.exp (-(Real.pi*(N:ℝ)/((α:ℝ)^2*(t:ℝ)^2))) ≤ 2 := by
  have hαR : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
  set Y : ℝ := Real.pi*(N:ℝ)/((α:ℝ)^2*(t:ℝ)^2) with hY
  have hY9 : (p:ℝ)+9 ≤ Y := by rw [hY]; exact auZ_y_far p α t N hp hα ht hpi hg
  have h1 : Real.exp (-Y) ≤ Real.exp (-((p:ℝ)+9)) := Real.exp_le_exp.mpr (by linarith)
  have hpow : (2:ℝ)^(p+9) ≤ Real.exp ((p:ℝ)+9) := by
    have he : Real.exp ((p:ℝ)+9) = Real.exp 1 ^ (p+9) := by
      rw [show (p:ℝ)+9 = ((p+9:ℕ):ℝ) by push_cast; ring]
      simpa using Real.exp_nat_mul (1:ℝ) (p+9)
    rw [he]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (le_of_lt Real.exp_one_gt_two) _
  have h2 : Real.exp (-((p:ℝ)+9)) ≤ 1/(2:ℝ)^(p+9) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hYexp : Real.exp (-Y) ≤ 1/(2:ℝ)^(p+9) := h1.trans h2
  have hc4 : (2:ℝ)^p * (1/(2*(α:ℝ))) ≤ (2:ℝ)^p/4 := by
    have h : 1/(2*(α:ℝ)) ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    calc (2:ℝ)^p * (1/(2*(α:ℝ))) ≤ (2:ℝ)^p * (1/4) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (2:ℝ)^p/4 := by ring
  have hfinal : (2:ℝ)^p/4 * (1/(2:ℝ)^(p+9)) ≤ 2 := by
    have he : (2:ℝ)^p/4 * (1/(2:ℝ)^(p+9)) = (2:ℝ)^p/(2:ℝ)^(p+11) := by
      rw [show (2:ℝ)^(p+11) = (2:ℝ)^(p+9) * 4 by rw [show p+11 = p+9+2 by omega, pow_add]; norm_num]
      ring
    rw [he]
    have hle1 : (2:ℝ)^p/(2:ℝ)^(p+11) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  calc (2:ℝ)^p * (1/(2*(α:ℝ))) * Real.exp (-Y)
      ≤ ((2:ℝ)^p/4) * (1/(2:ℝ)^(p+9)) := by
        apply mul_le_mul hc4 hYexp (Real.exp_pos _).le (by positivity)
    _ ≤ 2 := hfinal

theorem auWtErr (p α t : ℕ) (N : ℕ) (hp : 100 ≤ p) (hα : 2 ≤ α) (ht : 1 ≤ t)
    (hpi : |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1) :
    |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) * Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2 := by
  rw [auWt]
  by_cases hg : auZ p α t (N:ℤ) ≤ ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p)
  · rw [if_pos hg]
    exact compute_case p α t N hp hα ht hpi hg
  · rw [if_neg hg]
    have hlt : ((p+10:ℕ):ℤ) * (2:ℤ)^(auPrec p) < auZ p α t (N:ℤ) := lt_of_not_ge hg
    have hαR : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
    have hg2 := guard_case p α t N hp hα ht hpi hlt
    have hTnn : 0 ≤ (2:ℝ)^p * (1/(2*(α:ℝ))) * Real.exp (-(Real.pi*(N:ℝ)/((α:ℝ)^2*(t:ℝ)^2))) := by
      apply mul_nonneg
      · apply mul_nonneg
        · exact pow_nonneg (by norm_num) p
        · exact div_nonneg zero_le_one (by linarith : (0:ℝ) ≤ 2*(α:ℝ))
      · exact (Real.exp_pos _).le
    simp only [Int.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg hTnn]
    exact hg2

end Work.Resample
