import Mathlib
import Submission.Work.Fx.ExpDefs
import Submission.Work.Fx.expRec
import Submission.Work.Fx.expStepErr
import Submission.Work.Fx.expTail
import Submission.Work.Fx.scaleCommon

/-!
# Helper facts for the assembly of `Work.Fx.expCplx`
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Fx

open HvdH

/-- Uniform bound on the size (`szl`) of every window occurring in the loop. -/
def scnt (p : ℕ) : ℕ := 20 * wprec p + 1000

namespace ExpAsm

open HvdH

/-! ## Elementary size and value facts -/

theorem isz_le_of_natAbs_le {z : ℤ} {k : ℕ} (h : z.natAbs ≤ 2 ^ k) : isz z ≤ k + 3 := by
  have h1 : z.natAbs < 2 ^ (k + 1) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
  have h2 : z.natAbs.size ≤ k + 1 := Nat.size_le.mpr h1
  simp only [isz]; omega

theorem isz_two_pow (k : ℕ) : isz ((2 : ℤ) ^ k) = k + 3 := by
  have h : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by rw [Int.natAbs_pow]; norm_num
  rw [isz, h, Nat.size_pow]

theorem exp32_le : Real.exp 32 ≤ (2 : ℝ) ^ 47 := by
  have h1 : Real.exp 32 = Real.exp 1 ^ 32 := by
    have h := Real.exp_nat_mul 1 32
    simpa using h
  rw [h1]
  calc Real.exp 1 ^ 32 ≤ (2.7182818286 : ℝ) ^ 32 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 32
    _ ≤ (2 : ℝ) ^ 47 := by norm_num

theorem normSq_XI (X Y : ℤ) :
    Complex.normSq (((X : ℂ) + (Y : ℂ) * Complex.I)) = (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 := by
  rw [Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem norm_zval_le (p : ℕ) (X Y : ℤ)
    (h : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) : ‖zval p X Y‖ ≤ 32 := by
  have h3 : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ^ 2 = (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 := by
    rw [Complex.sq_norm, normSq_XI]
  have h5 : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ^ 2 ≤ (32 * 2 ^ p) ^ 2 := by rw [h3]; exact h
  have h4 : ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ 32 * 2 ^ p := by
    calc ‖((X : ℂ) + (Y : ℂ) * Complex.I)‖
        = Real.sqrt (‖((X : ℂ) + (Y : ℂ) * Complex.I)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((32 * 2 ^ p) ^ 2) := Real.sqrt_le_sqrt h5
      _ = 32 * 2 ^ p := Real.sqrt_sq (by positivity)
  rw [zval, norm_div]
  have hden : ‖((2 : ℂ) ^ p)‖ = (2 : ℝ) ^ p := by simp
  rw [hden, div_le_iff₀ (by positivity)]
  linarith

theorem abs_le_of_sq_sum {X Y : ℤ} {b : ℝ} (h : (X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ b ^ 2)
    (hb : 0 ≤ b) : |(X : ℝ)| ≤ b ∧ |(Y : ℝ)| ≤ b := by
  have h1 : (X : ℝ) ^ 2 ≤ b ^ 2 := by nlinarith [sq_nonneg (Y : ℝ)]
  have h2 : (Y : ℝ) ^ 2 ≤ b ^ 2 := by nlinarith [sq_nonneg (X : ℝ)]
  have h3 : |b| = b := abs_of_nonneg hb
  exact ⟨(sq_le_sq.mp h1).trans (le_of_eq h3), (sq_le_sq.mp h2).trans (le_of_eq h3)⟩

theorem fact_coef_le (d k : ℕ) :
    (d.factorial : ℝ) / ((d + k).factorial : ℝ) ≤ (1 : ℝ) / (k.factorial : ℝ) := by
  have h : (d.factorial * k.factorial : ℕ) ≤ (d + k).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add d k)
  have h2 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h3 : (0 : ℝ) < ((d + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d + k)
  have h4 : ((d.factorial : ℝ) * (k.factorial : ℝ)) ≤ ((d + k).factorial : ℝ) := by
    rw [← Nat.cast_mul]; exact_mod_cast h
  rw [div_le_iff₀ h3, one_div, inv_mul_eq_div, le_div_iff₀ h2]
  linarith

theorem hval_norm_le (z : ℂ) (hz : ‖z‖ ≤ 32) (d i : ℕ) : ‖hval z d i‖ ≤ Real.exp 32 := by
  have h1 : ‖hval z d i‖ ≤ pot 32 0 (i + 1) := by
    rw [hval, pot]
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul, norm_pow, Complex.norm_div, Complex.norm_natCast, Complex.norm_natCast,
      Nat.factorial_zero, Nat.zero_add]
    have hz' : ‖z‖ ^ k ≤ 32 ^ k := pow_le_pow_left₀ (norm_nonneg _) hz k
    have hcoef : (d.factorial : ℝ) / ((d + k).factorial : ℝ) ≤ ((1 : ℕ) : ℝ) / (k.factorial : ℝ) := by
      simpa using fact_coef_le d k
    exact mul_le_mul hz' hcoef (by positivity) (by positivity)
  have h2 : pot 32 0 (i + 1) ≤ Real.exp 32 := expRec.2.2.1 32 (by norm_num) 0 (i + 1)
  linarith

/-! ## Parameter arithmetic -/

theorem le_wprec (p : ℕ) : p ≤ wprec p := by simp only [wprec]; omega

theorem d0_le_wprec (p : ℕ) : d0 p ≤ wprec p := by simp only [wprec, d0]; omega

theorem wprec_add (p : ℕ) : wprec p = p + d0 p := by simp only [wprec, d0]; omega

theorem size_ge (p : ℕ) (hp : 100 ≤ p) : 7 ≤ p.size := by
  by_contra h
  have h6 : p.size ≤ 6 := by omega
  have h7 := (Nat.size_le.mp h6 : p < 2 ^ 6)
  norm_num at h7
  omega

theorem d0_ge (p : ℕ) (hp : 100 ≤ p) : 91 ≤ d0 p := by
  have := size_ge p hp
  simp only [d0]; omega

theorem four_exp32_le (p : ℕ) (hp : 100 ≤ p) : 4 * Real.exp 32 ≤ (2 : ℝ) ^ (d0 p) := by
  have h1 : 4 * Real.exp 32 ≤ 4 * (2 : ℝ) ^ 47 := by linarith [exp32_le]
  have h2 : (4 : ℝ) * (2 : ℝ) ^ 47 = (2 : ℝ) ^ 49 := by norm_num
  have h3 : (49 : ℕ) ≤ d0 p := by have := d0_ge p hp; omega
  calc 4 * Real.exp 32 ≤ (2 : ℝ) ^ 49 := by rw [← h2]; linarith
    _ ≤ (2 : ℝ) ^ (d0 p) := pow_le_pow_right₀ (by norm_num) h3

theorem isz_X_le (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) : isz X ≤ p + 8 := by
  have h1 : X.natAbs < 2 ^ (p + 6) := by
    have h2 : ((X.natAbs : ℕ) : ℝ) = |(X : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h3 : ((X.natAbs : ℕ) : ℝ) < ((2 ^ (p + 6) : ℕ) : ℝ) := by
      rw [h2]; push_cast
      have h4 : (32 : ℝ) * 2 ^ p < 2 ^ (p + 6) := by
        rw [pow_add]
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) p]
      linarith
    exact_mod_cast h3
  have h4 : X.natAbs.size ≤ p + 6 := Nat.size_le.mpr h1
  simp only [isz]; omega

theorem isz_Zs_le (p : ℕ) {X : ℤ} (h : |(X : ℝ)| ≤ 32 * 2 ^ p) :
    isz (X * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := by
  have h1 : isz (X * (2 : ℤ) ^ (d0 p)) ≤ isz X + isz ((2 : ℤ) ^ (d0 p)) :=
    isz_mul_le X ((2 : ℤ) ^ (d0 p))
  have h2 : isz X ≤ p + 8 := isz_X_le p h
  have h3 : isz ((2 : ℤ) ^ (d0 p)) = d0 p + 3 := isz_two_pow (d0 p)
  have h4 : wprec p = p + d0 p := wprec_add p
  omega

theorem isz_d0_le (p : ℕ) : isz ((d0 p : ℕ) : ℤ) ≤ wprec p + 2 := by
  have h2 : isz ((d0 p : ℕ) : ℤ) = (d0 p).size + 2 := by
    simp only [isz, Int.natAbs_natCast]
  have h3 : (d0 p).size ≤ d0 p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := d0 p))
  have h4 : d0 p ≤ wprec p := d0_le_wprec p
  omega

theorem isz_dd_le' (p : ℕ) {dd : ℤ} {i : ℕ} (hdd : dd = ((wcnt p : ℕ) : ℤ) - (i : ℤ))
    (hi : i ≤ wcnt p) : isz dd ≤ wprec p + 10 := by
  have h1 : dd.natAbs ≤ wcnt p := by
    have h2 : (0 : ℤ) ≤ dd := by rw [hdd]; omega
    have h3 : dd ≤ ((wcnt p : ℕ) : ℤ) := by rw [hdd]; omega
    have h4 : ((dd.natAbs : ℕ) : ℤ) = dd := Int.natAbs_of_nonneg h2
    omega
  have h5 : (dd.natAbs : ℕ) < 2 ^ (p + 6) := by
    have h6 : wcnt p < 2 ^ (p + 6) := by
      simp only [wcnt]
      have h7 : 8 * (p + 1) ≤ 2 ^ (p + 4) := by
        have hp : p + 1 ≤ 2 ^ p := by
          have := Nat.lt_two_pow_self (n := p); omega
        calc 8 * (p + 1) ≤ 8 * 2 ^ p := Nat.mul_le_mul_left 8 hp
          _ = 2 ^ (p + 3) := by rw [pow_add]; ring
          _ ≤ 2 ^ (p + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h8 : (2:ℕ) ^ (p + 4) < 2 ^ (p + 6) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    omega
  have h6 : dd.natAbs.size ≤ p + 6 := Nat.size_le.mpr h5
  have h7 : p ≤ wprec p := le_wprec p
  simp only [isz]; omega

/-! ## The coordinate bound derived from the error invariant -/

theorem coord_single (P : ℕ) {Qre Qim : ℤ}
    (hW : ‖((Qre:ℂ) + (Qim:ℂ)*Complex.I)/(2:ℂ)^P‖ ≤ (2:ℝ)^48) :
    isz Qre ≤ P + 52 ∧ isz Qim ≤ P + 52 := by
  have hden : (2:ℂ)^P = (((2:ℝ)^P : ℝ) : ℂ) := by push_cast; ring
  have hpos : (0:ℝ) < (2:ℝ)^P := by positivity
  have hre : ((((Qre:ℂ) + (Qim:ℂ)*Complex.I) / (2:ℂ)^P).re) = (Qre:ℝ) / (2:ℝ)^P := by
    have hc : ((Qre:ℂ).re) = (Qre:ℝ) := by simp
    have hd : ((Qim:ℂ).im) = 0 := by simp
    rw [hden, Complex.div_ofReal]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, hc, hd]
    ring
  have him : ((((Qre:ℂ) + (Qim:ℂ)*Complex.I) / (2:ℂ)^P).im) = (Qim:ℝ) / (2:ℝ)^P := by
    have hc : ((Qre:ℂ).im) = 0 := by simp
    have hd : ((Qim:ℂ).re) = (Qim:ℝ) := by simp
    rw [hden, Complex.div_ofReal]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, mul_one, hc, hd]
    ring
  have bound_of : ∀ (c : ℤ), |(c:ℝ)| / (2:ℝ)^P ≤ (2:ℝ)^48 → c.natAbs ≤ 2^(P+48) := by
    intro c h1
    have h2' : |(c:ℝ)| ≤ (2:ℝ)^(P+48) := by
      have h2'' := (div_le_iff₀ hpos).mp h1
      rw [← pow_add] at h2''
      rwa [show (48 + P) = (P + 48) from by omega] at h2''
    have h3 : ((c.natAbs : ℕ) : ℝ) ≤ ((2 ^ (P+48) : ℕ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      exact h2'
    exact_mod_cast h3
  have h1re : |(Qre:ℝ)| / (2:ℝ)^P ≤ (2:ℝ)^48 := by
    have := Complex.abs_re_le_norm (((Qre:ℂ) + (Qim:ℂ)*Complex.I) / (2:ℂ)^P)
    rw [hre, abs_div, abs_of_pos hpos] at this
    linarith
  have h1im : |(Qim:ℝ)| / (2:ℝ)^P ≤ (2:ℝ)^48 := by
    have := Complex.abs_im_le_norm (((Qre:ℂ) + (Qim:ℂ)*Complex.I) / (2:ℂ)^P)
    rw [him, abs_div, abs_of_pos hpos] at this
    linarith
  have h4 : isz Qre ≤ P + 48 + 3 := isz_le_of_natAbs_le (bound_of Qre h1re)
  have h5 : isz Qim ≤ P + 48 + 3 := isz_le_of_natAbs_le (bound_of Qim h1im)
  omega

theorem coord_bound (p : ℕ) (X Y : ℤ) (hp : 100 ≤ p) (hz : ‖zval p X Y‖ ≤ 32) (i : ℕ)
    {Qre Qim : ℤ}
    (herr : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
        hval (zval p X Y) (wcnt p - i) i‖ ≤
      4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - i) i) :
    isz Qre ≤ wprec p + 52 ∧ isz Qim ≤ wprec p + 52 := by
  have hvalb : ‖hval (zval p X Y) (wcnt p - i) i‖ ≤ Real.exp 32 := hval_norm_le _ hz _ _
  have hpot : pot 32 (wcnt p - i) i ≤ Real.exp 32 := expRec.2.2.1 32 (by norm_num) _ _
  have h4e : 4 * Real.exp 32 ≤ (2 : ℝ) ^ (d0 p) := four_exp32_le p hp
  have hsplit : (2 : ℝ) ^ (wprec p) = (2 : ℝ) ^ p * (2 : ℝ) ^ (d0 p) := by
    rw [wprec_add, pow_add]
  have hkey : 4 * Real.exp 32 ≤ (2 : ℝ) ^ (wprec p) := by
    rw [hsplit]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ p := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (d0 p) := by positivity
    nlinarith
  have herr1 : 4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - i) i ≤ 1 := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (wprec p) := by positivity
    rw [div_mul_eq_mul_div, div_le_one hpos]
    linarith
  have hW : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)‖ ≤ (2 : ℝ) ^ 48 := by
    have hsum : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)‖ ≤
        ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
          hval (zval p X Y) (wcnt p - i) i‖ + ‖hval (zval p X Y) (wcnt p - i) i‖ := by
      have h := norm_add_le (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
        hval (zval p X Y) (wcnt p - i) i) (hval (zval p X Y) (wcnt p - i) i)
      simpa using h
    have h2 : (2 : ℝ) ^ 48 = 2 * 2 ^ 47 := by norm_num
    linarith [exp32_le]
  exact coord_single (wprec p) hW

theorem hsplit_pow (p : ℕ) : (2:ℝ)^(wprec p) = (2:ℝ)^p * (2:ℝ)^(d0 p) := by
  rw [wprec_add, pow_add]

/-! ## The loop invariant and the error recurrence -/

/-- The Horner loop invariant. -/
noncomputable def Inv (p : ℕ) (X Y : ℤ) (i : ℕ) (acc : List Val) : Prop :=
  ∃ (rest : List Val) (Qre Qim dd : ℤ),
    acc = [Val.int Qre, Val.int Qim, Val.int dd, Val.int (X * (2 : ℤ) ^ (d0 p)),
           Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)),
           Val.int ((d0 p : ℕ))] ++ rest ∧
    dd = ((wcnt p : ℕ) : ℤ) - (i : ℤ) ∧ i ≤ wcnt p ∧
    ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
        hval (zval p X Y) (wcnt p - i) i‖ ≤
      4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - i) i

theorem zval_shift (p : ℕ) (X Y : ℤ) :
    (((X * (2 : ℤ) ^ (d0 p) : ℤ) : ℂ) + ((Y * (2 : ℤ) ^ (d0 p) : ℤ) : ℂ) * Complex.I) /
        ((2 : ℂ) ^ (wprec p)) = zval p X Y := by
  have h : (2 : ℂ) ^ (wprec p) = (2 : ℂ) ^ p * (2 : ℂ) ^ (d0 p) := by
    rw [show wprec p = p + d0 p by simp only [wprec, d0]; omega, pow_add]
  rw [h, zval, div_eq_iff (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))]
  push_cast
  field_simp

theorem err_step (p : ℕ) (X Y : ℤ) {i : ℕ} (hi : i < wcnt p) {Qre Qim dd : ℤ}
    (hdd : dd = ((wcnt p : ℕ) : ℤ) - (i : ℤ)) (hdd1 : 1 ≤ dd)
    (hz : ‖zval p X Y‖ ≤ 32)
    (herr : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
        hval (zval p X Y) (wcnt p - i) i‖ ≤ 4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - i) i) :
    ‖(((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
        (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (wprec p) -
      hval (zval p X Y) (wcnt p - (i + 1)) (i + 1)‖ ≤
      4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - (i + 1)) (i + 1) := by
  set d : ℕ := wcnt p - i with hd
  have hd1 : 1 ≤ d := by simp only [hd]; omega
  have hdim : d - 1 = wcnt p - (i + 1) := by simp only [hd]; omega
  have hdc : ((d : ℕ) : ℂ) = (dd : ℂ) := by
    have hh : (d : ℤ) = dd := by simp only [hd, hdd]; omega
    rw [← hh]; push_cast; ring
  have hstep := expStepErr (wprec p) (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p))
    ((2 : ℤ) ^ (wprec p)) Qre Qim dd rfl hdd1
  rw [← hdc] at hstep
  simp only [zval_shift] at hstep
  have hr1 : hval (zval p X Y) (d - 1) (i + 1) =
      1 + (zval p X Y / (d : ℂ)) * hval (zval p X Y) d i := expRec.1 (zval p X Y) d i hd1
  have hr2 : pot 32 (d - 1) (i + 1) = 1 + (32 / (d : ℝ)) * pot 32 d i :=
    expRec.2.1 32 d i hd1 (by norm_num)
  have hnorm : ‖(zval p X Y / (d : ℂ)) *
      ((((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) - hval (zval p X Y) d i)‖
      ≤ (32 / (d : ℝ)) * (4 / (2 : ℝ) ^ (wprec p) * pot 32 d i) := by
    have hdn : ‖(d : ℂ)‖ = (d : ℝ) := by simp
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    rw [norm_mul, norm_div, hdn]
    have h1 : ‖zval p X Y‖ / (d : ℝ) ≤ 32 / (d : ℝ) :=
      div_le_div₀ (by norm_num : (0:ℝ) ≤ 32) hz hdpos le_rfl
    have h2 : (0 : ℝ) ≤ 32 / (d : ℝ) := by positivity
    exact mul_le_mul h1 herr (norm_nonneg _) h2
  have h1 : ‖(((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
      (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
      / (2 : ℂ) ^ (wprec p) -
      (1 + (zval p X Y / (d : ℂ)) * (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)))‖ ≤
      4 / (2 : ℝ) ^ (wprec p) := by simpa using hstep
  have hdis : (((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
      (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
      / (2 : ℂ) ^ (wprec p) - hval (zval p X Y) (d - 1) (i + 1) =
      ((((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
        (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (wprec p) -
        (1 + (zval p X Y / (d : ℂ)) * (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)))) +
      (zval p X Y / (d : ℂ)) *
        ((((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) - hval (zval p X Y) d i) := by
    rw [hr1]; ring
  calc ‖(((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
        (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (wprec p) - hval (zval p X Y) (wcnt p - (i + 1)) (i + 1)‖
      = ‖(((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
        (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (wprec p) -
        (1 + (zval p X Y / (d : ℂ)) * (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)))
        + (zval p X Y / (d : ℂ)) *
          ((((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) - hval (zval p X Y) d i)‖ := by
        rw [← hdim, hdis]
    _ ≤ ‖(((stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ) : ℂ) +
        (((stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd : ℤ)) : ℂ) * Complex.I)
        / (2 : ℂ) ^ (wprec p) -
        (1 + (zval p X Y / (d : ℂ)) * (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)))‖ +
        ‖(zval p X Y / (d : ℂ)) * ((((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) -
          hval (zval p X Y) d i)‖ := norm_add_le _ _
    _ ≤ 4 / (2 : ℝ) ^ (wprec p) +
        ‖(zval p X Y / (d : ℂ)) * ((((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) -
          hval (zval p X Y) d i)‖ := by linarith
    _ ≤ 4 / (2 : ℝ) ^ (wprec p) + (32 / (d : ℝ)) * (4 / (2 : ℝ) ^ (wprec p) * pot 32 d i) := by
        linarith
    _ = 4 / (2 : ℝ) ^ (wprec p) * (1 + (32 / (d : ℝ)) * pot 32 d i) := by ring
    _ = 4 / (2 : ℝ) ^ (wprec p) * pot 32 (wcnt p - (i + 1)) (i + 1) := by rw [← hdim, ← hr2]

/-! ## Window size bounds -/

theorem szl_pre_le (p : ℕ) (X Y : ℤ) (Qre Qim dd : ℤ)
    (hX : |(X : ℝ)| ≤ 32 * 2 ^ p) (hY : |(Y : ℝ)| ≤ 32 * 2 ^ p)
    (hqr : isz Qre ≤ wprec p + 52) (hqi : isz Qim ≤ wprec p + 52) (hdd : isz dd ≤ wprec p + 10) :
    szl [Val.int 1, Val.int Qre, Val.int Qim, Val.int dd, Val.int (X * (2 : ℤ) ^ (d0 p)),
        Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)),
        Val.int ((d0 p : ℕ))] ≤ scnt p := by
  have h1 : isz (X * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hX
  have h2 : isz (Y * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hY
  have h3 : isz ((2 : ℤ) ^ (wprec p)) = wprec p + 3 := isz_two_pow (wprec p)
  have h4 : isz ((d0 p : ℕ) : ℤ) ≤ wprec p + 2 := isz_d0_le p
  have h5 : isz (1 : ℤ) = 3 := by simp [isz]
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, scnt]
  omega

theorem szl_mid_le (p : ℕ) (X Y : ℤ) (Qre Qim dd : ℤ)
    (hX : |(X : ℝ)| ≤ 32 * 2 ^ p) (hY : |(Y : ℝ)| ≤ 32 * 2 ^ p)
    (hqr : isz Qre ≤ wprec p + 52) (hqi : isz Qim ≤ wprec p + 52) (hdd : isz dd ≤ wprec p + 10) :
    szl [Val.int (X * (2 : ℤ) ^ (d0 p) * Qre - Y * (2 : ℤ) ^ (d0 p) * Qim),
        Val.int (X * (2 : ℤ) ^ (d0 p) * Qim + Y * (2 : ℤ) ^ (d0 p) * Qre), Val.int dd,
        Val.int (X * (2 : ℤ) ^ (d0 p)), Val.int (Y * (2 : ℤ) ^ (d0 p)),
        Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))] ≤ scnt p := by
  have h1 : isz (X * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hX
  have h2 : isz (Y * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hY
  have h3 : isz ((2 : ℤ) ^ (wprec p)) = wprec p + 3 := isz_two_pow (wprec p)
  have h4 : isz ((d0 p : ℕ) : ℤ) ≤ wprec p + 2 := isz_d0_le p
  have h5 : isz (X * (2 : ℤ) ^ (d0 p) * Qre - Y * (2 : ℤ) ^ (d0 p) * Qim) ≤ 2 * wprec p + 64 := by
    have ha : isz (X * (2 : ℤ) ^ (d0 p) * Qre) ≤ isz (X * (2 : ℤ) ^ (d0 p)) + isz Qre := isz_mul_le _ _
    have hb : isz (Y * (2 : ℤ) ^ (d0 p) * Qim) ≤ isz (Y * (2 : ℤ) ^ (d0 p)) + isz Qim := isz_mul_le _ _
    have hc := isz_sub_le (X * (2 : ℤ) ^ (d0 p) * Qre) (Y * (2 : ℤ) ^ (d0 p) * Qim)
    rcases le_total (isz (X * (2 : ℤ) ^ (d0 p) * Qre)) (isz (Y * (2 : ℤ) ^ (d0 p) * Qim)) with h | h
    · rw [max_eq_right h] at hc; omega
    · rw [max_eq_left h] at hc; omega
  have h6 : isz (X * (2 : ℤ) ^ (d0 p) * Qim + Y * (2 : ℤ) ^ (d0 p) * Qre) ≤ 2 * wprec p + 64 := by
    have ha : isz (Y * (2 : ℤ) ^ (d0 p) * Qre) ≤ isz (Y * (2 : ℤ) ^ (d0 p)) + isz Qre := isz_mul_le _ _
    have hb : isz (X * (2 : ℤ) ^ (d0 p) * Qim) ≤ isz (X * (2 : ℤ) ^ (d0 p)) + isz Qim := isz_mul_le _ _
    have hc := isz_add_le (X * (2 : ℤ) ^ (d0 p) * Qim) (Y * (2 : ℤ) ^ (d0 p) * Qre)
    rcases le_total (isz (X * (2 : ℤ) ^ (d0 p) * Qim)) (isz (Y * (2 : ℤ) ^ (d0 p) * Qre)) with h | h
    · rw [max_eq_right h] at hc; omega
    · rw [max_eq_left h] at hc; omega
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, scnt]
  omega

theorem szl_ep_le (p : ℕ) (X Y : ℤ) (Qre Qim : ℤ)
    (hX : |(X : ℝ)| ≤ 32 * 2 ^ p) (hY : |(Y : ℝ)| ≤ 32 * 2 ^ p)
    (hqr : isz Qre ≤ wprec p + 52) (hqi : isz Qim ≤ wprec p + 52) :
    szl [Val.int Qre, Val.int Qim, Val.int 0, Val.int (X * (2 : ℤ) ^ (d0 p)),
        Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)),
        Val.int ((d0 p : ℕ))] ≤ scnt p := by
  have h1 : isz (X * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hX
  have h2 : isz (Y * (2 : ℤ) ^ (d0 p)) ≤ wprec p + 11 := isz_Zs_le p hY
  have h3 : isz ((2 : ℤ) ^ (wprec p)) = wprec p + 3 := isz_two_pow (wprec p)
  have h4 : isz ((d0 p : ℕ) : ℤ) ≤ wprec p + 2 := isz_d0_le p
  have h5 : isz (0 : ℤ) = 2 := by simp [isz]
  simp only [szl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, vsz_int, scnt]
  omega

/-- Cost absorption. -/
theorem cost_absorb {S KA KB A B : ℕ} (hA : A ≤ S) (hB : B ≤ S) :
    KA * (A + 1) ^ KA + KB * (B + 1) ^ KB ≤ (KA + KB) * (S + 1) ^ (KA + KB) := by
  have h1 : (A + 1) ^ KA ≤ (S + 1) ^ (KA + KB) :=
    le_trans (Nat.pow_le_pow_left (by omega) KA)
      (Nat.pow_le_pow_right (by omega : 1 ≤ S + 1) (by omega))
  have h2 : (B + 1) ^ KB ≤ (S + 1) ^ (KA + KB) :=
    le_trans (Nat.pow_le_pow_left (by omega) KB)
      (Nat.pow_le_pow_right (by omega : 1 ≤ S + 1) (by omega))
  calc KA * (A + 1) ^ KA + KB * (B + 1) ^ KB
      ≤ KA * (S + 1) ^ (KA + KB) + KB * (S + 1) ^ (KA + KB) :=
        add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (KA + KB) * (S + 1) ^ (KA + KB) := by ring

/-! ## Cost arithmetic -/

/-- Per-iteration cost bound of the Horner step. -/
def cc (p KA KB : ℕ) : ℕ := (KA + KB) * (scnt p + 1) ^ (KA + KB)

/-- Final polynomial constant. -/
def Cst (Kpre KA KB Kep Kf : ℕ) : ℕ :=
  100 + 2 * Kpre + 4 * (KA + KB) + 4 * Kep + 4 * Kf + 20 * (KA + KB)

theorem le_pow_self (p n : ℕ) (hp : 1 ≤ p) : n ≤ (p + 1) ^ n := by
  have h1 : n ≤ 2 ^ n := le_of_lt (Nat.lt_two_pow_self (n := n))
  have h2 : (2:ℕ) ^ n ≤ (p + 1) ^ n := Nat.pow_le_pow_left (by omega : (2:ℕ) ≤ p + 1) n
  exact le_trans h1 h2

theorem wcnt_le (p : ℕ) (hp : 7 ≤ p) : wcnt p ≤ (p + 1) ^ 2 := by
  have h : 8 ≤ p + 1 := by omega
  calc wcnt p = 8 * (p + 1) := rfl
    _ ≤ (p + 1) * (p + 1) := Nat.mul_le_mul_right _ h
    _ = (p + 1) ^ 2 := by ring

theorem scnt_le (p : ℕ) (hp : 100 ≤ p) : scnt p + 1 ≤ (p + 1) ^ 3 := by
  have hps : p.size ≤ p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have h1 : scnt p + 1 ≤ 80 * p + 2401 := by simp only [scnt, wprec]; omega
  have h2 : 80 * p + 2401 ≤ (p + 1) ^ 3 := by
    have h3 : (p + 1) ^ 3 = p ^ 3 + 3 * p ^ 2 + 3 * p + 1 := by ring
    rw [h3]
    have hp' : (100 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    have hsq : (0 : ℤ) ≤ (p : ℤ) ^ 2 := sq_nonneg _
    have hsq3 : (0 : ℤ) ≤ (p : ℤ) ^ 3 := by positivity
    have : (0:ℤ) ≤ (p:ℤ) := by linarith
    nlinarith
  omega

theorem four_mul_le (p Kf : ℕ) (hp : 1 ≤ p) : 4 * Kf ≤ (p + 1) ^ (Kf + 2) := by
  have h1 : Kf ≤ 2 ^ Kf := le_of_lt (Nat.lt_two_pow_self (n := Kf))
  have h2 : 4 * Kf ≤ 2 ^ (Kf + 2) := by
    have h3 : (2:ℕ) ^ (Kf + 2) = 4 * 2 ^ Kf := by rw [pow_add]; ring
    rw [h3]; exact Nat.mul_le_mul_left 4 h1
  have h4 : (2:ℕ) ^ (Kf + 2) ≤ (p + 1) ^ (Kf + 2) :=
    Nat.pow_le_pow_left (by omega : (2:ℕ) ≤ p + 1) (Kf + 2)
  exact le_trans h2 h4

theorem cc_le (p KA KB : ℕ) (hp : 100 ≤ p) : cc p KA KB ≤ (p + 1) ^ (4 * (KA + KB)) := by
  have h1 : scnt p + 1 ≤ (p + 1) ^ 3 := scnt_le p hp
  have h2 : (scnt p + 1) ^ (KA + KB) ≤ ((p + 1) ^ 3) ^ (KA + KB) :=
    Nat.pow_le_pow_left h1 (KA + KB)
  have h3 : ((p + 1) ^ 3) ^ (KA + KB) = (p + 1) ^ (3 * (KA + KB)) := by rw [pow_mul]
  have h4 : KA + KB ≤ (p + 1) ^ (KA + KB) := le_pow_self p (KA + KB) (by omega)
  have h5 : (p + 1) ^ (KA + KB) * (p + 1) ^ (3 * (KA + KB)) = (p + 1) ^ ((KA + KB) + 3 * (KA + KB)) :=
    (pow_add _ _ _).symm
  have h6 : (KA + KB) + 3 * (KA + KB) = 4 * (KA + KB) := by ring
  simp only [cc]
  calc (KA + KB) * (scnt p + 1) ^ (KA + KB)
      ≤ (p + 1) ^ (KA + KB) * (p + 1) ^ (3 * (KA + KB)) :=
        Nat.mul_le_mul h4 (le_trans h2 (le_of_eq h3))
    _ = (p + 1) ^ ((KA + KB) + 3 * (KA + KB)) := h5
    _ = (p + 1) ^ (4 * (KA + KB)) := by rw [h6]

theorem cost_total (p n1 n2 n3 Kpre KA KB Kep Kf : ℕ) (hp : 100 ≤ p)
    (h1 : n1 ≤ Kpre * (p + 1) ^ Kpre)
    (h2 : n2 ≤ wcnt p * (cc p KA KB + Kf * 4) + Kf)
    (h3 : n3 ≤ Kep * (scnt p + 1) ^ Kep) :
    n1 + n2 + n3 ≤ Cst Kpre KA KB Kep Kf * (p + 1) ^ (Cst Kpre KA KB Kep Kf) := by
  set C : ℕ := Cst Kpre KA KB Kep Kf with hC
  have hC1 : 2 * Kpre ≤ C := by simp only [hC, Cst]; omega
  have hC2 : 4 * (KA + KB) + 2 + 2 + Kf ≤ C := by simp only [hC, Cst]; omega
  have hC3 : 4 * Kep ≤ C := by simp only [hC, Cst]; omega
  have hC4 : Kf ≤ C := by simp only [hC, Cst]; omega
  have hC5 : 5 ≤ C := by simp only [hC, Cst]; omega
  have hb1 : Kpre * (p + 1) ^ Kpre ≤ (p + 1) ^ C := by
    have hle : Kpre ≤ (p + 1) ^ Kpre := le_pow_self p Kpre (by omega)
    calc Kpre * (p + 1) ^ Kpre ≤ (p + 1) ^ Kpre * (p + 1) ^ Kpre := Nat.mul_le_mul_right _ hle
      _ = (p + 1) ^ (2 * Kpre) := by rw [← pow_add]; ring_nf
      _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) hC1
  have hb2 : wcnt p * (cc p KA KB + Kf * 4) + Kf ≤ 3 * (p + 1) ^ C := by
    have hw : wcnt p ≤ (p + 1) ^ 2 := wcnt_le p (by omega)
    have hcc : cc p KA KB ≤ (p + 1) ^ (4 * (KA + KB)) := cc_le p KA KB hp
    have h4k : Kf * 4 ≤ (p + 1) ^ (Kf + 2) := by linarith [four_mul_le p Kf (by omega)]
    have hkf : Kf ≤ (p + 1) ^ Kf := le_pow_self p Kf (by omega)
    have e1 : (p + 1) ^ 2 * cc p KA KB ≤ (p + 1) ^ C := by
      calc (p + 1) ^ 2 * cc p KA KB ≤ (p + 1) ^ 2 * (p + 1) ^ (4 * (KA + KB)) :=
            Nat.mul_le_mul_left _ hcc
        _ = (p + 1) ^ (2 + 4 * (KA + KB)) := by rw [← pow_add]
        _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (p + 1) ^ 2 * (Kf * 4) ≤ (p + 1) ^ C := by
      calc (p + 1) ^ 2 * (Kf * 4) ≤ (p + 1) ^ 2 * (p + 1) ^ (Kf + 2) :=
            Nat.mul_le_mul_left _ h4k
        _ = (p + 1) ^ (2 + (Kf + 2)) := by rw [← pow_add]
        _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) (by omega)
    have e3 : Kf ≤ (p + 1) ^ C := le_trans hkf (Nat.pow_le_pow_right (by omega) hC4)
    have hmul : wcnt p * (cc p KA KB + Kf * 4) = wcnt p * cc p KA KB + wcnt p * (Kf * 4) := by ring
    rw [hmul]
    have hw1 : wcnt p * cc p KA KB ≤ (p + 1) ^ C :=
      le_trans (Nat.mul_le_mul hw le_rfl) e1
    have hw2 : wcnt p * (Kf * 4) ≤ (p + 1) ^ C :=
      le_trans (Nat.mul_le_mul hw le_rfl) e2
    linarith
  have hb3 : Kep * (scnt p + 1) ^ Kep ≤ (p + 1) ^ C := by
    have hle : Kep ≤ (p + 1) ^ Kep := le_pow_self p Kep (by omega)
    have hsc : (scnt p + 1) ^ Kep ≤ (p + 1) ^ (3 * Kep) := by
      calc (scnt p + 1) ^ Kep ≤ ((p + 1) ^ 3) ^ Kep := Nat.pow_le_pow_left (scnt_le p hp) Kep
        _ = (p + 1) ^ (3 * Kep) := by rw [pow_mul]
    calc Kep * (scnt p + 1) ^ Kep ≤ (p + 1) ^ Kep * (p + 1) ^ (3 * Kep) := Nat.mul_le_mul hle hsc
      _ = (p + 1) ^ (Kep + 3 * Kep) := by rw [← pow_add]
      _ = (p + 1) ^ (4 * Kep) := by ring_nf
      _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) hC3
  calc n1 + n2 + n3 ≤ (p + 1) ^ C + 3 * (p + 1) ^ C + (p + 1) ^ C := by linarith
    _ = 5 * (p + 1) ^ C := by ring
    _ ≤ C * (p + 1) ^ C := Nat.mul_le_mul_right _ hC5
    _ = Cst Kpre KA KB Kep Kf * (p + 1) ^ (Cst Kpre KA KB Kep Kf) := by rw [hC]

/-! ## The final rounding lemma (paper's rounding map) -/

theorem expRound' (p d0 : ℕ) (A B : ℤ) :
    ‖((((Int.tdiv A ((2 : ℤ) ^ d0) : ℤ)) : ℂ) + ((Int.tdiv B ((2 : ℤ) ^ d0) : ℤ) : ℂ) * Complex.I)
        / 2 ^ p
      - (((A : ℂ) + (B : ℂ) * Complex.I) / 2 ^ (p + d0))‖ ≤ 2 / (2 : ℝ) ^ p := by
  set q : ℤ := (2 : ℤ) ^ d0 with hq
  have hqpos : (0 : ℤ) < q := by rw [hq]; positivity
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hqC : (((q : ℤ)) : ℂ) ≠ 0 := by
    have h : (((q : ℤ)) : ℂ) = (((q : ℝ)) : ℂ) := by push_cast; ring
    rw [h]; exact_mod_cast (ne_of_gt hqR)
  have hA := tdiv_sub_div_lt_one A hqpos
  have hB := tdiv_sub_div_lt_one B hqpos
  have hcmp : (2 : ℂ) ^ (p + d0) = (2 : ℂ) ^ p * ((q : ℤ) : ℂ) := by
    rw [hq, pow_add]; push_cast; ring
  rw [hcmp]
  rw [show (((A : ℂ) + (B : ℂ) * Complex.I) / ((2 : ℂ) ^ p * ((q : ℤ) : ℂ)))
      = (((A : ℂ) + (B : ℂ) * Complex.I) / ((q : ℤ) : ℂ)) / (2 : ℂ) ^ p by
        rw [← div_div]
        ring_nf]
  rw [← sub_div]
  rw [norm_div]
  have hnum : (((Int.tdiv A q : ℤ)) : ℂ) + (((Int.tdiv B q : ℤ)) : ℂ) * Complex.I -
      ((A : ℂ) + (B : ℂ) * Complex.I) / ((q : ℤ) : ℂ)
      = (((((Int.tdiv A q : ℤ) : ℝ) - (A : ℝ)/q : ℝ) : ℂ) +
         ((((Int.tdiv B q : ℤ) : ℝ) - (B : ℝ)/q : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [hnum]
  have hle := Complex.norm_le_abs_re_add_abs_im
    (((((Int.tdiv A q : ℤ) : ℝ) - (A : ℝ)/q : ℝ) : ℂ) +
     ((((Int.tdiv B q : ℤ) : ℝ) - (B : ℝ)/q : ℝ) : ℂ) * Complex.I)
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    zero_mul, zero_add] at hle
  have hden : ‖((2 : ℂ) ^ p)‖ = (2 : ℝ) ^ p := by simp
  have hpos2 : (0 : ℝ) < ‖((2 : ℂ) ^ p)‖ := by rw [hden]; positivity
  have hpos3 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  rw [div_le_iff₀ hpos2, hden,
    div_mul_cancel₀ (2 : ℝ) (ne_of_gt hpos3)]
  linarith

/-! ## Window definitions and the final error combination -/

/-- The 8-value window on which one Horner step acts (dummy `1` on top). -/
def preWin (p : ℕ) (X Y Qre Qim dd : ℤ) : List Val :=
  [Val.int 1, Val.int Qre, Val.int Qim, Val.int dd, Val.int (X * (2 : ℤ) ^ (d0 p)),
   Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))]

/-- The 7-value window between the two halves of a Horner step. -/
def midWin (p : ℕ) (X Y Qre Qim dd : ℤ) : List Val :=
  [Val.int (X * (2 : ℤ) ^ (d0 p) * Qre - Y * (2 : ℤ) ^ (d0 p) * Qim),
   Val.int (X * (2 : ℤ) ^ (d0 p) * Qim + Y * (2 : ℤ) ^ (d0 p) * Qre), Val.int dd,
   Val.int (X * (2 : ℤ) ^ (d0 p)), Val.int (Y * (2 : ℤ) ^ (d0 p)),
   Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))]

/-- The window after a Horner step. -/
def postWin (p : ℕ) (X Y Qre Qim dd : ℤ) : List Val :=
  [Val.int (stepQre (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd),
   Val.int (stepQim (X * (2 : ℤ) ^ (d0 p)) (Y * (2 : ℤ) ^ (d0 p)) ((2 : ℤ) ^ (wprec p)) Qre Qim dd),
   Val.int (dd - 1), Val.int (X * (2 : ℤ) ^ (d0 p)), Val.int (Y * (2 : ℤ) ^ (d0 p)),
   Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))]

/-- The window on which the epilogue acts (after `wcnt p` steps, `dd = 0`). -/
def epWin (p : ℕ) (X Y Qre Qim : ℤ) : List Val :=
  [Val.int Qre, Val.int Qim, Val.int 0, Val.int (X * (2 : ℤ) ^ (d0 p)),
   Val.int (Y * (2 : ℤ) ^ (d0 p)), Val.int ((2 : ℤ) ^ (wprec p)), Val.int ((d0 p : ℕ))]

theorem vsz_int_one : vsz (Val.int (1 : ℤ)) = 3 := by
  rw [vsz_int]; simp [isz]

theorem getD_replicate_nil {i n : ℕ} (h : i < n) :
    (List.replicate n (Val.int (1 : ℤ))).getD i Val.nil = Val.int 1 := by
  induction n generalizing i with
  | zero => simp at h
  | succ n ih =>
    cases i with
    | zero => simp
    | succ j => simp only [List.replicate_succ, List.getD_cons_succ]; exact ih (by omega)

/-- The final error combination: rounding down to precision `p`, the invariant's error at the end
of the loop, and the Taylor tail. -/
theorem final_bound (p : ℕ) (hp : 100 ≤ p) (z : ℂ) (hz : ‖z‖ ≤ 32) (U V Qre Qim : ℤ)
    (hU : U = Int.tdiv Qre ((2 : ℤ) ^ (d0 p))) (hV : V = Int.tdiv Qim ((2 : ℤ) ^ (d0 p)))
    (herr : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - hval z 0 (wcnt p)‖ ≤
      4 / (2 : ℝ) ^ (wprec p) * pot 32 0 (wcnt p)) :
    ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p - Complex.exp z‖ ≤ 4 / (2 : ℝ) ^ p := by
  have h1 : ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
      ((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)‖ ≤ 2 / (2 : ℝ) ^ p := by
    have h := expRound' p (d0 p) Qre Qim
    simpa [hU, hV, wprec_add p] using h
  have h2 : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - hval z 0 (wcnt p)‖ ≤
      1 / (2 : ℝ) ^ p := by
    have hpot : pot 32 0 (wcnt p) ≤ Real.exp 32 := expRec.2.2.1 32 (by norm_num) 0 (wcnt p)
    have h4e : 4 * Real.exp 32 ≤ (2 : ℝ) ^ (d0 p) := four_exp32_le p hp
    have hpos1 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
    have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (d0 p) := by positivity
    have hmono : 4 / (2 : ℝ) ^ (wprec p) * pot 32 0 (wcnt p) ≤ 4 / (2 : ℝ) ^ (wprec p) * Real.exp 32 := by
      have : (0 : ℝ) ≤ 4 / (2 : ℝ) ^ (wprec p) := by positivity
      exact mul_le_mul_of_nonneg_left hpot this
    refine le_trans (le_trans herr hmono) ?_
    rw [hsplit_pow p]
    field_simp
    nlinarith
  have h3 : ‖hval z 0 (wcnt p) - Complex.exp z‖ ≤ 1 / (2 : ℝ) ^ (p + 20) := by
    have htail := expTail z p hp hz
    have hw : wcnt p = 8 * (p + 1) := rfl
    rw [← hw] at htail
    rw [← expRec.2.2.2.1 z (wcnt p)] at htail
    rwa [norm_sub_rev] at htail
  have hB : ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - Complex.exp z‖ ≤
      1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ (p + 20) := by
    have hsum := norm_add_le (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) -
      hval z 0 (wcnt p)) (hval z 0 (wcnt p) - Complex.exp z)
    have heq : ((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - Complex.exp z =
        (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - hval z 0 (wcnt p)) +
        (hval z 0 (wcnt p) - Complex.exp z) := by ring
    rw [heq]
    exact le_trans hsum (add_le_add h2 h3)
  have h20 : 1 / (2 : ℝ) ^ (p + 20) ≤ 1 / (2 : ℝ) ^ p := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have harith : 2 / (2 : ℝ) ^ p + (1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ (p + 20)) ≤ 4 / (2 : ℝ) ^ p := by
    have h2 : (4 : ℝ) / (2 : ℝ) ^ p =
        2 / (2 : ℝ) ^ p + (1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p) := by
      field_simp
      ring
    rw [h2]
    linarith [h20]
  have heq2 : ((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p - Complex.exp z =
      (((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
        ((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) +
      (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - Complex.exp z) := by ring
  rw [heq2]
  calc ‖(((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
        ((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)) +
      (((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - Complex.exp z)‖
      ≤ ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
          ((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p)‖ +
        ‖((Qre : ℂ) + (Qim : ℂ) * Complex.I) / (2 : ℂ) ^ (wprec p) - Complex.exp z‖ :=
        norm_add_le _ _
    _ ≤ 2 / (2 : ℝ) ^ p + (1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ (p + 20)) := add_le_add h1 hB
    _ ≤ 4 / (2 : ℝ) ^ p := harith

/-! ## Dropping the top block -/

theorem drop_seven_append (a b c d e f g : Val) (rest : List Val) :
    ([a, b, c, d, e, f, g] ++ rest).drop 7 = rest := by
  rw [show (7 : ℕ) = ([a, b, c, d, e, f, g] : List Val).length from rfl, List.drop_left]

theorem drop_eight_append (a b c d e f g h : Val) (rest : List Val) :
    ([a, b, c, d, e, f, g, h] ++ rest).drop 8 = rest := by
  rw [show (8 : ℕ) = ([a, b, c, d, e, f, g, h] : List Val).length from rfl, List.drop_left]

theorem drop_append_postWin (p : ℕ) (X Y Qre Qim dd : ℤ) (rest : List Val) :
    (postWin p X Y Qre Qim dd ++ rest).drop 7 = rest := by
  rw [show (7 : ℕ) = (postWin p X Y Qre Qim dd).length from rfl, List.drop_left]

theorem drop_append_preWin (p : ℕ) (X Y Qre Qim dd : ℤ) (rest : List Val) :
    (preWin p X Y Qre Qim dd ++ rest).drop 8 = rest := by
  rw [show (8 : ℕ) = (preWin p X Y Qre Qim dd).length from rfl, List.drop_left]


end ExpAsm
end Work.Fx
