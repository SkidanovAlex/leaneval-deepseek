import Mathlib
import Submission.Work.BMF.vmvt_setup
import Submission.Work.BMF.vmvt_M_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The arithmetic core of the Vinogradov–Linnik induction step

This file proves `Work.BMF.vmvt_step_ineq`: the single induction step of the proof of the
Vinogradov mean value estimate `Work.BMF.vmvt_uniform`.  All the work here is elementary real
arithmetic (`Real.exp`, `Real.log`, `Real.rpow`) collected in a few auxiliary lemmas.
-/

namespace Work.BMF

open scoped BigOperators

set_option maxHeartbeats 2000000

/-! ## Elementary manipulation lemmas -/

/-- Logarithm of a five-fold product of positive reals. -/
lemma log_mul5 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) :
    Real.log (a*b*c*d*e) = Real.log a + Real.log b + Real.log c + Real.log d + Real.log e := by
  rw [Real.log_mul (show a*b*c*d ≠ 0 by positivity) (show e ≠ 0 by positivity),
      Real.log_mul (show a*b*c ≠ 0 by positivity) (show d ≠ 0 by positivity),
      Real.log_mul (show a*b ≠ 0 by positivity) (show c ≠ 0 by positivity),
      Real.log_mul (show a ≠ 0 by positivity) (show b ≠ 0 by positivity)]

/-- `x^a * x^b * x^c = x^(a+b+c)` for `x > 0`. -/
lemma rpow_three (x : ℝ) (hx : 0 < x) (a b c : ℝ) : x^a * x^b * x^c = x^(a+b+c) := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]

/-! ## The exponent `th` -/

lemma th_one_aux (k : ℕ) (hk : 1 ≤ k) : th k 1 = (k:ℝ) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  simp only [th, Nat.cast_one]
  rw [mul_one, pow_one]
  push_cast
  field_simp
  ring

/-- `th k r > 0` for `k ≥ 2`, `r ≥ 1`: by induction on `r` using `th_key`. -/
lemma th_pos_aux (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) : 0 < th k r := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hq0 : (0:ℝ) ≤ 1 - 1/(k:ℝ) := by
    have h2 : 1/(k:ℝ) ≤ 1 := by
      rw [div_le_iff₀ hkpos]
      have h3 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      linarith
    linarith
  have hone : th k 1 = (k:ℝ) := th_one_aux k hk1
  have hstep : ∀ n : ℕ, 0 < th k (1+n) → 0 < th k (1+n+1) := by
    intro n ih
    have h := th_key k (1+n) hk1
    rw [← h]
    have h4 : 0 ≤ th k (1+n) * (1 - 1/(k:ℝ)) := mul_nonneg (le_of_lt ih) hq0
    have h5 : (0:ℝ) ≤ 2*(((1+n:ℕ)):ℝ) + ((k:ℝ)-1)/2 := by
      have h6 : (0:ℝ) ≤ ((1+n:ℕ):ℝ) := by positivity
      have h7 : (0:ℝ) ≤ (k:ℝ)-1 := by
        have h8 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
        linarith
      linarith
    linarith only [hkpos, h4, h5]
  have hmain : ∀ m : ℕ, 0 < th k (1+m) := by
    intro m
    induction m with
    | zero => simpa [hone] using hkpos
    | succ m ih => exact hstep m ih
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hr
  rw [hm]
  exact hmain m

lemma th_le_two_mul_aux (k r : ℕ) (hk : 1 ≤ k) : th k r ≤ 2*(k:ℝ)*(r:ℝ) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hq0 : (0:ℝ) ≤ 1 - 1/(k:ℝ) := by
    have h2 : 1/(k:ℝ) ≤ 1 := by
      rw [div_le_iff₀ hkpos]
      have h3 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    linarith
  have hq1 : 1 - 1/(k:ℝ) ≤ 1 := by
    have : (0:ℝ) ≤ 1/(k:ℝ) := div_nonneg zero_le_one (le_of_lt hkpos)
    linarith
  have hq : (1 - 1/(k:ℝ))^r ≤ 1 := pow_le_one₀ hq0 hq1
  simp only [th]
  push_cast
  nlinarith only [hq, le_of_lt hkpos]

lemma Estep_div_k_aux (k r : ℕ) (hk : 1 ≤ k) :
    ((2*k*r + k*(k-1)/2 : ℕ) : ℝ) / (k:ℝ) = 2*(r:ℝ) + ((k:ℝ)-1)/2 := by
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  have h2 : 2 ∣ k*(k-1) := by
    rw [← even_iff_two_dvd]
    exact Nat.even_mul_pred_self k
  have hdiv : ((k*(k-1)/2 : ℕ) : ℝ) = (k:ℝ)*((k:ℝ)-1)/2 := by
    rw [Nat.cast_div (K := ℝ) h2 (by norm_num)]
    rw [Nat.cast_mul, Nat.cast_sub hk]
    ring
  have hmain : ((2*k*r : ℕ) : ℝ) = 2*(k:ℝ)*(r:ℝ) := by push_cast; ring
  rw [Nat.cast_add, hdiv, hmain]
  field_simp
  try ring

/-! ## Bounds for `Y` -/

lemma Y_bound_aux (k Q : ℕ) (hk : 2 ≤ k) (hQ : 1 ≤ Q) :
    (((max (2*(max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1))) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ)) : ℝ)
      ≤ (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * (Q:ℝ)^(1/(k:ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hpC : 0 < pC := pC_pos
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hkR : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  set R : ℝ := (Q:ℝ)^(1/(k:ℝ)) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    exact Real.one_le_rpow hQ1 (by positivity)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  set A : ℝ := pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7 with hAdef
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hA7 : 2*(k:ℝ) + 7 ≤ A := by
    rw [hAdef]
    have : 0 ≤ pC*(k:ℝ)^3*Real.log k := by positivity
    linarith
  have hMle : (((max k (⌈R⌉₊+1)) : ℕ) : ℝ) ≤ (k:ℝ) + R + 2 := by
    have hceil : ((⌈R⌉₊ : ℕ) : ℝ) < R + 1 := Nat.ceil_lt_add_one hR0
    push_cast
    exact max_le (by linarith) (by linarith)
  have h1 : 2 * (((max k (⌈R⌉₊+1)) : ℕ) : ℝ) ≤ A * R := by
    have h2 : 2 * (((max k (⌈R⌉₊+1)) : ℕ) : ℝ) ≤ 2 * ((k:ℝ) + R + 2) := by linarith
    have h3 : 2 * ((k:ℝ) + R + 2) ≤ (2*(k:ℝ)+7) * R := by
      nlinarith only [hR1, le_of_lt hkR]
    have h4 : (2*(k:ℝ)+7) * R ≤ A * R := mul_le_mul_of_nonneg_right hA7 hR0
    linarith
  have h2 : ((⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ) : ℝ) ≤ A * R := by
    have hB0 : 0 ≤ pC*(k:ℝ)^3*Real.log k := by positivity
    have hlt : ((⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ) : ℝ)
        < pC*(k:ℝ)^3*Real.log k + 1 := Nat.ceil_lt_add_one hB0
    have hA' : pC*(k:ℝ)^3*Real.log k + 1 ≤ A := by rw [hAdef]; linarith [hkR]
    have hR' : pC*(k:ℝ)^3*Real.log k + 1
        ≤ (pC*(k:ℝ)^3*Real.log k + 1) * R := by
      nth_rewrite 1 [← mul_one (pC*(k:ℝ)^3*Real.log k + 1)]
      exact mul_le_mul_of_nonneg_left hR1 (by linarith)
    have hfin : (pC*(k:ℝ)^3*Real.log k + 1) * R ≤ A * R := mul_le_mul_of_nonneg_right hA' hR0
    linarith
  have hY : (((max (2*(max k (⌈R⌉₊+1))) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ)) : ℝ) ≤ A * R := by
    have hcast : (((max (2*(max k (⌈R⌉₊+1))) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ)) : ℝ)
        = max (2 * (((max k (⌈R⌉₊+1)) : ℕ) : ℝ)) ((⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_max, Nat.cast_mul]
      norm_num
    rw [hcast]
    exact max_le h1 h2
  rw [hAdef, hRdef] at hY
  exact hY

/-! ## Growth of `Ac` -/

lemma ac_ratio_aux (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    Ac C0 k r * Real.exp (C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k)) ≤ Ac C0 k (r+1) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hC0pos : 0 < C0 := C0_pos
  have hCk : 0 < C0 * (k:ℝ)^2 := by positivity
  have hlogkr : Real.log ((k:ℝ)*(r:ℝ)) = Real.log k + Real.log (r:ℝ) :=
    Real.log_mul (ne_of_gt hkpos) (ne_of_gt hr0)
  have hlogkr1 : Real.log ((k:ℝ)*((r:ℝ)+1)) = Real.log k + Real.log ((r:ℝ)+1) :=
    Real.log_mul (ne_of_gt hkpos) (by positivity)
  have hbracket : (r:ℝ)^2*(1+Real.log ((k:ℝ)*(r:ℝ))) + (2*(r:ℝ)+1)*(1+Real.log k)
      ≤ ((r:ℝ)+1)^2*(1+Real.log ((k:ℝ)*((r:ℝ)+1))) := by
    rw [hlogkr, hlogkr1]
    have hlogr0 : 0 ≤ Real.log (r:ℝ) := Real.log_nonneg hr1
    have hlogr_le : Real.log (r:ℝ) ≤ Real.log ((r:ℝ)+1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogr1_0 : 0 ≤ Real.log ((r:ℝ)+1) := le_trans hlogr0 hlogr_le
    have hsq : (r:ℝ)^2 ≤ ((r:ℝ)+1)^2 := by nlinarith only [hr1]
    nlinarith only [hlogr0, hlogr_le, hlogr1_0, hsq]
  rw [Ac, Ac, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hthis := mul_le_mul_of_nonneg_left hbracket (le_of_lt hCk)
  nlinarith only [hthis]

/-! ## The constant term -/

lemma term_one_aux (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    (4*(k:ℝ)^4)^(k*(r+1)) ≤ (1/2) * Ac C0 k (r+1) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
  have hC0 : (100:ℝ) ≤ C0 := by
    rw [C0]
    have h : (0:ℝ) < Real.log (pC + 8) := Real.log_pos (by linarith [pC_pos])
    linarith
  have hlog : Real.log (4*(k:ℝ)^4) = Real.log 4 + 4*Real.log k := by
    rw [Real.log_mul (show (4:ℝ) ≠ 0 by norm_num) (show (k:ℝ)^4 ≠ 0 by positivity),
        Real.log_pow]
    norm_num
  have hLHS : (4*(k:ℝ)^4)^(k*(r+1))
      = Real.exp (((k*(r+1) : ℕ)) * Real.log (4*(k:ℝ)^4)) := by
    rw [← Real.exp_log (show (0:ℝ) < (4*(k:ℝ)^4)^(k*(r+1)) by positivity), Real.log_pow]
  have h2 : 2 * (4*(k:ℝ)^4)^(k*(r+1)) ≤ Ac C0 k (r+1) := by
    have h2exp : (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    rw [hLHS, h2exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hlog]
    push_cast
    have hlog4 : Real.log 4 ≤ 4 := le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
    have hlog2 : Real.log 2 ≤ 1 := le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
    have hk1' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have hg : 0 ≤ Real.log k := Real.log_nonneg hk1'
    have hkr : (k:ℝ) ≤ (k:ℝ)*((r:ℝ)+1) := by
      have h3 : (0:ℝ) ≤ (k:ℝ)*(r:ℝ) := mul_nonneg (le_of_lt hkpos) hr0
      linarith only [h3]
    have hlogmono : Real.log k ≤ Real.log ((k:ℝ)*((r:ℝ)+1)) := Real.log_le_log hkpos hkr
    have hkr1 : (1:ℝ) ≤ (k:ℝ)*((r:ℝ)+1) := by linarith only [hkr, hk1']
    have hkey : (k:ℝ)*((r:ℝ)+1) ≤ (k:ℝ)^2*((r:ℝ)+1)^2 := by
      have h5 : ((k:ℝ)*((r:ℝ)+1)) ≤ ((k:ℝ)*((r:ℝ)+1))*((k:ℝ)*((r:ℝ)+1)) := by
        nlinarith only [hkr1]
      have h6 : ((k:ℝ)*((r:ℝ)+1))*((k:ℝ)*((r:ℝ)+1)) = (k:ℝ)^2*((r:ℝ)+1)^2 := by ring
      linarith only [h5, h6]
    have hA : (k:ℝ)*((r:ℝ)+1)*(Real.log 4 + 4*Real.log k)
        ≤ (k:ℝ)*((r:ℝ)+1)*(4*(1+Real.log k)) := by
      have h7 : Real.log 4 + 4*Real.log k ≤ 4*(1+Real.log k) := by linarith only [hlog4]
      exact mul_le_mul_of_nonneg_left h7 (by nlinarith only [hkr1, hkpos])
    have h8 : (0:ℝ) ≤ 4*(1+Real.log k) := by linarith only [hg]
    have hB : (k:ℝ)*((r:ℝ)+1)*(4*(1+Real.log k))
        ≤ 4*((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k) := by
      have h9 : ((k:ℝ)*((r:ℝ)+1))*(4*(1+Real.log k))
          ≤ ((k:ℝ)^2*((r:ℝ)+1)^2)*(4*(1+Real.log k)) :=
        mul_le_mul_of_nonneg_right hkey h8
      have h10 : ((k:ℝ)^2*((r:ℝ)+1)^2)*(4*(1+Real.log k))
          = 4*((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k) := by ring
      have h11 : (k:ℝ)*((r:ℝ)+1)*(4*(1+Real.log k))
          = ((k:ℝ)*((r:ℝ)+1))*(4*(1+Real.log k)) := by ring
      linarith only [h9, h10, h11]
    have hY1 : (1:ℝ) ≤ ((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k) := by
      have h10 : (1:ℝ) ≤ ((k:ℝ)*((r:ℝ)+1))^2 := by nlinarith only [hkr1]
      have h11 : (1:ℝ) ≤ 1 + Real.log k := by linarith only [hg]
      exact one_le_mul_of_one_le_of_one_le h10 h11
    have hY2 : ((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k)
        ≤ ((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log ((k:ℝ)*((r:ℝ)+1))) := by
      have h12 : (1+Real.log k) ≤ (1+Real.log ((k:ℝ)*((r:ℝ)+1))) := by linarith only [hlogmono]
      exact mul_le_mul_of_nonneg_left h12 (by positivity)
    have hE : Real.log 2 + 4*((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k)
        ≤ C0*((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log ((k:ℝ)*((r:ℝ)+1))) := by
      have h5 : 1 + 4*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k))
          ≤ 5*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k)) := by linarith only [hY1]
      have h6 : 5*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k))
          ≤ C0*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k)) := by
        have h13 : (5:ℝ) ≤ C0 := by linarith only [hC0]
        exact mul_le_mul_of_nonneg_right h13 (by positivity)
      have h7 : C0*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log k))
          ≤ C0*(((k:ℝ)*((r:ℝ)+1))^2*(1+Real.log ((k:ℝ)*((r:ℝ)+1)))) :=
        mul_le_mul_of_nonneg_left hY2 (by positivity)
      linarith only [hlog2, h5, h6, h7]
    linarith only [hA, hB, hE]
  nlinarith only [h2]

/-! ## The constant comparison at the heart of the induction step -/

lemma master_const_aux (k r : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) :
    16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
      * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^(2*k*r+k*(k-1)/2)
      * (2:ℝ)^(th k r)
    ≤ Real.exp (C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hpC : 0 < pC := pC_pos
  have hg : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hle : Real.log k ≤ (k:ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
  have hLpos : 0 < Real.log (pC + 8) := Real.log_pos (by linarith [pC_pos])
  have hL0 : 0 ≤ Real.log (pC + 8) := le_of_lt hLpos
  have hfpos : (0:ℝ) < ((k.factorial:ℕ):ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  set A : ℝ := pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7 with hAdef
  set E : ℕ := 2*k*r + k*(k-1)/2 with hEdef
  have hEdiv := Estep_div_k_aux k r hk1
  rw [← hEdef] at hEdiv
  have hApos : 0 < A := by
    rw [hAdef]
    have : 0 ≤ pC*(k:ℝ)^3*Real.log k := by positivity
    linarith
  have hA_le : A ≤ (pC + 8) * (k:ℝ)^3 * (Real.log k + 1) := by
    rw [hAdef]
    have h8 : 2*(k:ℝ) + 7 ≤ 8*(k:ℝ)^3 := by
      have h4 : 2*(k:ℝ) + 7 ≤ 4*(k:ℝ)^2 := by
        nlinarith only [sq_nonneg ((k:ℝ)-1), hk2]
      have h5 : 4*(k:ℝ)^2 ≤ 8*(k:ℝ)^3 := by nlinarith only [hk2, sq_nonneg (k:ℝ)]
      linarith
    nlinarith only [h8, hg, hpC]
  have hlogA : Real.log A ≤ Real.log (pC + 8) + 4 * Real.log k := by
    have h2 : 0 < (pC + 8) * (k:ℝ)^3 * (Real.log k + 1) := by positivity
    have h1 : Real.log A ≤ Real.log ((pC + 8) * (k:ℝ)^3 * (Real.log k + 1)) :=
      Real.log_le_log hApos hA_le
    have h3 : Real.log ((pC + 8) * (k:ℝ)^3 * (Real.log k + 1))
        = Real.log (pC + 8) + 3 * Real.log k + Real.log (Real.log k + 1) := by
      rw [Real.log_mul (show (pC + 8) * (k:ℝ)^3 ≠ 0 by
              exact ne_of_gt (by positivity))
          (show Real.log k + 1 ≠ 0 by
              exact ne_of_gt (by linarith)),
          Real.log_mul (show pC + 8 ≠ 0 by exact ne_of_gt (by linarith))
            (show (k:ℝ)^3 ≠ 0 by exact ne_of_gt (by positivity)),
          Real.log_pow]
      ring
    have h4 : Real.log (Real.log k + 1) ≤ Real.log k :=
      Real.log_le_log (by linarith) (by linarith)
    rw [h3] at h1
    linarith
  have hfac : Real.log ((k.factorial:ℕ):ℝ) ≤ (k:ℝ) * Real.log k := by
    have h1 : ((k.factorial:ℕ):ℝ) ≤ (k:ℝ)^k := by
      have h2 : ((k^k : ℕ) : ℝ) = (k:ℝ)^k := by push_cast; ring
      calc ((k.factorial:ℕ):ℝ) ≤ ((k^k : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow k
        _ = (k:ℝ)^k := h2
    calc Real.log ((k.factorial:ℕ):ℝ) ≤ Real.log ((k:ℝ)^k) := Real.log_le_log hfpos h1
      _ = (k:ℝ) * Real.log k := by rw [Real.log_pow]
  have hth : (th k r) * Real.log 2 ≤ 2*(k:ℝ)*(r:ℝ) * Real.log k := by
    have h1 : th k r ≤ 2*(k:ℝ)*(r:ℝ) := th_le_two_mul_aux k r hk1
    have h2 : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by linarith)
    have h3 : 0 ≤ th k r := le_of_lt (th_pos_aux k r hk hr)
    have h4 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h5 : 0 ≤ 2*(k:ℝ)*(r:ℝ) := by positivity
    calc th k r * Real.log 2 ≤ (2*(k:ℝ)*(r:ℝ)) * Real.log k := mul_le_mul h1 h2 h4 h5
      _ = 2*(k:ℝ)*(r:ℝ) * Real.log k := rfl
  have hEbound : (E:ℝ) ≤ 2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2 := by
    rw [hEdef]
    have h1 : ((k*(k-1)/2 : ℕ) : ℝ) ≤ (k:ℝ)^2 := by
      have h2 : k*(k-1)/2 ≤ k*k := by
        calc k*(k-1)/2 ≤ k*(k-1) := Nat.div_le_self _ _
          _ ≤ k*k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
      calc ((k*(k-1)/2 : ℕ) : ℝ) ≤ ((k*k : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (k:ℝ)^2 := by push_cast; ring
    have h0 : ((2*k*r : ℕ) : ℝ) = 2*(k:ℝ)*(r:ℝ) := by push_cast; ring
    rw [Nat.cast_add, h0]
    linarith
  have hLHSpos : 0 < 16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6 * A^E * (2:ℝ)^(th k r) := by
    have h1 : (0:ℝ) < (2:ℝ)^(th k r) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : (0:ℝ) < A^E := pow_pos hApos E
    have h3 : (0:ℝ) < (k:ℝ)^6 := by positivity
    positivity
  have h16 : Real.log 16 ≤ 16 :=
    le_trans (Real.log_le_sub_one_of_pos (by norm_num)) (by norm_num)
  have hnum : Real.log 16 + (k:ℝ)*Real.log k + 6*Real.log k
      + (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2) * (Real.log (pC+8) + 4*Real.log k)
      + 2*(k:ℝ)*(r:ℝ)*Real.log k
      ≤ C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k) := by
    rw [C0]
    have hk2s : (4:ℝ) ≤ (k:ℝ)^2 := by nlinarith only [hk2]
    have hLg : 0 ≤ Real.log (pC+8) * Real.log k := mul_nonneg hL0 hg
    have hm1 : (1:ℝ) ≤ (1+Real.log (pC+8))*(1+Real.log k) :=
      one_le_mul_of_one_le_of_one_le (by linarith only [hL0]) (by linarith only [hg])
    have hBr : Real.log (pC+8) ≤ (1+Real.log (pC+8))*(1+Real.log k) := by
      nlinarith only [hL0, hg, hLg]
    have hgr : Real.log k ≤ (1+Real.log (pC+8))*(1+Real.log k) := by
      nlinarith only [hL0, hg, hLg]
    have hkk' : 2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2 ≤ 3*(k:ℝ)^2*(r:ℝ) := by
      have h1 : (0:ℝ) ≤ (k:ℝ)*(3*(k:ℝ)-2)*((r:ℝ)-1) :=
        mul_nonneg (mul_nonneg (by linarith only [hk2]) (by linarith only [hk2])) (by linarith only [hr1])
      have h2 : (0:ℝ) ≤ (k:ℝ)*((k:ℝ)-2) := mul_nonneg (by linarith only [hk2]) (by linarith only [hk2])
      nlinarith only [h1, h2]
    have hW16 : Real.log 16 ≤ 4*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by
      have h4 : (4:ℝ) ≤ (k:ℝ)^2*(r:ℝ) := by nlinarith only [hk2s, hr1]
      have h5 : (4:ℝ) ≤ (k:ℝ)^2*(r:ℝ)*((1+Real.log (pC+8))*(1+Real.log k)) :=
        le_trans h4 (le_mul_of_one_le_right (by positivity) hm1)
      have h6 : (k:ℝ)^2*(r:ℝ)*((1+Real.log (pC+8))*(1+Real.log k))
          = (k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k) := by ring
      linarith only [h16, h5, h6]
    have hWkg : (k:ℝ)*Real.log k ≤ (k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k) := by
      have h4 : (k:ℝ) ≤ (k:ℝ)^2*(r:ℝ) := by nlinarith only [hk2, hr1]
      have h5 : (k:ℝ)*Real.log k ≤ ((k:ℝ)^2*(r:ℝ))*Real.log k :=
        mul_le_mul_of_nonneg_right h4 hg
      have h6 : ((k:ℝ)^2*(r:ℝ))*Real.log k
          ≤ ((k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k)) :=
        mul_le_mul_of_nonneg_left hgr (by positivity)
      have h7 : ((k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k))
          = (k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k) := by ring
      linarith only [h5, h6, h7]
    have hW6g : 6*Real.log k ≤ 6*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by
      have h4 : (1:ℝ) ≤ (k:ℝ)^2*(r:ℝ) := by nlinarith only [hk2s, hr1]
      have h5 : Real.log k ≤ ((k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k)) := by
        have h5' : (1+Real.log (pC+8))*(1+Real.log k)
            ≤ ((k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k)) :=
          le_mul_of_one_le_left (by positivity) h4
        exact le_trans hgr h5'
      have h6 : ((k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k))
          = (k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k) := by ring
      linarith only [h5, h6]
    have hWL : (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2)*Real.log (pC+8)
        ≤ 3*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by
      have h4 := mul_le_mul hkk' hBr (le_of_lt hLpos)
        (by positivity : (0:ℝ) ≤ 3*(k:ℝ)^2*(r:ℝ))
      have h5 : (3*(k:ℝ)^2*(r:ℝ))*((1+Real.log (pC+8))*(1+Real.log k))
          = 3*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by ring
      linarith only [h4, h5]
    have hW4g : (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2)*(4*Real.log k)
        ≤ 12*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by
      have h4g : 4*Real.log k ≤ 4*((1+Real.log (pC+8))*(1+Real.log k)) := by
        nlinarith only [hgr]
      have h4 := mul_le_mul hkk' h4g (by positivity : (0:ℝ) ≤ 4*Real.log k)
        (by positivity : (0:ℝ) ≤ 3*(k:ℝ)^2*(r:ℝ))
      ring_nf at h4 ⊢
      linarith only [h4]
    have hW2kr : 2*(k:ℝ)*(r:ℝ)*Real.log k
        ≤ 2*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by
      have h4b : (1:ℝ) ≤ (k:ℝ) := by linarith only [hk2]
      have h4c : Real.log k ≤ (k:ℝ)*((1+Real.log (pC+8))*(1+Real.log k)) :=
        le_trans hgr (le_mul_of_one_le_left (by positivity) h4b)
      have h8 : (2*(k:ℝ)*(r:ℝ)) * Real.log k
          ≤ (2*(k:ℝ)*(r:ℝ)) * ((k:ℝ)*((1+Real.log (pC+8))*(1+Real.log k))) :=
        mul_le_mul_of_nonneg_left h4c (by positivity)
      have h9 : (2*(k:ℝ)*(r:ℝ)) * ((k:ℝ)*((1+Real.log (pC+8))*(1+Real.log k)))
          = 2*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by ring
      have h10 : (2*(k:ℝ)*(r:ℝ)) * Real.log k = 2*(k:ℝ)*(r:ℝ)*Real.log k := by ring
      linarith only [h8, h9, h10]
    have hWfin : 28*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k))
        ≤ 100*(k:ℝ)^2*(2*(r:ℝ)+1)*(1+Real.log (pC+8))*(1+Real.log k) := by
      have h0 : (28:ℝ)*(r:ℝ) ≤ 100*(2*(r:ℝ)+1) := by linarith only [hr1]
      have h7 : (0:ℝ) ≤ (k:ℝ)^2*(1+Real.log (pC+8))*(1+Real.log k) := by
        have h8 : (0:ℝ) ≤ (k:ℝ)^2 := by positivity
        have h9 : (0:ℝ) ≤ 1+Real.log (pC+8) := by linarith only [hL0]
        have h10 : (0:ℝ) ≤ 1+Real.log k := by linarith only [hg]
        positivity
      have h0' := mul_le_mul_of_nonneg_right h0 h7
      have e1 : (28:ℝ)*(r:ℝ)*((k:ℝ)^2*(1+Real.log (pC+8))*(1+Real.log k))
          = 28*((k:ℝ)^2*(r:ℝ)*(1+Real.log (pC+8))*(1+Real.log k)) := by ring
      have e2 : (100*(2*(r:ℝ)+1))*((k:ℝ)^2*(1+Real.log (pC+8))*(1+Real.log k))
          = 100*(k:ℝ)^2*(2*(r:ℝ)+1)*(1+Real.log (pC+8))*(1+Real.log k) := by ring
      linarith only [h0', e1, e2]
    have hexp : (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2) * (Real.log (pC+8) + 4*Real.log k)
        = (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2)*Real.log (pC+8)
          + (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2)*(4*Real.log k) := by ring
    rw [hexp]
    linarith only [hW16, hWkg, hW6g, hWL, hW4g, hW2kr, hWfin]

  have hbound : Real.log (16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6 * A^E * (2:ℝ)^(th k r))
      ≤ C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k) := by
    have hlog := log_mul5 16 ((k.factorial:ℕ):ℝ) ((k:ℝ)^6) (A^E) ((2:ℝ)^(th k r))
      (by norm_num) hfpos (by positivity) (pow_pos hApos E)
      (Real.rpow_pos_of_pos (by norm_num) _)
    rw [hlog, Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num)]
    have h1 : (E:ℝ) * Real.log A ≤ (E:ℝ) * (Real.log (pC+8) + 4*Real.log k) :=
      mul_le_mul_of_nonneg_left hlogA (by positivity)
    have h2 : (E:ℝ) * (Real.log (pC+8) + 4*Real.log k)
        ≤ (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2) * (Real.log (pC+8) + 4*Real.log k) :=
      mul_le_mul_of_nonneg_right hEbound (by linarith)
    have h3 : (E:ℝ) * Real.log A ≤ (2*(k:ℝ)*(r:ℝ) + (k:ℝ)^2) * (Real.log (pC+8) + 4*Real.log k) :=
      le_trans h1 h2
    push_cast
    linarith only [hfac, h3, hth, hnum]
  calc 16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6 * A^E * (2:ℝ)^(th k r)
      = Real.exp (Real.log (16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6 * A^E
          * (2:ℝ)^(th k r))) := (Real.exp_log hLHSpos).symm
    _ ≤ Real.exp (C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k)) :=
        Real.exp_le_exp.mpr hbound

/-- The arithmetic core of the induction: given the recursion `J_{k(r+1),k}(Q) ≤ (4k⁴)^{k(r+1)} + 4·k!·(k³)²·Y^{2kr+k(k−1)/2}·Q^k·J_{kr,k}(1+Q/M)` and the induction hypothesis `J_{kr,k}(1+Q/M) ≤ Ac C₀ k r·(1+Q/M)^{th k r}`, the right-hand side is dominated by `Ac C₀ k (r+1)·Q^{th k (r+1)}`, where `M = max k (⌈Q^{1/k}⌉+1)` (so `Q ≤ M^k`, whence `1+Q/M ≤ 2Q^{1−1/k}`) and `Y = max (2M) ⌈pC·k³·log k⌉` (so `Y ≤ (pC·k³·log k + 2k + 5)·Q^{1/k}`). The proof is the exponent identity `k + 2r + (k−1)/2 + th k r·(1−1/k) = th k (r+1)` (`Work.BMF.th_key`) plus the growth of `Ac` (`Ac C₀ k (r+1)/Ac C₀ k r ≥ exp(C₀ k² (2r+1)(1+log k))`) with `C0 = 100(1+log(pC+8))` chosen large enough. The definitions `th`, `Ac`, `C0`, `pC` live in `Submission/Work/BMF/vmvt_setup.lean` (import `Submission.Work.BMF.vmvt_setup`). -/
theorem vmvt_step_ineq (k r Q : ℕ) (hk : 2 ≤ k) (hr : 1 ≤ r) (hQ : 1 ≤ Q) :
    (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
      * (((max (2*(max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1))) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ : ℕ)) : ℝ)^(2*k*r+k*(k-1)/2)
      * (Q:ℝ)^k * (Ac C0 k r * (1 + (Q:ℝ)/((max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊+1) : ℕ) : ℝ))^(th k r))
    ≤ Ac C0 k (r+1) * (Q:ℝ)^(th k (r+1)) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < (k:ℝ) := by
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    linarith
  have hkRne : (k:ℝ) ≠ 0 := ne_of_gt hkR
  have hpC : 0 < pC := pC_pos
  set s : ℝ := (Q:ℝ) with hsdef
  set R : ℝ := s^(1/(k:ℝ)) with hRdef
  set M : ℕ := max k (⌈R⌉₊+1) with hMdef
  set Y : ℕ := max (2*M) ⌈pC*(k:ℝ)^3*Real.log k⌉₊ with hYdef
  set E : ℕ := 2*k*r+k*(k-1)/2 with hEdef
  have hs1 : (1:ℝ) ≤ s := by rw [hsdef]; exact_mod_cast hQ
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hRs : R = s^(1/(k:ℝ)) := hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact Real.rpow_pos_of_pos hs0 _
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hfact0 : (0:ℝ) < ((k.factorial:ℕ):ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hMb := vmvt_M_bounds k Q hk hQ
  rw [← hsdef, ← hRdef, ← hMdef] at hMb
  obtain ⟨hQleM, hMQ⟩ := hMb
  have hYb := Y_bound_aux k Q hk hQ
  rw [← hsdef, ← hRdef, ← hMdef, ← hYdef] at hYb
  have hMk : (k:ℝ) ≤ (M:ℝ) := by
    rw [hMdef, Nat.cast_max]
    exact le_max_left _ _
  have hMpos : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le hkR hMk
  have hsM0 : 0 ≤ s/(M:ℝ) := div_nonneg (le_of_lt hs0) (le_of_lt hMpos)
  have h1sM : 0 ≤ 1 + s/(M:ℝ) := by linarith
  have hAexp0 : 0 ≤ pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7 := by
    have h1 : 0 ≤ pC*(k:ℝ)^3*Real.log k :=
      mul_nonneg (mul_nonneg (le_of_lt hpC) (by positivity)) hlogk0
    linarith
  have hexp : (E:ℝ)/(k:ℝ) + (k:ℝ) + (1-1/(k:ℝ))*(th k r) = th k (r+1) := by
    have h1 := Estep_div_k_aux k r hk1
    rw [← hEdef] at h1
    have h2 := th_key k r hk1
    nlinarith only [h1, h2]
  -- the zero-th order term
  have hT1 : (4*(k:ℝ)^4)^(k*(r+1)) ≤ (1/2) * (Ac C0 k (r+1) * s^(th k (r+1))) := by
    have h1 := term_one_aux k r hk hr
    have h2 : 1 ≤ s^(th k (r+1)) :=
      Real.one_le_rpow hs1 (le_of_lt (th_pos_aux k (r+1) hk (by omega)))
    have h3 : 0 < Ac C0 k (r+1) := Real.exp_pos _
    nlinarith only [h1, h2, h3]
  -- the coefficient
  have h1 := master_const_aux k r hk hr
  have h2 := ac_ratio_aux k r hk hr
  have hcoef : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
        * (2:ℝ)^(th k r) * Ac C0 k r ≤ (1/2) * Ac C0 k (r+1) := by
    have hAc1 : 0 < Ac C0 k (r+1) := Real.exp_pos _
    have hAr : 0 ≤ Ac C0 k r := le_of_lt (Real.exp_pos _)
    have hstep : 16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * Ac C0 k r ≤ Ac C0 k (r+1) := by
      calc 16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
            * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
            * (2:ℝ)^(th k r) * Ac C0 k r
          = (16 * ((k.factorial:ℕ):ℝ) * (k:ℝ)^6
            * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
            * (2:ℝ)^(th k r)) * Ac C0 k r := by ring
        _ ≤ Real.exp (C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k)) * Ac C0 k r :=
            mul_le_mul_of_nonneg_right h1 hAr
        _ = Ac C0 k r * Real.exp (C0 * (k:ℝ)^2 * (2*(r:ℝ)+1) * (1 + Real.log k)) := by ring
        _ ≤ Ac C0 k (r+1) := h2
    nlinarith only [hstep, hAc1]
  -- the main term
  have hYpow : ((Y:ℕ):ℝ)^E
      ≤ (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) :=
    pow_le_pow_left₀ (by positivity) hYb E
  have hthr0 : 0 ≤ th k r := le_of_lt (th_pos_aux k r hk hr)
  have hbasestep : (1 + s/(M:ℝ))^(th k r) ≤ (2*s^(1-1/(k:ℝ)))^(th k r) :=
    Real.rpow_le_rpow h1sM hMQ hthr0
  have hAcr0 : 0 ≤ Ac C0 k r := le_of_lt (Real.exp_pos _)
  have h4k0 : 0 ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 := by positivity
  have hsp0 : 0 ≤ s^k := pow_nonneg (le_of_lt hs0) k
  have h1s0 : 0 ≤ (1 + s/(M:ℝ))^(th k r) := Real.rpow_nonneg h1sM _
  have h2s0 : 0 ≤ 2*s^(1-1/(k:ℝ)) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hs0) _)
  have h2sp0 : 0 ≤ (2*s^(1-1/(k:ℝ)))^(th k r) := Real.rpow_nonneg h2s0 _
  have hAR0 : 0 ≤ (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R := mul_nonneg hAexp0 hR0
  have hARp0 : 0 ≤ ((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E := pow_nonneg hAR0 E
  have hYT0 : 0 ≤ ((Y:ℕ):ℝ)^E := pow_nonneg (by positivity) E
  have hstepA : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
        * (Ac C0 k r * (1 + s/(M:ℝ))^(th k r))
      ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (Ac C0 k r * (2*s^(1-1/(k:ℝ)))^(th k r)) := by
    refine mul_le_mul ?_ ?_ (mul_nonneg hAcr0 h1s0) ?_
    · have hx : ((Y:ℕ):ℝ)^E * s^k
          ≤ (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k :=
        mul_le_mul_of_nonneg_right hYpow hsp0
      have hx2 : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * (((Y:ℕ):ℝ)^E * s^k)
          ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * ((((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k) :=
        mul_le_mul_of_nonneg_left hx h4k0
      calc 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
          = 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * (((Y:ℕ):ℝ)^E * s^k) := by ring
        _ ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * ((((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k) := hx2
        _ = 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
            * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k := by ring
    · exact mul_le_mul_of_nonneg_left hbasestep hAcr0
    · have hX : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 := h4k0
      have hY0 : (0:ℝ) ≤ ((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E := hARp0
      have hZ0 : (0:ℝ) ≤ s^k := hsp0
      have h1' : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) := mul_nonneg hX hY0
      have h2' : (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k := mul_nonneg h1' hZ0
      simpa only [mul_assoc] using h2'
  have hRE : R^E = s^((E:ℝ)/(k:ℝ)) := by
    rw [hRs, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs0)]
    congr 1
    field_simp
    try ring
  have hmulpow : (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E)
      = (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E * s^((E:ℝ)/(k:ℝ)) := by
    rw [mul_pow, hRE]
  have h2E : (2*s^(1-1/(k:ℝ)))^(th k r)
      = (2:ℝ)^(th k r) * s^((1-1/(k:ℝ))*(th k r)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hs0) _),
        ← Real.rpow_mul (le_of_lt hs0)]
  have hsk : s^k = s^((k:ℝ)) := (Real.rpow_natCast s k).symm
  have hstepB : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (Ac C0 k r * (2*s^(1-1/(k:ℝ)))^(th k r))
      = (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * Ac C0 k r)
        * (s^((E:ℝ)/(k:ℝ)) * s^((k:ℝ)) * s^((1-1/(k:ℝ))*(th k r))) := by
    rw [hmulpow, h2E, hsk]
    ring
  have hstepB' : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
        * (((pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7) * R)^E) * s^k
        * (Ac C0 k r * (2*s^(1-1/(k:ℝ)))^(th k r))
      = (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * Ac C0 k r) * s^(th k (r+1)) := by
    rw [hstepB, rpow_three s hs0 ((E:ℝ)/(k:ℝ)) ((k:ℝ)) ((1-1/(k:ℝ))*(th k r)), hexp]
  have hstepC : (4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6
          * (pC*(k:ℝ)^3*Real.log k + 2*(k:ℝ) + 7)^E
          * (2:ℝ)^(th k r) * Ac C0 k r) * s^(th k (r+1))
      ≤ (1/2) * Ac C0 k (r+1) * s^(th k (r+1)) :=
    mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (le_of_lt hs0) _)
  have hT2 : 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
        * (Ac C0 k r * (1 + s/(M:ℝ))^(th k r))
      ≤ (1/2) * Ac C0 k (r+1) * s^(th k (r+1)) := by
    calc 4*((k.factorial:ℕ):ℝ)*(k:ℝ)^6 * ((Y:ℕ):ℝ)^E * s^k
          * (Ac C0 k r * (1 + s/(M:ℝ))^(th k r))
        ≤ _ := hstepA
      _ = _ := hstepB'
      _ ≤ _ := hstepC
  have hsum := add_le_add hT1 hT2
  linarith only [hsum]

end Work.BMF
