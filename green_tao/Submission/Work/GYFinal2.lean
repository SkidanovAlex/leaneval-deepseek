import Submission.Work.GYCorr13
import Submission.Work.GYLocal4
import Submission.Work.GYFinal
import Submission.Commons.NumberTheory.Sieve.density_fGT_window

/-!
# `GYFinal2`: the final assembly of the Green–Tao majorant interface `hP`

This file discharges the hypothesis `hP` of `GYMaj.green_tao_of_majorant`: for every `k ≥ 3` there
are `δ > 0` and a constant `CmB`, and for every `cd > 0`, `ε > 0` a threshold `P` such that for
every prime `p ≥ P` there are `R, W, B` with the Green–Tao pseudorandomness, density, domination
and support properties.

The correlation constant is the `p`-free `CmB m q = max 1 (Dcmax m q + (Kmax m)^q * (2 CwMoment (Ec m q)))`
of `GYCorr13`, so no uniformity issue arises.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj

open GYMaj.BoxAvg GYMaj.Local GYMaj.Corr
open Commons.NumberTheory.Sieve

/-! ## 1. The explicit constants `ε_box`, `εbad`, `Q` -/

/-- `2^{k·2^{k-1}} · (k·2^{k-1})`, the natural "size" of the localisation parameters. -/
noncomputable def PsiK (k : ℕ) : ℝ :=
  ((k * 2 ^ (k - 1) : ℕ) : ℝ) * (2 : ℝ) ^ (k * 2 ^ (k - 1))

/-- The box-average accuracy `ε_box`. -/
noncomputable def epsB (k : ℕ) (ε : ℝ) : ℝ := min 1 (ε / (6 * (PsiK k + 1)))

/-- The localisation error `εbad`. -/
noncomputable def epsD (k : ℕ) (ε : ℝ) : ℝ := ε / (6 * (3 : ℝ) ^ (k * 2 ^ (k - 1)))

/-- The lower bound on `Q` coming from `hbadQ`. -/
noncomputable def hbadBound (k : ℕ) (ε : ℝ) : ℝ :=
  2 * PsiK k * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ)
    * (2 : ℝ) ^ (3 * k) / epsD k ε

/-- The box parameter `Q`. -/
noncomputable def Qcand (k : ℕ) (ε : ℝ) : ℕ :=
  ⌈max (max 1 (16 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1))
    (max (2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * 4 / 3 + 1) (hbadBound k ε))⌉₊

lemma PsiK_nonneg (k : ℕ) : 0 ≤ PsiK k := by
  rw [PsiK]
  positivity

lemma PsiK_ge (k : ℕ) : ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ PsiK k := by
  rw [PsiK]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k * 2 ^ (k - 1)) := one_le_pow₀ (by norm_num)
  have h2 : (0 : ℝ) ≤ ((k * 2 ^ (k - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

lemma epsB_pos {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < epsB k ε := by
  rw [epsB, lt_min_iff]
  refine ⟨one_pos, ?_⟩
  apply div_pos hε
  have := PsiK_nonneg k
  linarith

lemma epsB_le_one (k : ℕ) (ε : ℝ) : epsB k ε ≤ 1 := min_le_left _ _

lemma epsB_nonneg {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 ≤ epsB k ε := (epsB_pos hε).le

lemma epsB_hsp1 {k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    epsB k ε * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * 2 ^ (k * 2 ^ (k - 1)) ≤ ε / 3 := by
  have hP := PsiK_nonneg k
  have h1 : epsB k ε ≤ ε / (6 * (PsiK k + 1)) := min_le_right _ _
  have h2 : (0 : ℝ) < 6 * (PsiK k + 1) := by linarith
  have h3 : epsB k ε * PsiK k ≤ ε / (6 * (PsiK k + 1)) * PsiK k :=
    mul_le_mul_of_nonneg_right h1 hP
  have h4 : ε / (6 * (PsiK k + 1)) * PsiK k ≤ ε / 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h2]
    nlinarith
  have h5 : epsB k ε * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * 2 ^ (k * 2 ^ (k - 1))
      = epsB k ε * PsiK k := by rw [PsiK]; ring
  rw [h5]
  linarith

lemma epsB_hsp2 {k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    epsB k ε * ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ ε / 3 := by
  have hP := PsiK_nonneg k
  have h1 : epsB k ε ≤ ε / (6 * (PsiK k + 1)) := min_le_right _ _
  have h2 : (0 : ℝ) < 6 * (PsiK k + 1) := by linarith
  have h4 : ε / (6 * (PsiK k + 1)) * PsiK k ≤ ε / 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h2]
    nlinarith
  have hk := PsiK_ge k
  have h3 : epsB k ε * ((k * 2 ^ (k - 1) : ℕ) : ℝ) ≤ epsB k ε * PsiK k :=
    mul_le_mul_of_nonneg_left hk (le_of_lt (epsB_pos hε))
  have h5 : epsB k ε * PsiK k ≤ ε / (6 * (PsiK k + 1)) * PsiK k :=
    mul_le_mul_of_nonneg_right h1 hP
  linarith

lemma epsD_pos {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < epsD k ε := by
  rw [epsD]
  apply div_pos hε
  positivity

lemma epsD_nonneg {k : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 ≤ epsD k ε := (epsD_pos hε).le

lemma epsD_hsp3 {k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (3 : ℝ) ^ (k * 2 ^ (k - 1)) * epsD k ε ≤ ε / 3 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (k * 2 ^ (k - 1)) := by positivity
  rw [epsD, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 6 * _)]
  have h := mul_div_cancel₀ ε (ne_of_gt h3)
  nlinarith [h]

lemma Qcand_ge (k : ℕ) (ε : ℝ) : 1 ≤ Qcand k ε := by
  have h : (1 : ℝ) ≤ (Qcand k ε : ℝ) := by
    rw [Qcand]
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_max_left (1 : ℝ) _) (le_max_left _ _)
  exact_mod_cast h

lemma Qcand_hΔ1 {k : ℕ} {ε : ℝ} :
    2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) ≤ (1 / 8) * (Qcand k ε : ℝ) := by
  have hA : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  have hQ : 16 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1 ≤ (Qcand k ε : ℝ) := by
    rw [Qcand]
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_max_right (1 : ℝ) _) (le_max_left _ _)
  nlinarith

lemma Qcand_hΔ2 {k : ℕ} {ε : ℝ} :
    2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) < (1 - 2 * (1 / 8)) * (Qcand k ε : ℝ) := by
  have hA : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  have hQ : 2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * 4 / 3 + 1 ≤ (Qcand k ε : ℝ) := by
    rw [Qcand]
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  nlinarith

lemma Qcand_hbadQ {k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    2 * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1)
        * (AmaxLoc k : ℝ) * 2 ^ (3 * k) ≤ epsD k ε * (Qcand k ε : ℝ) := by
  have hA : (0 : ℝ) ≤ (AmaxLoc k : ℝ) := Nat.cast_nonneg _
  have h1 : 2 * ((k * 2 ^ (k - 1) : ℕ) : ℝ) * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1)
        * (AmaxLoc k : ℝ) * 2 ^ (3 * k) ≤ 2 * PsiK k
        * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ)
        * (2 : ℝ) ^ (3 * k) := by
    have h2 : (0 : ℝ) ≤ (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) := by positivity
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (3 * k) := by positivity
    have h4 : (0 : ℝ) ≤ (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ)
        * (2 : ℝ) ^ (3 * k) := mul_nonneg (mul_nonneg h2 hA) h3
    have h5 := mul_le_mul_of_nonneg_right (PsiK_ge k) h4
    nlinarith [h5]
  have hQ : hbadBound k ε ≤ (Qcand k ε : ℝ) := by
    rw [Qcand]
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_max_right (2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * 4 / 3 + 1) (hbadBound k ε))
      (le_max_right (max 1 (16 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1))
        (max (2 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) * 4 / 3 + 1) (hbadBound k ε)))
  have hD : 0 < epsD k ε := epsD_pos hε
  have h4 : epsD k ε * hbadBound k ε
      = 2 * PsiK k * (10 * (3 * (k : ℝ)) * (AmaxLoc k : ℝ) + 1) * (AmaxLoc k : ℝ)
        * (2 : ℝ) ^ (3 * k) := by
    rw [hbadBound]
    field_simp
  have h5 : epsD k ε * hbadBound k ε ≤ epsD k ε * (Qcand k ε : ℝ) :=
    mul_le_mul_of_nonneg_left hQ (le_of_lt hD)
  linarith

/-! ## 2. The window for the scale `R` -/

/-- `k · 2^{k-1}`, the number of linear forms. -/
noncomputable def Kk (k : ℕ) : ℕ := k * 2 ^ (k - 1)

/-- The lower bound `(log p - log (Q 2^{10L}))/(10L)` for `log R`. -/
noncomputable def ell (k Q p : ℕ) : ℝ :=
  (Real.log (p : ℝ) - Real.log ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))) / (10 * (Kk k : ℝ))

/-- The candidate scale `R = ⌈exp (ell)⌉`. -/
noncomputable def Rcand (k Q p : ℕ) : ℕ := ⌈Real.exp (ell k Q p)⌉₊

lemma Kk_pos {k : ℕ} (hk : 1 ≤ k) : 0 < Kk k := by
  rw [Kk]
  positivity

lemma PQ_pos {k Q : ℕ} (hQ : 1 ≤ Q) : 0 < (Q : ℝ) * (2 : ℝ) ^ (10 * Kk k) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  positivity

lemma ell_le_log_Rcand (k Q p : ℕ) : ell k Q p ≤ Real.log (Rcand k Q p : ℝ) := by
  have h : Real.exp (ell k Q p) ≤ (Rcand k Q p : ℝ) := by
    rw [Rcand]
    exact Nat.le_ceil _
  calc ell k Q p = Real.log (Real.exp (ell k Q p)) := (Real.log_exp _).symm
    _ ≤ Real.log (Rcand k Q p : ℝ) := Real.log_le_log (Real.exp_pos _) h

lemma eventually_log_ge (C : ℝ) : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → C ≤ Real.log (p : ℝ) := by
  refine ⟨⌈Real.exp C⌉₊ + 1, fun p hp => ?_⟩
  have h1 : Real.exp C ≤ (⌈Real.exp C⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈Real.exp C⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  push_cast at h2
  have h3 : Real.exp C < (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans (Real.exp_pos C) h3
  exact le_of_lt ((Real.lt_log_iff_exp_lt hp0).mpr h3)

lemma ratio_k_pow {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (2 : ℝ) ^ (k + 5) / (10 * (Kk k : ℝ)) = 32 / 5 := by
  have h1 : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ (k - 1) * (2 : ℝ) ^ 6 := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (Kk k : ℝ) = (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
    rw [Kk]
    push_cast
    ring
  rw [h1, h2]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have h20 : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
  field_simp
  norm_num

lemma le_of_log_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x ≤ Real.log y) : x ≤ y := by
  have h1 := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hx, Real.exp_log hy] at h1

lemma Rcand_pow_le {k Q p : ℕ} (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hell : 0 ≤ ell k Q p) :
    (Rcand k Q p : ℝ) ^ (10 * Kk k) ≤ (p : ℝ) / (Q : ℝ) := by
  have hKkr : (0 : ℝ) < (Kk k : ℝ) := by exact_mod_cast Kk_pos hk
  have hL10 : (0 : ℝ) < 10 * (Kk k : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hPXgt : (1 : ℝ) < (Q : ℝ) * (2 : ℝ) ^ (10 * Kk k) := by
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (10 * Kk k) := by
      have hL1 : 1 ≤ 10 * Kk k := by have := Kk_pos hk; omega
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (10 * Kk k) := pow_le_pow_right₀ (by norm_num) hL1
    nlinarith
  have hppos : (0 : ℝ) < (p : ℝ) := by
    by_contra hc
    push Not at hc
    have h0 : (p : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg p)
    have hell' : ell k Q p
        = -(Real.log ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))) / (10 * (Kk k : ℝ)) := by
      rw [ell, h0, Real.log_zero]
      ring
    rw [hell'] at hell
    have h2 : 0 < Real.log ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) := Real.log_pos hPXgt
    have h4 : -(Real.log ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))) / (10 * (Kk k : ℝ)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hL10
    linarith
  have hR : (Rcand k Q p : ℝ) ≤ 2 * Real.exp (ell k Q p) := by
    have h1 : (Rcand k Q p : ℝ) < Real.exp (ell k Q p) + 1 := by
      rw [Rcand]
      exact Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h2 : (1 : ℝ) ≤ Real.exp (ell k Q p) := by
      rw [Real.one_le_exp_iff]
      exact hell
    linarith
  have hstep : (Rcand k Q p : ℝ) ^ (10 * Kk k)
      ≤ (2 * Real.exp (ell k Q p)) ^ (10 * Kk k) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hR _
  have hexp : Real.exp ((10 * Kk k : ℕ) * ell k Q p)
      = (p : ℝ) / ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) := by
    have h1 : ((10 * Kk k : ℕ) : ℝ) * ell k Q p
        = Real.log (p : ℝ) - Real.log ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) := by
      have hcast : (((10 * Kk k : ℕ)) : ℝ) = 10 * (Kk k : ℝ) := by push_cast; ring
      rw [ell, hcast]
      field_simp
    rw [h1, Real.exp_sub, Real.exp_log hppos,
      Real.exp_log (by linarith : (0 : ℝ) < (Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))]
  have hfinal : (2 : ℝ) ^ (10 * Kk k)
      * ((p : ℝ) / ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))) = (p : ℝ) / (Q : ℝ) := by
    field_simp
  calc (Rcand k Q p : ℝ) ^ (10 * Kk k)
      ≤ (2 * Real.exp (ell k Q p)) ^ (10 * Kk k) := hstep
    _ = (2 : ℝ) ^ (10 * Kk k) * Real.exp ((10 * Kk k : ℕ) * ell k Q p) := by
        rw [mul_pow, ← Real.exp_nat_mul]
    _ = (2 : ℝ) ^ (10 * Kk k)
          * ((p : ℝ) / ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k))) := by rw [hexp]
    _ = (p : ℝ) / (Q : ℝ) := hfinal

lemma Rcand_side {k Q p : ℕ} (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hell : 0 ≤ ell k Q p) :
    (Rcand k Q p : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ) := by
  have h := Rcand_pow_le hk hQ hell
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hnat : Rcand k Q p ^ (10 * k * 2 ^ (k - 1)) * Q ≤ p := by
    have h2 : (Rcand k Q p : ℝ) ^ (10 * Kk k) * (Q : ℝ) ≤ (p : ℝ) := by
      rw [le_div_iff₀ hQ0] at h
      exact h
    rw [Kk] at h2
    have h3 : ((Rcand k Q p ^ (10 * (k * 2 ^ (k - 1))) * Q : ℕ) : ℝ) ≤ (p : ℝ) := by
      push_cast
      linarith [h2]
    have h4 : 10 * k * 2 ^ (k - 1) = 10 * (k * 2 ^ (k - 1)) := by ring
    rw [h4]
    exact_mod_cast h3
  have h1 : Rcand k Q p ^ (10 * k * 2 ^ (k - 1)) ≤ p / Q := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < Q)]
    exact hnat
  calc (Rcand k Q p : ℤ) ^ (10 * k * 2 ^ (k - 1))
      = ((Rcand k Q p ^ (10 * k * 2 ^ (k - 1)) : ℕ) : ℤ) := by push_cast; ring
    _ ≤ ((p / Q : ℕ) : ℤ) := by exact_mod_cast h1

/-- **The window for the scale `R`.** -/
theorem exists_R_window {k W : ℕ} {ε_box εw : ℝ} (hk : 1 ≤ k) (hW : 1 ≤ W)
    (hεw : 0 < εw) (hεb : 0 < ε_box) (Q : ℕ) (hQ : 1 ≤ Q) (Rc : ℝ) (hRc : 3 ≤ Rc) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p →
      Rc ≤ (Rcand k Q p : ℝ) ∧ 3 * k ≤ Rcand k Q p ∧ 1 < Rcand k Q p ∧
      Rcand k Q p ≤ p ∧ (W : ℝ) ≤ p ∧ (Q : ℝ) ≤ p ∧ (k.factorial : ℝ) < p ∧
      (Rcand k Q p : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ) ∧
      Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)
        ≤ (k : ℝ) * 2 ^ (k + 5) * Real.log (Rcand k Q p) ∧
      6 * (3 * (k : ℝ)) * (Real.log (Rcand k Q p)) ^ (k * 2 ^ (k - 1))
        ≤ ε_box * (Rcand k Q p : ℝ) ^ 6 ∧
      (∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
        4 * ((zbC a) ^ a * (EK a * stripBound W a))
          ≤ (ε_box / 2) * Real.log (Rcand k Q p) * Kc a) ∧
      (Rcand k Q p : ℝ) ≤ εw * (p : ℝ) := by
  classical
  set PQ : ℝ := (Q : ℝ) * (2 : ℝ) ^ (10 * Kk k) with hPQ
  have hPQpos : 0 < PQ := by rw [hPQ]; exact PQ_pos hQ
  have hKkpos : 0 < Kk k := Kk_pos hk
  have hKk0 : (0 : ℝ) < (Kk k : ℝ) := by exact_mod_cast hKkpos
  have hL10 : (0 : ℝ) < 10 * (Kk k : ℝ) := by linarith
  have hLten : (10 : ℝ) ≤ 10 * (Kk k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Kk k : ℝ) := by exact_mod_cast hKkpos
    linarith
  have hPQgt : (1 : ℝ) < PQ := by
    rw [hPQ]
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (10 * Kk k) := by
      have hL1 : 1 ≤ 10 * Kk k := by omega
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ (10 * Kk k) := pow_le_pow_right₀ (by norm_num) hL1
    nlinarith
  have hkpow : k * 2 ^ (k - 1) = Kk k := by rw [Kk]
  have hv : ∀ᶠ X : ℝ in Filter.atTop,
      6 * (3 * (k : ℝ)) * (Real.log X) ^ (Kk k) ≤ ε_box * X ^ (6 : ℝ) :=
    Commons.Analysis.Asymptotics.eventually_const_mul_log_pow_le_rpow
      (c := 6 * (3 * (k : ℝ))) (ε := ε_box) (r := 6) (by positivity) hεb (by norm_num) (Kk k)
  rw [Filter.eventually_atTop] at hv
  obtain ⟨X0, hX0⟩ := hv
  set Lsm : ℝ := ∑ a ∈ Finset.Icc 1 (Kk k),
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) / ((ε_box / 2) * Kc a) with hLsm
  have hLsm_ge : ∀ a ∈ Finset.Icc 1 (Kk k),
      4 * ((zbC a) ^ a * (EK a * stripBound W a)) / ((ε_box / 2) * Kc a) ≤ Lsm := by
    intro a ha
    rw [hLsm]
    refine Finset.single_le_sum (f := fun b => 4 * ((zbC b) ^ b * (EK b * stripBound W b))
      / ((ε_box / 2) * Kc b)) (fun b hb => ?_) ha
    have h1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hzb : (0 : ℝ) ≤ (zbC b) ^ b := pow_nonneg (le_of_lt (zbC_pos h1)) b
    have hEK : 0 < EK b := EK_pos b
    have hsb : 0 ≤ stripBound W b := stripBound_nonneg W b
    have hKc : 0 < Kc b := Kc_pos b
    positivity
  set Lreq : ℝ := max (max (Real.log Rc) (Real.log ((3 * k : ℕ) : ℝ)))
    (max (Real.log (max X0 1)) Lsm) with hLreq
  obtain ⟨P1, hP1⟩ := eventually_log_ge (10 * (Kk k : ℝ) * Lreq + Real.log PQ)
  obtain ⟨P2, hP2⟩ := eventually_log_ge
    ((5 / 27) * (Real.log (2 * εw * (W : ℝ) + 1) + (32 / 5) * Real.log PQ))
  obtain ⟨P3, hP3⟩ := eventually_log_ge (Real.log PQ)
  obtain ⟨P4, hP4⟩ := eventually_log_ge
    ((1 / 9) * (10 * Real.log 2 - 10 * Real.log εw - Real.log PQ + 1))
  obtain ⟨P5, hP5⟩ := eventually_log_ge (Real.log ((W : ℝ) + 1))
  obtain ⟨P6, hP6⟩ := eventually_log_ge (Real.log (Q : ℝ))
  obtain ⟨P7, hP7⟩ := eventually_log_ge (Real.log ((k.factorial : ℝ) + 1))
  obtain ⟨P8, hP8⟩ := eventually_log_ge (Real.log 3)
  refine ⟨P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8, fun p hp => ?_⟩
  have hp1 : P1 ≤ p := by omega
  have hp2 : P2 ≤ p := by omega
  have hp3 : P3 ≤ p := by omega
  have hp4 : P4 ≤ p := by omega
  have hp5 : P5 ≤ p := by omega
  have hp6 : P6 ≤ p := by omega
  have hp7 : P7 ≤ p := by omega
  have hp8 : P8 ≤ p := by omega
  have hlog1 : 10 * (Kk k : ℝ) * Lreq + Real.log PQ ≤ Real.log (p : ℝ) := hP1 p hp1
  have hlog2 : (5 / 27) * (Real.log (2 * εw * (W : ℝ) + 1) + (32 / 5) * Real.log PQ)
      ≤ Real.log (p : ℝ) := hP2 p hp2
  have hlog3 : Real.log PQ ≤ Real.log (p : ℝ) := hP3 p hp3
  have hlog4 : (1 / 9) * (10 * Real.log 2 - 10 * Real.log εw - Real.log PQ + 1)
      ≤ Real.log (p : ℝ) := hP4 p hp4
  have hlog5 : Real.log ((W : ℝ) + 1) ≤ Real.log (p : ℝ) := hP5 p hp5
  have hlog6 : Real.log (Q : ℝ) ≤ Real.log (p : ℝ) := hP6 p hp6
  have hlog7 : Real.log ((k.factorial : ℝ) + 1) ≤ Real.log (p : ℝ) := hP7 p hp7
  have hlog8 : Real.log 3 ≤ Real.log (p : ℝ) := hP8 p hp8
  have hp1pos : (0 : ℝ) < (p : ℝ) := by
    by_contra hc
    push Not at hc
    have h0 : (p : ℝ) = 0 := le_antisymm hc (Nat.cast_nonneg p)
    rw [h0, Real.log_zero] at hlog8
    have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
    linarith
  have hpge : PQ ≤ (p : ℝ) := by
    calc PQ = Real.exp (Real.log PQ) := (Real.exp_log hPQpos).symm
      _ ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.mpr hlog3
      _ = (p : ℝ) := Real.exp_log hp1pos
  have hell0 : 0 ≤ ell k Q p := by
    rw [ell]
    rw [show ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) = PQ by rw [hPQ]]
    exact div_nonneg (by linarith [hlog3]) (le_of_lt hL10)
  have hA : Lreq ≤ ell k Q p := by
    rw [ell]
    rw [show ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) = PQ by rw [hPQ]]
    rw [le_div_iff₀ hL10]
    linarith [hlog1]
  have hRpos : (0 : ℝ) < (Rcand k Q p : ℝ) := lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
  have hlogRc : Real.log Rc ≤ Real.log (Rcand k Q p : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hA (ell_le_log_Rcand k Q p))
  have hRA : Rc ≤ (Rcand k Q p : ℝ) :=
    le_of_log_le (by linarith) hRpos hlogRc
  have hlog3k : Real.log ((3 * k : ℕ) : ℝ) ≤ Real.log (Rcand k Q p : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hA (ell_le_log_Rcand k Q p))
  have h3k : 3 * k ≤ Rcand k Q p := by
    have h := le_of_log_le (by exact_mod_cast (by omega : 0 < 3 * k)) hRpos hlog3k
    exact_mod_cast h
  have hR1 : 1 < Rcand k Q p := by
    have : 1 ≤ 3 * k := by omega
    omega
  have hlogX0 : Real.log (max X0 1) ≤ Real.log (Rcand k Q p : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans hA (ell_le_log_Rcand k Q p))
  have hX0le : max X0 1 ≤ (Rcand k Q p : ℝ) :=
    le_of_log_le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hRpos hlogX0
  have hvR : 6 * (3 * (k : ℝ)) * (Real.log (Rcand k Q p)) ^ (k * 2 ^ (k - 1))
      ≤ ε_box * (Rcand k Q p : ℝ) ^ 6 := by
    rw [hkpow]
    have := hX0 _ (le_trans (le_max_left _ _) hX0le)
    have h6 : (Rcand k Q p : ℝ) ^ (6 : ℝ) = (Rcand k Q p : ℝ) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h6] at this
    exact this
  have hLsmle : Lsm ≤ Real.log (Rcand k Q p : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans hA (ell_le_log_Rcand k Q p))
  have hsmR : ∀ a : ℕ, 1 ≤ a → a ≤ k * 2 ^ (k - 1) →
      4 * ((zbC a) ^ a * (EK a * stripBound W a))
        ≤ (ε_box / 2) * Real.log (Rcand k Q p) * Kc a := by
    intro a ha1 ha2
    have hmem : a ∈ Finset.Icc 1 (Kk k) := by
      rw [Finset.mem_Icc]
      exact ⟨ha1, by rw [← hkpow]; exact ha2⟩
    have h1 := hLsm_ge a hmem
    have hK : 0 < (ε_box / 2) * Kc a := by
      have := Kc_pos a
      positivity
    have h4 : 4 * ((zbC a) ^ a * (EK a * stripBound W a)) ≤ Lsm * ((ε_box / 2) * Kc a) := by
      rw [div_le_iff₀ hK] at h1
      exact h1
    have h5 : Lsm * ((ε_box / 2) * Kc a)
        ≤ Real.log (Rcand k Q p : ℝ) * ((ε_box / 2) * Kc a) :=
      mul_le_mul_of_nonneg_right hLsmle hK.le
    have h6 : Real.log (Rcand k Q p : ℝ) * ((ε_box / 2) * Kc a)
        = (ε_box / 2) * Real.log (Rcand k Q p) * Kc a := by ring
    linarith [h4, h5, h6]
  have hsideR : (Rcand k Q p : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ) :=
    Rcand_side hk hQ hell0
  have hRp : Rcand k Q p ≤ p := by
    have h := Rcand_pow_le hk hQ hell0
    have h10L : 1 ≤ 10 * Kk k := by omega
    have hRle : (Rcand k Q p : ℝ) ≤ (Rcand k Q p : ℝ) ^ (10 * Kk k) := by
      have h1 : (Rcand k Q p : ℝ) ^ 1 ≤ (Rcand k Q p : ℝ) ^ (10 * Kk k) :=
        pow_le_pow_right₀ (by exact_mod_cast (le_of_lt hR1)) h10L
      simpa using h1
    have hQle : (p : ℝ) / (Q : ℝ) ≤ (p : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < Q))]
      have hq : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith [Nat.cast_nonneg (α := ℝ) p]
    have h2 : (Rcand k Q p : ℝ) ≤ (p : ℝ) := le_trans hRle (le_trans h hQle)
    exact_mod_cast h2
  have hudom : Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)
      ≤ (k : ℝ) * 2 ^ (k + 5) * Real.log (Rcand k Q p) := by
    have hp3 : (3 : ℝ) ≤ (p : ℝ) :=
      le_of_log_le (by norm_num : (0 : ℝ) < 3) hp1pos hlog8
    have hp1R : (1 : ℝ) ≤ (p : ℝ) := by linarith
    have hle1 : 2 * εw * (W : ℝ) * (p : ℝ) + 1 ≤ (2 * εw * (W : ℝ) + 1) * (p : ℝ) := by
      have hW0 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)
        ≤ Real.log ((2 * εw * (W : ℝ) + 1) * (p : ℝ)) :=
      Real.log_le_log (by positivity) hle1
    have h3 : Real.log ((2 * εw * (W : ℝ) + 1) * (p : ℝ))
        = Real.log (2 * εw * (W : ℝ) + 1) + Real.log (p : ℝ) :=
      Real.log_mul (by positivity) hp1pos.ne'
    have h4 : (k : ℝ) * 2 ^ (k + 5) * ell k Q p
        = (32 / 5) * (Real.log (p : ℝ) - Real.log PQ) := by
      have hPQ' : ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) = PQ := by rw [hPQ]
      have hell : ell k Q p = (Real.log (p : ℝ) - Real.log PQ) / (10 * (Kk k : ℝ)) := by
        rw [ell, hPQ']
      rw [hell, ← ratio_k_pow hk]
      ring
    have h5 : Real.log (2 * εw * (W : ℝ) + 1) + Real.log (p : ℝ)
        ≤ (32 / 5) * (Real.log (p : ℝ) - Real.log PQ) := by
      nlinarith [hlog2]
    have h7 : (k : ℝ) * 2 ^ (k + 5) * ell k Q p
        ≤ (k : ℝ) * 2 ^ (k + 5) * Real.log (Rcand k Q p) :=
      mul_le_mul_of_nonneg_left (ell_le_log_Rcand k Q p) (by positivity)
    linarith [h2, h3, h5, h4, h7]
  have hRε : (Rcand k Q p : ℝ) ≤ εw * (p : ℝ) := by
    have h1 : (Rcand k Q p : ℝ) ≤ 2 * Real.exp (ell k Q p) := by
      have ha : (Rcand k Q p : ℝ) < Real.exp (ell k Q p) + 1 := by
        rw [Rcand]; exact Nat.ceil_lt_add_one (Real.exp_pos _).le
      have hb : (1 : ℝ) ≤ Real.exp (ell k Q p) := by rw [Real.one_le_exp_iff]; exact hell0
      linarith
    have h3 : ell k Q p ≤ (Real.log (p : ℝ) - Real.log PQ) / 10 := by
      have h11 : (1 : ℝ) / (10 * (Kk k : ℝ)) ≤ 1 / 10 :=
        one_div_le_one_div_of_le (by norm_num) hLten
      have hell' : ell k Q p = (Real.log (p : ℝ) - Real.log PQ) * (1 / (10 * (Kk k : ℝ))) := by
        rw [ell]
        rw [show ((Q : ℝ) * (2 : ℝ) ^ (10 * Kk k)) = PQ by rw [hPQ]]
        ring
      rw [hell']
      have hnn : 0 ≤ Real.log (p : ℝ) - Real.log PQ := by linarith [hlog3]
      calc (Real.log (p : ℝ) - Real.log PQ) * (1 / (10 * (Kk k : ℝ)))
          ≤ (Real.log (p : ℝ) - Real.log PQ) * (1 / 10) := mul_le_mul_of_nonneg_left h11 hnn
        _ = (Real.log (p : ℝ) - Real.log PQ) / 10 := by ring
    have h4 : (Real.log (p : ℝ) - Real.log PQ) / 10
        ≤ Real.log εw + Real.log (p : ℝ) - Real.log 2 := by
      nlinarith [hlog4]
    have h5 : 2 * Real.exp (ell k Q p) ≤ εw * (p : ℝ) := by
      have h6 : (2 : ℝ) * Real.exp (ell k Q p)
          = Real.exp (Real.log 2 + ell k Q p) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
      have h7 : εw * (p : ℝ) = Real.exp (Real.log εw + Real.log (p : ℝ)) := by
        rw [Real.exp_add, Real.exp_log hεw, Real.exp_log hp1pos]
      rw [h6, h7]
      exact Real.exp_le_exp.mpr (by linarith [h3, h4])
    linarith [h1, h5]
  have hWle : (W : ℝ) ≤ (p : ℝ) := by
    have h := le_of_log_le (by positivity : (0 : ℝ) < (W : ℝ) + 1) hp1pos hlog5
    linarith
  have hQle : (Q : ℝ) ≤ (p : ℝ) :=
    le_of_log_le (by exact_mod_cast (by omega : 0 < Q)) hp1pos hlog6
  have hkfact : (k.factorial : ℝ) < (p : ℝ) := by
    have h := le_of_log_le (by positivity : (0 : ℝ) < (k.factorial : ℝ) + 1) hp1pos hlog7
    linarith
  exact ⟨hRA, h3k, hR1, hRp, hWle, hQle, hkfact, hsideR, hudom, hvR, hsmR, hRε⟩

/-! ## 3. The `B`-threshold for the numeric condition `B^{k-1}Σf < cd p²` -/

lemma eventually_bndGT_pow {k : ℕ} (hk : 1 ≤ k) {W : ℕ} (hW : 1 ≤ W) {cd εw : ℝ}
    (hcd : 0 < cd) (hεw : 0 < εw) :
    ∃ PB : ℕ, ∀ p : ℕ, PB ≤ p → ((Cmaj k)⁻¹ * bndGT W p εw) ^ k < cd * (p : ℝ) := by
  have hC : 0 < Cmaj k := by rw [Cmaj]; positivity
  set c' : ℝ := cd * (Cmaj k) ^ k with hc'
  have hc'pos : 0 < c' := by rw [hc']; positivity
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp
    (Commons.Analysis.Asymptotics.eventually_const_mul_log_pow_le_rpow
      (c := (2 : ℝ) ^ k) (ε := c' / 2) (r := 1) (by positivity) (by positivity) (by norm_num) k)
  refine ⟨max (⌈max X0 0⌉₊ + 1) (⌈max (2 * εw * (W : ℝ) + 1) 0⌉₊ + 1), fun p hp => ?_⟩
  have hpX : X0 ≤ (p : ℝ) := by
    have h1 : max X0 0 ≤ (⌈max X0 0⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈max X0 0⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (le_trans (le_max_left _ _) hp)
    push_cast at h2
    have h3 : X0 ≤ max X0 0 := le_max_left _ _
    linarith
  have hpL : 2 * εw * (W : ℝ) + 1 ≤ (p : ℝ) := by
    have h1 : max (2 * εw * (W : ℝ) + 1) 0 ≤ (⌈max (2 * εw * (W : ℝ) + 1) 0⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈max (2 * εw * (W : ℝ) + 1) 0⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (le_trans (le_max_right _ _) hp)
    push_cast at h2
    have h3 : 2 * εw * (W : ℝ) + 1 ≤ max (2 * εw * (W : ℝ) + 1) 0 := le_max_left _ _
    linarith
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
  have h2εW0 : (0 : ℝ) ≤ 2 * εw * (W : ℝ) := by positivity
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hlogle : Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) ≤ 2 * Real.log (p : ℝ) := by
    have hle : 2 * εw * (W : ℝ) * (p : ℝ) + 1 ≤ (p : ℝ) ^ 2 := by
      have h1 : (2 * εw * (W : ℝ) + 1) * (p : ℝ) ≤ (p : ℝ) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hpL (by linarith)
      nlinarith
    calc Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) ≤ Real.log ((p : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (p : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hlog0 : 0 ≤ Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) := by
    apply Real.log_nonneg
    have : (0 : ℝ) < 2 * εw * (W : ℝ) * (p : ℝ) := by positivity
    linarith
  have hpow : (Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)) ^ k < c' * (p : ℝ) := by
    have h1 : (Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)) ^ k ≤ (2 * Real.log (p : ℝ)) ^ k :=
      pow_le_pow_left₀ hlog0 hlogle k
    have h2 : (2 * Real.log (p : ℝ)) ^ k = (2 : ℝ) ^ k * (Real.log (p : ℝ)) ^ k := by rw [mul_pow]
    have h3 : (2 : ℝ) ^ k * (Real.log (p : ℝ)) ^ k ≤ (c' / 2) * (p : ℝ) := by
      have := hX0 (p : ℝ) hpX
      rwa [Real.rpow_one] at this
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    nlinarith [h3, hc'pos, hp0]
  have hbnd : bndGT W p εw
      = (Nat.totient W : ℝ) / (W : ℝ) * Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) := rfl
  have hφ : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (by omega : 0 < W))]
    exact_mod_cast Nat.totient_le W
  have hφ0 : 0 ≤ (Nat.totient W : ℝ) / (W : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbndle : bndGT W p εw ≤ Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) := by
    rw [hbnd]
    calc (Nat.totient W : ℝ) / (W : ℝ) * Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)
        ≤ 1 * Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hφ hlog0
      _ = Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) := one_mul _
  have hbnd0 : 0 ≤ bndGT W p εw := by rw [hbnd]; exact mul_nonneg hφ0 hlog0
  have hstep : ((Cmaj k)⁻¹ * bndGT W p εw) ^ k
      ≤ (Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)) ^ k / (Cmaj k) ^ k := by
    have h1 : ((Cmaj k)⁻¹ * bndGT W p εw) ^ k
        = ((Cmaj k) ^ k)⁻¹ * (bndGT W p εw) ^ k := by
      rw [mul_pow, inv_pow]
    rw [h1, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbnd0 hbndle k) (by positivity)
  have hc'eq : c' / (Cmaj k) ^ k = cd := by
    rw [hc']
    have hCk : ((Cmaj k) ^ k) ≠ 0 := by positivity
    field_simp
  calc ((Cmaj k)⁻¹ * bndGT W p εw) ^ k
      ≤ (Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1)) ^ k / (Cmaj k) ^ k := hstep
    _ < c' * (p : ℝ) / (Cmaj k) ^ k := by
        have hCk : (0 : ℝ) < (Cmaj k) ^ k := by positivity
        exact div_lt_div_of_pos_right hpow hCk
    _ = cd * (p : ℝ) := by rw [← hc'eq]; ring


/-! ## 4. The Green–Tao majorant interface `hP` -/

/-- **The Green–Tao majorant interface `hP`.** -/
theorem majorant_hP : ∀ (k : ℕ), 3 ≤ k → ∃ (δ : ℝ) (CmB : ℕ → ℕ → ℝ), 0 < δ ∧
    ∀ (cd : ℝ), 0 < cd → ∀ (ε : ℝ), 0 < ε →
    ∃ (P : ℕ), 0 < P ∧
    ∀ (p : ℕ) [Fact p.Prime], P ≤ p →
      ∃ (R W : ℕ) (B : ℝ), 1 < R ∧ 1 ≤ W ∧ 0 < B ∧
        KPseudorandom p k (nuGT R W p (1 / 8)) CmB ε ∧
        δ * (p : ℝ) ≤ ∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p (1 / 8) x ∧
        (∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p (1 / 8) x ≤ nuGT R W p (1 / 8) x) ∧
        (∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p (1 / 8) x ≤ B) ∧
        B ^ (k - 1) * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p (1 / 8) x) < cd * (p : ℝ) ^ 2 ∧
        (∀ x : ZMod p, fGT W p (1 / 8) x ≠ 0 →
          (1 / 8) * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * (1 / 8) * (p : ℝ) ∧
            Nat.Prime (W * x.val + 1)) := by
  intro k hk3
  obtain ⟨δ0, hδ0pos, hdens⟩ :=
    Commons.NumberTheory.Sieve.density_fGT_window (1 / 8) (by norm_num) (by norm_num)
  have hCmajpos : 0 < Cmaj k := by rw [Cmaj]; positivity
  refine ⟨δ0 / Cmaj k,
    (fun m q => max 1 (Dcmax m q + (Kmax m) ^ q * (2 * CwMoment (Ec m * q)))), ?_, ?_⟩
  · positivity
  · intro cd hcd ε hε
    set εw : ℝ := 1 / 8 with hεw
    have hεwpos : 0 < εw := by rw [hεw]; norm_num
    have hεw4 : 4 * εw ≤ 1 := by rw [hεw]; norm_num
    set εb : ℝ := epsB k ε with hεb
    have hεbpos : 0 < εb := by rw [hεb]; exact epsB_pos hε
    have hεb1 : εb ≤ 1 := by rw [hεb]; exact epsB_le_one k ε
    set εd : ℝ := epsD k ε with hεd
    have hεdpos : 0 < εd := by rw [hεd]; exact epsD_pos hε
    set Q : ℕ := Qcand k ε with hQdef
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Qcand_ge k ε
    obtain ⟨w, W, Rc, hWpos, hRc3, hwbig, hwdiv, hbox⟩ :=
      BoxAvg.exists_W_R_boxAvgGood k εb hεbpos (by omega)
    have hW1 : 1 ≤ W := hWpos
    obtain ⟨PR, hRspec⟩ := exists_R_window (k := k) (W := W) (ε_box := εb) (εw := εw)
      (by omega) hW1 hεwpos hεbpos Q hQ1 Rc hRc3
    obtain ⟨Pd, hPd⟩ := hdens W hW1
    obtain ⟨PB, hPB⟩ := eventually_bndGT_pow (k := k) (by omega) (W := W) hW1 hcd hεwpos
    refine ⟨max (max PR Pd) (max (max (Q + 1) (k.factorial + 1)) (max 3 (max 9 PB))),
      by positivity, ?_⟩
    intro p hpprime hpP
    haveI : Fact p.Prime := hpprime
    have hPR : PR ≤ p := by omega
    have hPd' : Pd ≤ p := by omega
    have hQp : Q ≤ p := by omega
    have hkfp : k.factorial < p := by omega
    have hp3 : 3 ≤ p := by omega
    have hp9 : 9 ≤ p := by omega
    have hPB' : PB ≤ p := by omega
    obtain ⟨hRA, h3k, hR1, hRp, hWle, hQle, hkfact', hsideQR, hudom, hvR, hsmR, hRε⟩ :=
      hRspec p hPR
    set R : ℕ := Rcand k Q p with hRdef
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    have hεp1 : 1 ≤ εw * (p : ℝ) := by
      rw [hεw]
      nlinarith
    have hWp : W ≤ p := by exact_mod_cast hWle
    haveI hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    -- the density estimate
    have hdens' : δ0 * (p : ℝ) ≤ ∑ x : ZMod p, fGT W p εw x := by
      have h := hPd p hPd' (Fact.out : p.Prime)
      simpa only [fGT] using h
    have hdens'' : (δ0 / Cmaj k) * (p : ℝ)
        ≤ ∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x := by
      have h1 : (Cmaj k)⁻¹ * (δ0 * (p : ℝ))
          ≤ (Cmaj k)⁻¹ * ∑ x : ZMod p, fGT W p εw x :=
        mul_le_mul_of_nonneg_left hdens' (by positivity)
      have h2 : (Cmaj k)⁻¹ * ∑ x : ZMod p, fGT W p εw x
          = ∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x := by
        rw [Finset.mul_sum]
      rw [h2] at h1
      have h3 : (δ0 / Cmaj k) * (p : ℝ) = (Cmaj k)⁻¹ * (δ0 * (p : ℝ)) := by
        rw [div_eq_inv_mul]; ring
      rw [h3]
      exact h1
    -- the uniform bound `bndGT`
    have hbndGTpos : 0 < bndGT W p εw := by
      have hφpos : 0 < (Nat.totient W : ℝ) / (W : ℝ) :=
        div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
      have hlogpos : 0 < Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) := by
        apply Real.log_pos
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hW0 : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
        nlinarith
      rw [bndGT]
      exact mul_pos hφpos hlogpos
    have hbndGT0 : 0 ≤ bndGT W p εw := hbndGTpos.le
    have hBpos : 0 < (Cmaj k)⁻¹ * bndGT W p εw := by positivity
    -- `fGT ≤ bndGT` pointwise
    have hfGT_le_bnd : ∀ x : ZMod p, fGT W p εw x ≤ bndGT W p εw := by
      intro x
      by_cases hwin : εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ)
      · exact fGT_le_bnd hεwpos.le hwin.2
      · rw [fGT, if_neg (fun h => hwin ⟨h.1, h.2.1⟩)]
        exact hbndGT0
    -- the domination
    have hfdom : ∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x ≤ nuGT R W p εw x := by
      intro x
      by_cases hzero : fGT W p εw x = 0
      · rw [hzero, mul_zero]
        exact nuGT_nonneg (by omega : 1 < R) x
      · obtain ⟨hx1, hx2, hprime⟩ := fGT_ne_zero_imp hzero
        have hRW : R < W * x.val + 1 := by
          have hW1R : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW1
          have hxv0 : (0 : ℝ) ≤ (x.val : ℝ) := Nat.cast_nonneg _
          have h1 : (x.val : ℝ) ≤ (W : ℝ) * (x.val : ℝ) := by nlinarith
          have h2 : εw * (p : ℝ) + 1 ≤ (W : ℝ) * (x.val : ℝ) + 1 := by linarith
          have h3 : (R : ℝ) ≤ εw * (p : ℝ) := hRε
          have h4 : (R : ℝ) < (W : ℝ) * (x.val : ℝ) + 1 := by linarith
          have h5 : ((W * x.val + 1 : ℕ) : ℝ) = (W : ℝ) * (x.val : ℝ) + 1 := by push_cast; ring
          rw [← h5] at h4
          exact_mod_cast h4
        have hbnd : Real.log ((W * x.val + 1 : ℕ) : ℝ)
            ≤ (k : ℝ) * 2 ^ (k + 5) * Real.log (R : ℝ) := by
          have hle : ((W * x.val + 1 : ℕ) : ℝ) ≤ 2 * εw * (W : ℝ) * (p : ℝ) + 1 := by
            have hW0 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
            push_cast
            nlinarith
          calc Real.log ((W * x.val + 1 : ℕ) : ℝ)
              ≤ Real.log (2 * εw * (W : ℝ) * (p : ℝ) + 1) :=
                Real.log_le_log (by positivity) hle
            _ ≤ (k : ℝ) * 2 ^ (k + 5) * Real.log (R : ℝ) := hudom
        have h := fGT_div_const_le_nuGT (R := R) (W := W) (p := p) (ε := εw) (x := x)
          (by omega) hR1 hRW hprime hbnd
        simpa only [Cmaj] using h
    -- the `B` bound
    have hBfd : ∀ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x ≤ (Cmaj k)⁻¹ * bndGT W p εw :=
      fun x => mul_le_mul_of_nonneg_left (hfGT_le_bnd x) (by positivity)
    -- the numeric condition
    have hBnum : ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
        * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x) < cd * (p : ℝ) ^ 2 := by
      have hs : ∑ x : ZMod p, fGT W p εw x ≤ (p : ℝ) * bndGT W p εw := by
        calc ∑ x : ZMod p, fGT W p εw x ≤ ∑ _x : ZMod p, bndGT W p εw :=
              Finset.sum_le_sum (fun x _ => hfGT_le_bnd x)
          _ = (p : ℝ) * bndGT W p εw := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hs2 : ∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x
          ≤ ((Cmaj k)⁻¹ * bndGT W p εw) * (p : ℝ) := by
        rw [← Finset.mul_sum]
        calc (Cmaj k)⁻¹ * ∑ x : ZMod p, fGT W p εw x
            ≤ (Cmaj k)⁻¹ * ((p : ℝ) * bndGT W p εw) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
          _ = ((Cmaj k)⁻¹ * bndGT W p εw) * (p : ℝ) := by ring
      have hBk : ((Cmaj k)⁻¹ * bndGT W p εw) ^ k < cd * (p : ℝ) := hPB p hPB'
      have hB0 : 0 ≤ (Cmaj k)⁻¹ * bndGT W p εw := hBpos.le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hpow : ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
          * (((Cmaj k)⁻¹ * bndGT W p εw) * (p : ℝ))
          = ((Cmaj k)⁻¹ * bndGT W p εw) ^ k * (p : ℝ) := by
        have hk1 : k - 1 + 1 = k := by omega
        rw [← mul_assoc, ← pow_succ, hk1]
      have h1 : ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
            * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x)
          ≤ ((Cmaj k)⁻¹ * bndGT W p εw) ^ k * (p : ℝ) := by
        have h4 : (0 : ℝ) ≤ ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1) := by positivity
        calc ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
              * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x)
            ≤ ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
              * (((Cmaj k)⁻¹ * bndGT W p εw) * (p : ℝ)) :=
                mul_le_mul_of_nonneg_left hs2 h4
          _ = ((Cmaj k)⁻¹ * bndGT W p εw) ^ k * (p : ℝ) := hpow
      have h2 : ((Cmaj k)⁻¹ * bndGT W p εw) ^ k * (p : ℝ) < cd * (p : ℝ) * (p : ℝ) := by
        have := mul_lt_mul_of_pos_right hBk hp0
        linarith [this]
      calc ((Cmaj k)⁻¹ * bndGT W p εw) ^ (k - 1)
            * (∑ x : ZMod p, (Cmaj k)⁻¹ * fGT W p εw x)
          ≤ ((Cmaj k)⁻¹ * bndGT W p εw) ^ k * (p : ℝ) := h1
        _ < cd * (p : ℝ) * (p : ℝ) := h2
        _ = cd * (p : ℝ) ^ 2 := by ring
    -- the support condition
    have hsupp : ∀ x : ZMod p, fGT W p εw x ≠ 0 →
        εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
          Nat.Prime (W * x.val + 1) := fun x hx => fGT_ne_zero_imp hx
    -- the linear forms condition
    have hsideZ : (R : ℤ) ^ (10 * (k * 2 ^ (k - 1))) ≤ (p : ℤ) := by
      have h1 := hsideQR
      have h2 : (10 * k * 2 ^ (k - 1)) = (10 * (k * 2 ^ (k - 1))) := by ring
      rw [h2] at h1
      refine le_trans h1 ?_
      exact_mod_cast (Nat.div_le_self p Q)
    have hLF : LinFormsCond p (nuGT R W p εw) (k * 2 ^ (k - 1)) (3 * k - 4) k ε := by
      refine Local.linFormsCond_nuGT_of_bounds (p := p) (k := k) (R := R) (W := W) (Q := Q)
        (ε_box := εb) (εw := εw) (ε := ε) (εbad := εd)
        hkfp (hbox R hRA) hQ1 hQp hWpos (le_of_lt hR1) hR1 hεbpos.le hεb1
        hεwpos (by rw [hεw]; norm_num) hεdpos.le hε ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact hsideQR
      · rw [hεw, hQdef]; exact Qcand_hΔ1
      · rw [hεw, hQdef]; exact Qcand_hΔ2
      · rw [hεb]; exact epsB_hsp1 hε
      · rw [hεb]; exact epsB_hsp2 hε
      · rw [hεd]; exact epsD_hsp3 hε
      · rw [hεd, hQdef]; exact Qcand_hbadQ hε
    have hCC : CorrCond p (nuGT R W p εw) (2 ^ (k - 1))
        (fun m q => max 1 (Dcmax m q + (Kmax m) ^ q * (2 * CwMoment (Ec m * q)))) := by
      refine corrCond_nuGT_uniform (k := k) (R := R) (W := W) (ε_box := εb) (εcorr := εb)
        (εw := εw) (by omega) (by omega) h3k hW1 hεbpos.le hεb1 hεbpos hεb1 hεwpos hεw4 hεp1
        hvR hsmR hsideZ hp3 hWp hRp
    exact ⟨R, W, (Cmaj k)⁻¹ * bndGT W p εw, hR1, hW1, hBpos, ⟨hLF, hCC⟩,
      hdens'', hfdom, hBfd, hBnum, hsupp⟩

end GYMaj
