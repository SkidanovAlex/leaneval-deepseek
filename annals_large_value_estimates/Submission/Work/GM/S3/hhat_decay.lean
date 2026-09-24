import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.hhat_defs
import Submission.Work.GM.S3.phi_iteratedDeriv
import Submission.Work.GM.S3.w2C_iteratedDeriv_bound
import Submission.Work.GM.S3.hfun_contDiff_compactSupport
import Submission.Work.GM.S3.fourier_decay_smooth

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (hfun hhat)

/-- The `k`-th derivative of the oscillatory factor `phi t u = u^{it}` is bounded by
`k! (1+|t|)^k ≤ j! (1+|t|)^j` on `[1,2]` (where `|u^{it}| = 1`). -/
theorem phi_iteratedDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (k : ℕ), k ≤ j → ∀ x ∈ Set.Icc (1 : ℝ) 2,
      ‖iteratedDeriv k (phi t) x‖ ≤ C * (1 + |t|) ^ j := by
  refine ⟨(j.factorial : ℝ), by positivity, ?_⟩
  intro t k hk x hx
  have hx1 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  rw [phi_iteratedDeriv t k hx1, norm_mul]
  have hprod : ‖∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))‖
      ≤ (1 + |t|) ^ j * (j.factorial : ℝ) := by
    have h1 : ‖∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))‖
        ≤ ∏ i ∈ Finset.range k, ((1 + |t|) * (1 + (i : ℝ))) := by
      refine le_trans (norm_prod_le _ _) (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) ?_)
      intro i hi
      have h2 : ‖Complex.I * (t : ℂ) - (i : ℂ)‖ ≤ |t| + (i : ℝ) := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
        rw [show ‖((t : ℝ) : ℂ)‖ = |t| from RCLike.norm_ofReal t]
      have h3 : |t| + (i : ℝ) ≤ (1 + |t|) * (1 + (i : ℝ)) := by
        have : (0 : ℝ) ≤ |t| * (i : ℝ) := mul_nonneg (abs_nonneg t) (Nat.cast_nonneg i)
        nlinarith
      exact h2.trans h3
    have h4 : ∏ i ∈ Finset.range k, ((1 + |t|) * (1 + (i : ℝ)))
        = (1 + |t|) ^ k * (k.factorial : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      congr 1
      have hfac : ∀ k : ℕ, (∏ i ∈ Finset.range k, (1 + (i : ℝ))) = (k.factorial : ℝ) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
            push_cast
            ring
      rw [hfac k]
    rw [h4] at h1
    refine h1.trans ?_
    have ht : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hk' : (k.factorial : ℝ) ≤ (j.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hk
    calc (1 + |t|) ^ k * (k.factorial : ℝ) ≤ (1 + |t|) ^ j * (k.factorial : ℝ) := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hk) (by positivity)
      _ ≤ (1 + |t|) ^ j * (j.factorial : ℝ) := by
          exact mul_le_mul_of_nonneg_left hk' (by positivity)
  have hexp : ‖Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ)).re
        = -(k : ℝ) * Real.log x := by
      simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
    rw [hre, Real.exp_le_one_iff]
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hlog, hk0]
  calc ‖∏ i ∈ Finset.range k, (Complex.I * (t : ℂ) - (i : ℂ))‖ *
        ‖Complex.exp ((Complex.I * (t : ℂ) - (k : ℂ)) * (Real.log x : ℂ))‖
      ≤ ((1 + |t|) ^ j * (j.factorial : ℝ)) * 1 := by
        exact mul_le_mul hprod hexp (norm_nonneg _) (by positivity)
    _ = (j.factorial : ℝ) * (1 + |t|) ^ j := by ring

/-- Every iterated derivative of `hfun t = w² u^{it}` is bounded by `C (1+|t|)^j`, uniformly
in the point (the `C^∞` factor `w²` contributes a constant and `u^{it}` contributes
`(1+|t|)^j` through the product rule). -/
theorem hfun_iteratedDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t x : ℝ), ‖iteratedDeriv j (hfun t) x‖ ≤ C * (1 + |t|) ^ j := by
  obtain ⟨D, hD, hDb⟩ := w2C_iteratedDeriv_bound j
  obtain ⟨E, hE, hEb⟩ := phi_iteratedDeriv_bound j
  refine ⟨2 ^ j * D * E, by positivity, ?_⟩
  intro t x
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · have hx1 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hw : ContDiffAt ℝ (j : ℕ∞) w2C x :=
      (w2C_contDiff.contDiffAt).of_le (by exact_mod_cast le_top)
    have hp : ContDiffAt ℝ (j : ℕ∞) (phi t) x :=
      (contDiffAt_phi t hx1).of_le (by exact_mod_cast le_top)
    have hmul := iteratedDeriv_mul (f := w2C) (g := phi t) (x := x) (n := j) hw hp
    have h1 : iteratedDeriv j (hfun t) x =
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℂ) * iteratedDeriv i w2C x * iteratedDeriv (j - i) (phi t) x := by
      rw [hfun_eq_mul, hmul]
    rw [h1]
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i w2C x * iteratedDeriv (j - i) (phi t) x‖
          ≤ (j.choose i : ℝ) * (D * (E * (1 + |t|) ^ j)) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hji : j - i ≤ j := Nat.sub_le _ _
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have h1i : ‖iteratedDeriv i w2C x‖ ≤ D := hDb i hij x
      have h2i : ‖iteratedDeriv (j - i) (phi t) x‖ ≤ E * (1 + |t|) ^ j := hEb t (j - i) hji x hx
      have hEj : 0 ≤ E * (1 + |t|) ^ j := by positivity
      calc (j.choose i : ℝ) * ‖iteratedDeriv i w2C x‖ * ‖iteratedDeriv (j - i) (phi t) x‖
          ≤ (j.choose i : ℝ) * D * (E * (1 + |t|) ^ j) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1i (by positivity)) h2i (norm_nonneg _)
              (by positivity)
        _ = (j.choose i : ℝ) * (D * (E * (1 + |t|) ^ j)) := by ring
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      norm_num
    rw [hsum]
    ring
  · have hzero : iteratedDeriv j (hfun t) x = 0 := by
      have hEqOn : Set.EqOn (hfun t) (fun _ : ℝ => (0 : ℂ)) (Set.Icc (1 : ℝ) 2)ᶜ := by
        intro y hy
        rw [hfun, Submission.LargeValues.bumpW_eq_zero_of_notMem (by simpa using hy)]
        simp
      have hder := Set.EqOn.iteratedDeriv_of_isOpen hEqOn isClosed_Icc.isOpen_compl j
      have hx' : x ∈ (Set.Icc (1 : ℝ) 2)ᶜ := by simpa using hx
      simpa only [iteratedDeriv_const, ite_self] using hder hx'
    rw [hzero, norm_zero]
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
    have h3 : (0 : ℝ) ≤ (1 + |t|) ^ j := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hD) hE) h3

/-- **GM Lemma 4.3.** For every `j : ℕ` there is `C > 0` such that for all real `t` and all
`ξ ≠ 0`, `‖hhat t ξ‖ ≤ C * (1 + |t|)^j / |ξ|^j`, where `hhat t ξ = ∫ e(-ξu) (w(u)^2 u^{it}) du`. -/
theorem hhat_decay (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t ξ : ℝ), ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j := by
  obtain ⟨Cf, hCf, hfour⟩ := fourier_decay_smooth j
  obtain ⟨Ch, hCh, hbound⟩ := hfun_iteratedDeriv_bound j
  refine ⟨Cf * (Ch + 1), by positivity, ?_⟩
  intro t ξ hξ
  have hB : ∀ x : ℝ, ‖iteratedDeriv j (hfun t) x‖ ≤ (Ch + 1) * (1 + |t|) ^ j := by
    intro x
    have h1 := hbound t x
    have h2 : 0 ≤ (1 + |t|) ^ j := by positivity
    nlinarith [hCh, h1, h2]
  have hvan : ∀ x : ℝ, x ∉ Set.Icc (1 : ℝ) 2 → hfun t x = 0 := by
    intro x hx
    rw [hfun, Submission.LargeValues.bumpW_eq_zero_of_notMem hx]
    simp
  have hξj : 0 < |ξ| ^ j := pow_pos (abs_pos.mpr hξ) j
  have hmain := hfour ((Ch + 1) * (1 + |t|) ^ j) (hfun t) (hfun_contDiff t) hvan hB ξ hξ
  change ‖FourierTransform.fourier (hfun t) ξ‖ ≤ Cf * (Ch + 1) * (1 + |t|) ^ j / |ξ| ^ j
  refine hmain.trans (le_of_eq ?_)
  rw [div_eq_div_iff (ne_of_gt hξj) (ne_of_gt hξj)]
  ring

end Work.GM.S3
