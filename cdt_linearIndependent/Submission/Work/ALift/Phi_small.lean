import Mathlib
import Submission.Work.ALift.bridge
import Submission.Work.CNum.log_norm_hauptH

/-!
# Area ALift — the a priori smallness of any lift `Φ` of `φ_A` near the origin

`Phi_small` is the step "`‖Φ(z)‖ ≤ 9/10` for `‖z‖ ≤ 1/25`" of the continuation argument for
`H = aH_A + bH_B + cH_C` along a lift `Φ` of `φ_A = h ∘ ψ_A`.

The two symmetrisation identities `Φ(z) + Φ(-z) = Φ(z)·Φ(-z) = φ_A(z²)` say that
`W = Φ(z)` is a root of `X² - yX + y`, `y = φ_A(z²)`, hence `‖W‖² = ‖y‖·‖W - 1‖ ≤ ‖y‖(‖W‖+1)`,
i.e. `‖W‖²/(‖W‖+1) ≤ ‖y‖`.  Since `t ↦ t²/(t+1)` is increasing on `[0,∞)`, the bound
`‖W‖ ≤ 9/10` follows from `‖y‖ < 81/190 = (9/10)²/(9/10+1)`.

For `‖y‖` we use the Schwarz lemma for the Theorem-A contour map (`‖ψ_A(w)‖ ≤ ‖w‖`, from the
`PsiAFacts` data, whence `‖ψ_A(z²)‖ ≤ ‖z‖² ≤ 1/625`) and the explicit product formula
`h(q) = -256 q ∏ₙ (1+qⁿ⁺¹)²⁴`, which on `‖q‖ ≤ 1/625` gives
`‖h(q)‖ ≤ 256·(1/625)·exp(1/26) ≤ (256/625)·(26/25) = 6656/15625 < 81/190`.
-/

namespace Work.ALift

open Submission.CDTPlan Metric
open scoped BigOperators

noncomputable section

/-! ## Schwarz lemma for the Theorem-A contour map -/

/-- Schwarz lemma for `ψ_A`: it is holomorphic on the unit disc with `ψ_A 0 = 0` and maps the
closed unit disc into the open unit disc, hence `‖ψ_A z‖ ≤ ‖z‖` for `‖z‖ ≤ 1`. -/
lemma psiA_norm_le (hP : PsiAFacts) : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖psiA z‖ ≤ ‖z‖ := by
  intro z hz
  rcases lt_or_eq_of_le hz with hlt | heq
  · have hd : DifferentiableOn ℂ psiA (ball 0 1) := hP.2.1
    have hmaps : Set.MapsTo psiA (ball 0 1) (closedBall (psiA 0) (1 : ℝ)) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      rw [mem_closedBall_iff_norm, hP.2.2.1, sub_zero]
      exact le_of_lt (hP.2.2.2.1 w (mem_closedBall_zero_iff.mpr (le_of_lt hw)))
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps (mem_ball_zero_iff.mpr hlt)
    rw [hP.2.2.1] at h
    rwa [dist_eq_norm, sub_zero, dist_eq_norm, sub_zero, div_one, one_mul] at h
  · rw [heq]
    exact le_of_lt (hP.2.2.2.1 z (by rw [mem_closedBall_zero_iff, heq]))

/-! ## The hauptmodul is tiny on `‖q‖ ≤ 1/625` -/

/-- Quantitative form of `h(q) = -256 q ∏ₙ (1+qⁿ⁺¹)²⁴` on the disc `‖q‖ ≤ 1/625`:
`‖hauptH q‖ ≤ 256·(1/625)·exp(1/26) ≤ (256/625)·(26/25) = 6656/15625`. -/
lemma hauptH_norm_le_small {q : ℂ} (hq : ‖q‖ ≤ 1 / 625) :
    ‖hauptH q‖ ≤ 6656 / 15625 := by
  have hq34 : ‖q‖ ≤ 3 / 4 := by norm_num at hq ⊢; linarith
  have hlt1 : ‖q‖ < 1 := by norm_num at hq ⊢; linarith
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0
    rw [hauptH]
    norm_num
  have hlog := Work.CNum.log_norm_hauptH hq34 hq0
  -- geometric summability of `‖q‖^{n+1}`
  have hgeom : Summable (fun n : ℕ => (‖q‖ : ℝ) ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => (‖q‖ : ℝ) ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg q) hlt1
    simpa [pow_succ', mul_comm] using h0.mul_left ‖q‖
  have hgnorm : Summable (fun n : ℕ => ‖q ^ (n + 1)‖) := by
    simpa [norm_pow] using hgeom
  have hlogsum : Summable (fun n : ℕ => Real.log ‖1 + q ^ (n + 1)‖) :=
    hgnorm.summable_log_norm_one_add
  -- each logarithmic term is at most the corresponding power of `‖q‖`
  have hble : ∀ n : ℕ, Real.log ‖1 + q ^ (n + 1)‖ ≤ (‖q‖ : ℝ) ^ (n + 1) := by
    intro n
    have hpowlt : ‖q ^ (n + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hlt1 (Nat.succ_ne_zero n)
    have hposn : 0 < ‖1 + q ^ (n + 1)‖ := by
      have h2 : (1 : ℝ) ≤ ‖1 + q ^ (n + 1)‖ + ‖q ^ (n + 1)‖ := by
        have h3 := norm_add_le (1 + q ^ (n + 1)) (-(q ^ (n + 1)))
        rw [show 1 + q ^ (n + 1) + -(q ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h3
        exact h3
      linarith
    have h1 : ‖1 + q ^ (n + 1)‖ ≤ 1 + ‖q‖ ^ (n + 1) := by
      calc ‖1 + q ^ (n + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (n + 1)‖ := norm_add_le _ _
        _ = 1 + ‖q‖ ^ (n + 1) := by rw [norm_one, norm_pow]
    calc Real.log ‖1 + q ^ (n + 1)‖ ≤ Real.log (1 + ‖q‖ ^ (n + 1)) :=
          Real.log_le_log hposn h1
      _ ≤ ‖q‖ ^ (n + 1) := by
          have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ‖q‖ ^ (n + 1) by positivity)
          linarith
  have hsum_le : ∑' n : ℕ, Real.log ‖1 + q ^ (n + 1)‖ ≤ ∑' n : ℕ, (‖q‖ : ℝ) ^ (n + 1) :=
    Summable.tsum_le_tsum hble hlogsum hgeom
  have hgeo_val : ∑' n : ℕ, (‖q‖ : ℝ) ^ (n + 1) = ‖q‖ / (1 - ‖q‖) := by
    rw [show (fun n : ℕ => (‖q‖ : ℝ) ^ (n + 1)) = (fun n => ‖q‖ * ‖q‖ ^ n) from
      funext (fun n => by rw [pow_succ', mul_comm])]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg q) hlt1]
    rw [div_eq_mul_inv]
  have hsum24 : ∑' n : ℕ, 24 * Real.log ‖1 + q ^ (n + 1)‖ ≤ 24 * (‖q‖ / (1 - ‖q‖)) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hsum_le.trans_eq hgeo_val) (by norm_num)
  have hlog_bound :
      Real.log ‖hauptH q‖ ≤ Real.log 256 + Real.log ‖q‖ + 24 * (‖q‖ / (1 - ‖q‖)) := by
    rw [hlog]; linarith
  -- `24 ‖q‖/(1-‖q‖) ≤ 1/26 ≤ log (26/25)`
  have hnum : 24 * (‖q‖ / (1 - ‖q‖)) ≤ Real.log (26 / 25) := by
    have hpos : (0 : ℝ) < 1 - ‖q‖ := by linarith
    have h1 : 24 * (‖q‖ / (1 - ‖q‖)) ≤ 1 / 26 := by
      rw [show 24 * (‖q‖ / (1 - ‖q‖)) = 24 * ‖q‖ / (1 - ‖q‖) by ring, div_le_iff₀ hpos]
      nlinarith [hq, norm_nonneg q]
    have h2 : (1 : ℝ) / 26 ≤ Real.log (26 / 25) := by
      have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ) / 25) (by norm_num)
      norm_num at h ⊢
      linarith
    linarith
  have hlogq : Real.log 256 + Real.log ‖q‖ ≤ Real.log (256 / 625) := by
    have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    rw [← Real.log_mul (by norm_num) (ne_of_gt hqpos)]
    apply Real.log_le_log (by positivity)
    nlinarith [hq, norm_nonneg q]
  have hfin : Real.log ‖hauptH q‖ ≤ Real.log (6656 / 15625) := by
    have hmul : Real.log (256 / 625) + Real.log (26 / 25) = Real.log (6656 / 15625) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    linarith
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hfin (not_le.mpr (Real.log_lt_log (by norm_num) hlt))

/-! ## The statement -/

theorem Phi_small (hP : Submission.CDTPlan.PsiAFacts) (Φ : ℂ → ℂ)
    (hL : Submission.CDTPlan.LiftData Submission.CDTPlan.phiA Φ) :
    ∀ z : ℂ, ‖z‖ ≤ 1 / 25 → ‖Φ z‖ ≤ 9 / 10 := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by norm_num at hz ⊢; linarith
  have hzmem : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz1
  obtain ⟨h1, h2⟩ := hL.2.1 z hzmem
  -- `y = φ_A(z²)` is tiny
  have hzsq1 : ‖z ^ 2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg z, hz]
  have hy : ‖phiA (z ^ 2)‖ ≤ 6656 / 15625 := by
    show ‖hauptH (psiA (z ^ 2))‖ ≤ 6656 / 15625
    apply hauptH_norm_le_small
    refine (psiA_norm_le hP (z ^ 2) hzsq1).trans ?_
    rw [norm_pow]
    nlinarith [norm_nonneg z, hz]
  -- `W = Φ z` is a root of `X² - yX + y`
  have hquad : (Φ z) ^ 2 = phiA (z ^ 2) * (Φ z - 1) := by
    have hzneg : Φ (-z) = phiA (z ^ 2) - Φ z := by
      linear_combination (norm := ring_nf) h1
    rw [hzneg] at h2
    linear_combination (norm := ring_nf) -h2
  have ht2 : ‖Φ z‖ ^ 2 ≤ ‖phiA (z ^ 2)‖ * (‖Φ z‖ + 1) := by
    have hmul := congrArg norm hquad
    rw [norm_pow, norm_mul] at hmul
    calc ‖Φ z‖ ^ 2 = ‖phiA (z ^ 2)‖ * ‖Φ z - 1‖ := hmul
      _ ≤ ‖phiA (z ^ 2)‖ * (‖Φ z‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have h4 := norm_sub_le (Φ z) 1
          simpa using h4
  -- monotonicity of `t ↦ t²/(t+1)`
  by_contra hcon
  rw [not_le] at hcon
  have hgoal : (81 : ℝ) / 190 ≤ ‖Φ z‖ ^ 2 / (‖Φ z‖ + 1) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖Φ z‖ + 1)]
    have h1' : 0 < ‖Φ z‖ - 9 / 10 := by linarith
    have h2' : 0 < 190 * ‖Φ z‖ + 90 := by linarith [norm_nonneg (Φ z)]
    nlinarith [mul_pos h1' h2']
  have hdiv : ‖Φ z‖ ^ 2 / (‖Φ z‖ + 1) ≤ ‖phiA (z ^ 2)‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖Φ z‖ + 1)]
    exact ht2
  have hge : (81 : ℝ) / 190 ≤ ‖phiA (z ^ 2)‖ := hgoal.trans hdiv
  have hlt : (6656 : ℝ) / 15625 < 81 / 190 := by norm_num
  linarith

end

end Work.ALift
