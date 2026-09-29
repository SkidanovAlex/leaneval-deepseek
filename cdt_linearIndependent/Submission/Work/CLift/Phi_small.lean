import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CLift.psiC_schwarz
import Submission.Work.CNum.log_norm_hauptH

/-!
# Area CLift — the a priori smallness of any lift `Φ` of `φ_C` near the origin

The statement `Phi_small` is the step "`|Φ(z)| ≤ 0.02` for `|z| ≤ 10⁻³`" of the continuation
argument for `P` along a lift `Φ` of `φ_C = h ∘ ψ_C`.

Given the two symmetrisation identities
`Φ(z) + Φ(-z) = φ_C(z²) = Φ(z)·Φ(-z)`,
`W = Φ(z)` is a root of the quadratic `W² - yW + y = 0` with `y = φ_C(z²)`, so
`‖W‖² = ‖y‖·‖W - 1‖ ≤ ‖y‖·(‖W‖ + 1)`.  For `‖z‖ ≤ 10⁻³` the Schwarz lemma for `ψ_C`
(`psiC_schwarz`) gives `‖y‖ = ‖h(ψ_C(z²))‖ ≤ 3·10⁻⁴` (via the explicit product formula for `h`),
and the quadratic bound then yields `‖W‖ ≤ 1/50`.
-/

namespace Work.CLift

open Submission.CDTPlan Metric
open scoped BigOperators

noncomputable section

/-- `h` is tiny near the origin: `‖q‖ ≤ (3/4)·10⁻⁶` forces `‖hauptH q‖ ≤ 3·10⁻⁴`.

This is the quantitative form of `h(q) = -256 q ∏(1 + qⁿ⁺¹)²⁴` needed below: the infinite
product differs from `1` by less than `18/41`, while `256·(3/4)·10⁻⁶ = 1.92·10⁻⁴`. -/
lemma hauptH_small {q : ℂ} (hq : ‖q‖ ≤ 3 / 4 * 10 ^ (-6 : ℤ)) :
    ‖hauptH q‖ ≤ 3 / 10 ^ 4 := by
  have hqr : ‖q‖ ≤ (3:ℝ) / 4000000 := by
    norm_num at hq ⊢; exact hq
  rcases eq_or_ne q 0 with hq0 | hq0
  · subst hq0
    rw [hauptH]; norm_num
  have hq34 : ‖q‖ ≤ 3 / 4 := by norm_num at hqr ⊢; linarith
  have hlt1 : ‖q‖ < 1 := by norm_num at hqr ⊢; linarith
  have hlog := Work.CNum.log_norm_hauptH hq34 hq0
  -- the perturbed geometric series is summable
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
      have h2 : (1:ℝ) ≤ ‖1 + q ^ (n + 1)‖ + ‖q ^ (n + 1)‖ := by
        have h3 := norm_add_le (1 + q ^ (n + 1)) (-(q ^ (n + 1)))
        rw [show 1 + q ^ (n + 1) + -(q ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h3
        exact h3
      linarith
    have h1 : ‖1 + q ^ (n + 1)‖ ≤ 1 + ‖q‖ ^ (n + 1) := by
      calc ‖1 + q ^ (n + 1)‖ ≤ ‖(1:ℂ)‖ + ‖q ^ (n + 1)‖ := norm_add_le _ _
        _ = 1 + ‖q‖ ^ (n + 1) := by rw [norm_one, norm_pow]
    calc Real.log ‖1 + q ^ (n + 1)‖ ≤ Real.log (1 + ‖q‖ ^ (n + 1)) :=
          Real.log_le_log hposn h1
      _ ≤ ‖q‖ ^ (n + 1) := by
          have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + ‖q‖ ^ (n + 1) by positivity)
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
  have hnum : 24 * (‖q‖ / (1 - ‖q‖)) ≤ 18 / 41 := by
    have hhalf : (1:ℝ) / 2 ≤ 1 - ‖q‖ := by norm_num at hqr ⊢; linarith
    have hposd : (0:ℝ) < 1 - ‖q‖ := by linarith
    rw [show 24 * (‖q‖ / (1 - ‖q‖)) = 24 * ‖q‖ / (1 - ‖q‖) by ring, div_le_iff₀ hposd]
    nlinarith [hqr, norm_nonneg q]
  have hlog256q : Real.log 256 + Real.log ‖q‖ ≤ Real.log (192 / 1000000) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt (norm_pos_iff.mpr hq0))]
    apply Real.log_le_log (by positivity)
    nlinarith [hqr]
  have hlogbig : Real.log ((192:ℝ) / 1000000) + 18 / 41 ≤ Real.log ((3:ℝ) / 10 ^ 4) := by
    have hlogmul : Real.log ((192:ℝ) / 1000000) + Real.log ((25:ℝ) / 16) =
        Real.log ((3:ℝ) / 10 ^ 4) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have hlogge : (18:ℝ) / 41 ≤ Real.log ((25:ℝ) / 16) := by
      have h := Real.le_log_one_add_of_nonneg (x := (9:ℝ) / 16) (by norm_num)
      norm_num at h ⊢
      linarith
    linarith
  have hfin : Real.log ‖hauptH q‖ ≤ Real.log ((3:ℝ) / 10 ^ 4) := by linarith
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hfin (not_le.mpr (Real.log_lt_log (by norm_num) hlt))

/-- Any lift `Φ` of `φ_C = h ∘ ψ_C` (i.e. satisfying `Φ z + Φ(-z) = Φ z · Φ(-z) = φ_C(z²)`)
satisfies `‖Φ z‖ ≤ 1/50` for `‖z‖ ≤ 1/1000`. -/
theorem Phi_small (hM : HauptFacts) (hP : PsiCFacts) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2)) :
    ∀ z : ℂ, ‖z‖ ≤ 1 / 1000 → ‖Φ z‖ ≤ 1 / 50 := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by norm_num at hz ⊢; linarith
  have hzmem : z ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; exact hz1
  obtain ⟨h1, h2⟩ := hΦ z hzmem
  -- `y = φ_C(z²)` is tiny
  have hy : ‖phiC (z^2)‖ ≤ 3/10^4 := by
    show ‖hauptH (psiC (z^2))‖ ≤ 3/10^4
    apply hauptH_small
    have hzsq1 : ‖z^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg z, hz]
    refine (psiC_schwarz hP (z^2) hzsq1).trans ?_
    have hzsq_le : ‖z^2‖ ≤ (10:ℝ) ^ (-6:ℤ) := by
      rw [norm_pow]
      calc ‖z‖ ^ 2 ≤ ((1:ℝ)/1000) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
        _ = (10:ℝ) ^ (-6:ℤ) := by norm_num
    exact mul_le_mul_of_nonneg_left hzsq_le (by norm_num)
  -- `W = Φ z` is a root of `X² - yX + y`
  have hquad : (Φ z)^2 = phiC (z^2) * (Φ z - 1) := by
    have hzneg : Φ (-z) = phiC (z^2) - Φ z := by linear_combination (norm := ring_nf) h1
    rw [hzneg] at h2
    linear_combination (norm := ring_nf) -h2
  -- hence `‖W‖² ≤ ‖y‖(‖W‖ + 1)`
  have ht2 : ‖Φ z‖ ^ 2 ≤ ‖phiC (z^2)‖ * (‖Φ z‖ + 1) := by
    have hmul := congrArg norm hquad
    rw [norm_pow, norm_mul] at hmul
    calc ‖Φ z‖ ^ 2 = ‖phiC (z^2)‖ * ‖Φ z - 1‖ := hmul
      _ ≤ ‖phiC (z^2)‖ * (‖Φ z‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have h4 := norm_sub_le (Φ z) 1
          simpa using h4
  nlinarith [ht2, hy, norm_nonneg (Φ z),
    mul_le_mul_of_nonneg_right hy (by positivity : (0:ℝ) ≤ ‖Φ z‖ + 1)]

end

end Work.CLift
