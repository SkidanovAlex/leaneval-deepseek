import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Split

open Work.BoseFixB3

set_option linter.unusedVariables false

/-! ## Auxiliary facts about the two exponentials involved

`ellAt μ a = Kl · (μa)^{-1/2}` with `Kl = (μa³)^{-3/646}`, and
`kapAt μ a = (d²·ellAt μ a)^{-1}` with `d = (μa³)^{6/323}` (`Real.rpow`
throughout).  The dichotomy is a pure statement about `Real.rpow`: at a
non-positive base the exponent `-1/2` produces `0`, and at a positive base every
one of `(μa³)^{-3/646}`, `(μa)^{-1/2}`, `(μa³)^{6/323}` is positive. -/

/-- `x^(-1/2) = 0` for `x ≤ 0`: for `x < 0`, `Real.rpow_def_of_neg` gives
`x^y = exp (log x · y) · cos (y·π)` and `cos (-π/2) = 0`; at `x = 0`,
`Real.zero_rpow` applies since `-1/2 ≠ 0`. -/
lemma rpow_neg_half_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (-(1/2) : ℝ) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have hc : Real.cos ((-(1/2) : ℝ) * Real.pi) = 0 := by
      rw [show (-(1/2) : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg,
        Real.cos_pi_div_two]
    rw [hc, mul_zero]
  · rw [h, Real.zero_rpow (by norm_num : (-(1/2) : ℝ) ≠ 0)]

/-- `fsXp t c = t ^ (c/323)` is positive for a positive base. -/
lemma fsXp_pos_of_pos {t : ℝ} (ht : 0 < t) (c : ℝ) : 0 < Work.BoseBox.fsXp t c := by
  rw [Work.BoseBox.fsXp]; exact Real.rpow_pos_of_pos ht _

/-- `ellAt` unfolded to its two `Real.rpow` factors. -/
lemma ellAt_eq_fsXp (μ a : ℝ) :
    ellAt μ a = Work.BoseBox.fsXp (μ * a ^ 3) (-(3/2)) * (μ * a) ^ (-(1/2) : ℝ) := by
  simp only [ellAt, Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
    Work.BoseBox.fsParams]

/-- `kapAt` unfolded to `(d² ℓ)^{-1}` with `d = fsXp (μa³) 6` and `ℓ = ellAt μ a`. -/
lemma kapAt_eq_fsXp (μ a : ℝ) :
    kapAt μ a = ((Work.BoseBox.fsXp (μ * a ^ 3) 6) ^ 2 * ellAt μ a)⁻¹ := by
  simp only [kapAt, ellAt, Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
    Work.BoseBox.fsParams]

/-! `ellAt μ (a v) = Kl * (μ * a v)^(-1/2)` with `Kl = (μ*(a v)^3)^(-3/646)` (`Real.rpow`),
and `kapAt μ (a v) = ((fsParams …).d^2 * ellAt μ (a v))⁻¹` with `d = (μ*(a v)^3)^(6/323)`.
`Real.rpow_def_of_neg` gives `x^(-1/2) = |x|^(-1/2)*cos(-π/2) = 0` for `x < 0`, and `Real.zero_rpow`
gives `0^(-1/2) = 0`, so `μ * a v ≤ 0` forces `ellAt = 0`; for `μ * a v > 0` both `ellAt` and `kapAt`
are positive since `μ*(a v)^3 = (μ*a v)*(a v)^2 > 0`. -/
theorem ellKapDichotomy (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) :
    Work.BoseFixB3.ellAt μ (BoseGases.a v) = 0 ∨
      (0 < Work.BoseFixB3.ellAt μ (BoseGases.a v) ∧
        0 < Work.BoseFixB3.kapAt μ (BoseGases.a v)) := by
  set a := BoseGases.a v with ha
  by_cases hμa : μ * a ≤ 0
  · -- non-positive diluteness: the `-1/2`-power vanishes, hence `ellAt = 0`
    left
    rw [ellAt_eq_fsXp, rpow_neg_half_of_nonpos hμa, mul_zero]
  · -- positive diluteness: both factors are positive
    right
    have hμa' : 0 < μ * a := not_le.mp hμa
    have ha_ne : a ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hμa'; exact absurd hμa' (lt_irrefl 0)
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha_ne
    have ht : 0 < μ * a ^ 3 := by
      have hh : μ * a ^ 3 = (μ * a) * a ^ 2 := by ring
      rw [hh]; exact mul_pos hμa' ha2
    have hell : 0 < ellAt μ a := by
      rw [ellAt_eq_fsXp]
      exact mul_pos (fsXp_pos_of_pos ht _) (Real.rpow_pos_of_pos hμa' _)
    refine ⟨hell, ?_⟩
    rw [kapAt_eq_fsXp]
    exact inv_pos.mpr (mul_pos (pow_pos (fsXp_pos_of_pos ht 6) 2) hell)

end Work.BoseFixB3.Split
