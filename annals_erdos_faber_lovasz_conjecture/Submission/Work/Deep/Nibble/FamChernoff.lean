import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted

/-!
# A weighted Chernoff (Bernstein) bound on the round space

This module proves `Work.Deep.Nibble.weighted_chernoff_up`, the exponential tail
bound for a *weighted* sum of independent Bernoulli indicators on the round space
`edgeMeasure 𝓖 p` (each edge kept independently with probability `p`).  It is the
tool that bounds the two exceptional events of `r2_Wfam_tail`; unlike the
bounded-differences (Hoeffding) bounds of `Work.Deep.Reed.Prob`, its exponent is
proportional to the *mean* `p ∑ w`, which is what a rare-edge regime needs.

The work is done by the finite weighted Bernstein bound
`Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted`, which is stated
for the product measure on `ι → Bool`; round deviations are read off against that
product form by unfolding `FinProb.prob` and `edgeMeasure_wt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Weighted Chernoff (Bernstein) bound, upper tail, on the round space.**  For
weights `0 ≤ w e ≤ C`, each edge kept independently with probability `p`, and
`t ≥ 0`,
`P(∑_e w e [ω e] - ∑_e p w e ≥ t) ≤ 2 exp (- t² / (2 C (μ + t/3)))`,
where `μ = ∑_e p w e`. -/
theorem weighted_chernoff_up (𝓖 : Set (Set V)) {p C : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hC : 0 ≤ C) (w : 𝓖 → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hwr : ∀ e, w e ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    (edgeMeasure 𝓖 p hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ (∑ e : 𝓖, if ω e then w e else 0) - ∑ e : 𝓖, p * w e}
      ≤ 2 * Real.exp (- t ^ 2 / (2 * C * ((∑ e : 𝓖, p * w e) + t / 3))) := by
  classical
  have htwo := Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted
    (p := fun _ : 𝓖 => p) (fun _ => hp0) (fun _ => hp1) (X := w) hw0 hC hwr ht
  have hL : (edgeMeasure 𝓖 p hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ (∑ e : 𝓖, if ω e then w e else 0) - ∑ e : 𝓖, p * w e}
      = ∑ s : 𝓖 → Bool, (∏ e : 𝓖, (if s e then p else 1 - p)) *
          (if t ≤ (∑ e : 𝓖, if s e then w e else 0) - ∑ e : 𝓖, p * w e then (1 : ℝ) else 0) := by
    rw [FinProb.prob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edgeMeasure_wt]
    by_cases h : t ≤ (∑ e : 𝓖, if i e then w e else 0) - ∑ e : 𝓖, p * w e
    · simp only [h, Set.mem_setOf_eq, if_true, mul_one]
    · simp only [h, Set.mem_setOf_eq, if_false, mul_zero]
  rw [hL]
  refine le_trans (Finset.sum_le_sum fun s _ => ?_) htwo
  have hw' : (0 : ℝ) ≤ ∏ e : 𝓖, (if s e then p else 1 - p) := by
    refine Finset.prod_nonneg fun e _ => ?_
    by_cases h : s e <;> simp [h, hp0, hp1]
  refine mul_le_mul_of_nonneg_left ?_ hw'
  by_cases h : t ≤ (∑ e : 𝓖, if s e then w e else 0) - ∑ e : 𝓖, p * w e
  · rw [if_pos h, if_pos (le_trans h (le_abs_self _))]
  · rw [if_neg h]
    split_ifs <;> norm_num

end Work.Deep.Nibble
