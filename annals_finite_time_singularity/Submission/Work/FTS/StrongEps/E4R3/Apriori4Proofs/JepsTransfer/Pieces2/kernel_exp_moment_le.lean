import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.exp_moment_pt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exponential-moment bound for a compactly supported probability kernel

If `k ≥ 0` is a probability density on `ℝ × ℝ` whose support is contained in the `ℓ¹`-ball of
radius `2ε` (`ε ≤ 1`), then the exponential moment

  `∫ k(p) · 2 (e^{Cw |p|₁} − 1) e^{Cw |p|₁}`

(with `|p|₁ = |p.1| + |p.2|`) is bounded by `4 Cw ε e^{4Cw}`, hence by
`100 (Cw + 1) e^{4Cw} ε` (`Cw ≥ 0`).

The point is the elementary inequality `e^u − 1 ≤ u e^u` (`u ≥ 0`), applied on the support of
`k` only: off the support the integrand vanishes, and on it `u = Cw |p|₁ ≤ 2 Cw ε`, so

  `2 (e^u − 1) e^u ≤ 2 u e^{2u} ≤ 4 Cw ε e^{4Cw ε} ≤ 4 Cw ε e^{4Cw}`.

Multiplying by `k ≥ 0` and integrating, `∫ k = 1` turns this into the stated bound.  The purely
elementary pointwise inequality is `Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.exp_moment_pt`,
proved in a sibling module and imported here.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory Filter

theorem kernel_exp_moment_le {k : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hkmass : ∫ p : ℝ × ℝ, k p = 1)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) :
    (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
        * Real.exp (Cw * (|p.1| + |p.2|))))
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
  -- The pointwise domination: the kernel vanishes off its support, and on the support the
  -- elementary inequality `exp_moment_pt` applies.
  have hpt : ∀ p : ℝ × ℝ,
      k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
          * Real.exp (Cw * (|p.1| + |p.2|)))
        ≤ k p * (4 * Cw * ε * Real.exp (4 * Cw)) := by
    intro p
    by_cases hp : k p = 0
    · simp [hp]
    · have hr : |p.1| + |p.2| ≤ 2 * ε := hksupp p hp
      have hr0 : 0 ≤ |p.1| + |p.2| := add_nonneg (abs_nonneg p.1) (abs_nonneg p.2)
      have hu : 0 ≤ Cw * (|p.1| + |p.2|) := mul_nonneg hCw hr0
      have hu2 : Cw * (|p.1| + |p.2|) ≤ 2 * Cw * ε := by nlinarith [hCw, hr]
      exact mul_le_mul_of_nonneg_left
        (exp_moment_pt (Cw := Cw) (ε := ε) (u := Cw * (|p.1| + |p.2|)) hCw hε0 hε1 hu hu2)
        (hk0 p)
  -- The integrand is nonnegative.
  have hnn : 0 ≤ᵐ[volume] (fun p : ℝ × ℝ => k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
      * Real.exp (Cw * (|p.1| + |p.2|)))) := by
    filter_upwards with p
    have hm : 0 ≤ Cw * (|p.1| + |p.2|) :=
      mul_nonneg hCw (add_nonneg (abs_nonneg p.1) (abs_nonneg p.2))
    have h1 : 0 ≤ Real.exp (Cw * (|p.1| + |p.2|)) - 1 := sub_nonneg.mpr (Real.one_le_exp hm)
    have h2 : 0 ≤ Real.exp (Cw * (|p.1| + |p.2|)) := Real.exp_nonneg _
    exact mul_nonneg (hk0 p) (by positivity)
  have hchain : (∫ p : ℝ × ℝ, k p * (2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1)
        * Real.exp (Cw * (|p.1| + |p.2|))))
      ≤ ∫ p : ℝ × ℝ, k p * (4 * Cw * ε * Real.exp (4 * Cw)) :=
    integral_mono_of_nonneg hnn (hk.mul_const _) (Eventually.of_forall hpt)
  -- The constant integrand integrates to the constant, by `∫ k = 1`.
  have hconst : (∫ p : ℝ × ℝ, k p * (4 * Cw * ε * Real.exp (4 * Cw)))
      = 4 * Cw * ε * Real.exp (4 * Cw) := by
    rw [integral_mul_const, hkmass, one_mul]
  rw [hconst] at hchain
  refine le_trans hchain ?_
  calc 4 * Cw * ε * Real.exp (4 * Cw) = 4 * Cw * Real.exp (4 * Cw) * ε := by ring
    _ ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε := by
        apply mul_le_mul_of_nonneg_right _ hε0
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
