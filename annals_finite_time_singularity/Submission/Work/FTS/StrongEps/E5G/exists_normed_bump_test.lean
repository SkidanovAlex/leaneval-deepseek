import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.RingTheory.Finiteness.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A normalised smooth bump in `ℝ × ℝ` supported in a prescribed ball

Mathlib's `ContDiffBump` machinery provides a `C^∞` function `b` with

* `0 ≤ b x ≤ 1`,
* `b = 1` on `Metric.closedBall c b.rIn`,
* `support b = Metric.ball c b.rOut`,

and its normalisation `b.normed volume` has integral `1` and the same support.  Choosing the
centre `c = q` and the radii `rIn = δ/4`, `rOut = δ/2` produces the required bump: its support is
`Metric.ball q (δ/2)`, which is contained both in `Metric.ball q δ` and in
`Metric.ball q (ρ/2) ⊆ Metric.ball q ρ` because `δ ≤ ρ/2`.  Consequently the integral over
`Metric.closedBall q (ρ/2)` agrees with the total integral `1`.
-/

namespace Work.FTS.StrongEps.E5G

open MeasureTheory Metric

lemma exists_normed_bump_test (q : ℝ × ℝ) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ / 2) :
    ∃ ψ : ℝ × ℝ → ℝ,
      (∀ n : ℕ, ContDiff ℝ n ψ) ∧ HasCompactSupport ψ ∧ (∀ p, 0 ≤ ψ p) ∧ (∫ p, ψ p) = 1 ∧
        (∀ p, ψ p ≠ 0 → dist p q < δ) ∧ (∀ p, δ ≤ dist p q → ψ p = 0) ∧
        (∫ p in Metric.closedBall q (ρ / 2), ψ p) = 1 ∧ (∀ p, ψ p ≠ 0 → p ∈ Metric.ball q ρ) := by
  -- The support radius `δ/2` stays below `ρ`.
  have hδ2ρ : δ / 2 < ρ := by
    have h1 : δ / 2 ≤ ρ / 4 := by linarith [hδρ]
    have h2 : ρ / 4 < ρ := div_lt_self hρ (by norm_num)
    linarith
  -- The bump with centre `q` and radii `δ/4 < δ/2`; its support is `ball q (δ/2)`.
  set b : ContDiffBump q := ⟨δ / 4, δ / 2, by linarith, by linarith⟩ with hb
  have hb_rOut : b.rOut = δ / 2 := rfl
  -- Everything is supported in `ball q (δ/2)`.
  have hsupp : ∀ p, b.normed volume p ≠ 0 → dist p q < δ / 2 := by
    intro p hp
    have h1 : p ∈ Function.support (b.normed volume) := Function.mem_support.mpr hp
    rw [b.support_normed_eq, mem_ball] at h1
    simpa [hb_rOut] using h1
  refine ⟨b.normed volume, fun n => b.contDiff_normed, b.hasCompactSupport_normed,
    fun p => b.nonneg_normed p, b.integral_normed, ?_, ?_, ?_, ?_⟩
  · -- support inside `ball q δ`
    intro p hp
    have h1 := hsupp p hp
    linarith
  · -- vanishing outside `ball q δ`
    intro p hp
    by_contra h
    have h1 := hsupp p h
    linarith
  · -- the integral over `closedBall q (ρ/2)` is the total integral, namely `1`
    have hset : ∫ p in Metric.closedBall q (ρ / 2), b.normed volume p
        = ∫ p, b.normed volume p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
      by_contra hne
      have h1 := hsupp p hne
      have h2 : ¬ dist p q ≤ ρ / 2 := by
        simpa [Metric.mem_closedBall] using hp
      linarith
    rw [hset, b.integral_normed]
  · -- support inside `ball q ρ`
    intro p hp
    have h1 := hsupp p hp
    rw [Metric.mem_ball]
    linarith [h1, hδ2ρ]

end Work.FTS.StrongEps.E5G
