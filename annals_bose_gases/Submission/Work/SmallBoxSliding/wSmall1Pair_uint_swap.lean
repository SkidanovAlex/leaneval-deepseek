import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.SmallBoxSliding.qLHSBAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxSliding

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

open Submission.BoseGases

/-- **The `u`-`y` exchange for the localised one-body kernel.**

Fubini (legitimate by the supplied joint integrability `hint`) reduces the
`u`-then-`y` iterated integral of `wSmall1Pair h M ℓ d · z ·` to the `y`-then-`u`
integral; the inner `u`-integral is then the renormalisation-cancellation
identity `chiSmallB_w1_pair_uint_cancel`,

    ∫_u wSmall1Pair h M ℓ d u z y du = χ_M(z/ℓ)·χ_M(y/ℓ)·g₀(z−y),

and a final commutativity of the three factors puts the `y`-weight last. -/
theorem wSmall1Pair_uint_swap {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (z : EuclideanSpace ℝ (Fin 3))
    (hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 z p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))) :
    (∫ u : EuclideanSpace ℝ (Fin 3), ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      = ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiScale ℓ z
            * (Submission.BoseGases.g0 v h (z - y) / Submission.BoseGases.convScale ℓ (z - y))
            * Submission.BoseGases.chiScale ℓ y := by
  rw [MeasureTheory.integral_integral_swap hint]
  apply integral_congr_ae
  filter_upwards with y
  rw [Submission.BoseGases.chiSmallB_w1_pair_uint_cancel hv_supp h hM hℓ hd hR z y]
  ring

end Work.SmallBoxSliding
