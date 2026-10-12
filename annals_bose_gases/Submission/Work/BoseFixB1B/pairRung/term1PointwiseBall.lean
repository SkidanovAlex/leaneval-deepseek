import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.BoxFrameAux
import Submission.Work.BoseFixB1.boxTauGen_mode_bound_meas
import Submission.Work.BoseFixB1B.pairMass_pos
import Submission.Work.BoseFixB1S.D1InputsB1
import Submission.Work.BoseFixB1S.boxPairIdSlidingB1
import Submission.Work.BoseFixB1S.chainIntegralQdep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B.pairRung

theorem term1PointwiseBall {N : ℕ} {Ks a c V : ℝ} (hV : 0 < V) (hKs : 0 < Ks) (ha : 0 < a)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hsup : ∀ q, |g q| ≤ Ks * a) {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * c)) :
    g q ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
        Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V))
      ≤ Ks * a / (4 * V) := by
  -- The only mathematical input needed: `fsKinCoeff` is a square of a `max` with `0`,
  -- hence nonnegative.  Then the denominator dominates `V ^ 2 * 2 * (2 * Ks * a / V) = 4 * V * Ks * a`,
  -- and the numerator is bounded by `(Ks * a) ^ 2`, which gives exactly the claim.
  have hk : 0 ≤ (1 / ((N : ℝ) + 1)) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
    mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
  have hD : 0 < V ^ 2 * 2 * ((1 / ((N : ℝ) + 1)) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V) := by
    have h1 : 0 < 2 * Ks * a / V := by positivity
    have h2 : 0 < V ^ 2 * 2 := by positivity
    exact mul_pos h2 (add_pos_of_nonneg_of_pos hk h1)
  rw [div_le_iff₀ hD]
  have hg : g q ^ 2 ≤ (Ks * a) ^ 2 := by
    have h := hsup q
    rw [abs_le] at h
    exact sq_le_sq' h.1 h.2
  have hrew : (Ks * a / (4 * V)) *
        (V ^ 2 * 2 * ((1 / ((N : ℝ) + 1)) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V))
      = (Ks * a) ^ 2 + (Ks * a) * V * ((1 / ((N : ℝ) + 1)) * Submission.BoseGases.fsKinCoeff c ‖q‖) / 2 := by
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hrew]
  have hnonneg : 0 ≤ (Ks * a) * V * ((1 / ((N : ℝ) + 1)) * Submission.BoseGases.fsKinCoeff c ‖q‖) / 2 := by
    positivity
  linarith

end Work.BoseFixB1B.pairRung
