import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
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

theorem term1PointwiseCompl {N : ℕ} {Ks a c V : ℝ} (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks)
    (ha : 0 < a) (g : EuclideanSpace ℝ (Fin 3) → ℝ) {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * c)) :
    g q ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
        Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V))
      ≤ 2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2) := by
  -- `q` outside the ball of radius `2c` means `‖q‖ ≥ 2c`, so the spectral
  -- coefficient `[‖q‖ - c]₊²` satisfies `4 · fsKinCoeff c ‖q‖ ≥ ‖q‖²`.
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have hr2c : 2 * c ≤ ‖q‖ := by
    have h : (2 * c) ≤ dist q (0 : EuclideanSpace ℝ (Fin 3)) := by
      simpa [Metric.mem_ball] using hq
    rwa [dist_eq_norm, sub_zero] at h
  have hrpos : 0 < ‖q‖ := by linarith
  have hF : Submission.BoseGases.fsKinCoeff c ‖q‖ = (‖q‖ - c) ^ 2 :=
    Submission.BoseGases.fsKinCoeff_of_lt hc.le (by linarith)
  have hsq : ‖q‖ ^ 2 / 4 ≤ (‖q‖ - c) ^ 2 := by
    have h1 : (0 : ℝ) ≤ ‖q‖ / 2 - c := by linarith
    have h2 : (0 : ℝ) ≤ 3 * ‖q‖ / 2 - c := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hkey : ‖q‖ ^ 2 ≤ 4 * ((N : ℝ) + 1) *
      (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V) := by
    have hY : 0 ≤ 2 * Ks * a / V := by positivity
    have hb : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * (‖q‖ - c) ^ 2) = (‖q‖ - c) ^ 2 := by
      field_simp
    rw [hF]
    nlinarith [hsq, hb, hn.le, hY]
  -- clear both denominators and reduce to `1 ≤ 4 a A / ‖q‖²`
  set G := g q ^ 2 with hGdef
  set A := 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V with hAdef
  have hApos : 0 < V ^ 2 * 2 * A := by
    have h1 : 0 ≤ 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    have h2 : 0 ≤ 2 * Ks * a / V := by positivity
    have hA0 : 0 ≤ A := by rw [hAdef]; linarith
    positivity
  have hG : 0 ≤ G := by rw [hGdef]; positivity
  rw [div_le_iff₀ hApos]
  have hrhs : (2 * ((N : ℝ) + 1) / V ^ 2 * (g q ^ 2 / ‖q‖ ^ 2)) * (V ^ 2 * 2 * A)
      = 4 * ((N : ℝ) + 1) * A / ‖q‖ ^ 2 * G := by
    rw [hGdef, hAdef]
    field_simp
    ring
  rw [hrhs]
  have hge : 1 ≤ 4 * ((N : ℝ) + 1) * A / ‖q‖ ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖q‖ ^ 2)]
    nlinarith [hkey]
  exact le_mul_of_one_le_left hG hge

end Work.BoseFixB1B.pairRung
