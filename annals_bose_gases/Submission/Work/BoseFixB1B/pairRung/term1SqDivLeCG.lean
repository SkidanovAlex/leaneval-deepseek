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

/-!
# `Work.BoseFixB1B.pairRung.term1SqDivLeCG`

The momentum-side bookkeeping of the pairing rung: for `q` **outside** the open ball of radius
`2c` the inverse-square weight `g q ^ 2 / ‖q‖ ^ 2` is dominated by the constant `D` times the
weighted content `g q ^ 2 / W` that the pairing chain produces, where

* `D = 2 V ^ 2 / (N + 1) + Ks a V / c ^ 2`   (the "denominator" the chain pays with), and
* `W = V ^ 2 * 2 * ( [fsKinCoeff c ‖q‖] / (N + 1) + 2 Ks a / V )`   (the weight of `term1`).

The whole content is the arithmetic comparison `W ≤ D * ‖q‖ ^ 2`, which splits into

* `fsKinCoeff c ‖q‖ ≤ ‖q‖ ^ 2`   (since `r ↦ (max (r - c) 0) ^ 2 ≤ r ^ 2` for `r ≥ 0`), paid by
  the `N`-slot `2 V ^ 2 / (N + 1)`, and
* `4 ≤ ‖q‖ ^ 2 / c ^ 2`   (from `2c ≤ ‖q‖`), paid by the `Ks a V / c ^ 2`-slot.

Positivity of `g q ^ 2` then gives the displayed inequality by a single division comparison.
-/

/-- the elementary division comparison used at the very end: if `0 < r`, `0 < W`, `0 ≤ G` and
`W ≤ D * r` then `G / r ≤ D * (G / W)`. -/
private lemma div_le_mul_div {G r W D : ℝ} (hr : 0 < r) (hW : 0 < W) (hG : 0 ≤ G)
    (h : W ≤ D * r) : G / r ≤ D * (G / W) := by
  rw [← mul_div_assoc, div_le_div_iff₀ hr hW]
  calc G * W ≤ G * (D * r) := mul_le_mul_of_nonneg_left h hG
    _ = (D * G) * r := by ring

theorem term1SqDivLeCG {N : ℕ} {Ks a c V : ℝ} (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks)
    (ha : 0 < a) (g : EuclideanSpace ℝ (Fin 3) → ℝ) {q : EuclideanSpace ℝ (Fin 3)}
    (hq : q ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (2 * c)) :
    g q ^ 2 / ‖q‖ ^ 2 ≤ (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) *
      (g q ^ 2 / (V ^ 2 * 2 * (1 / ((N : ℝ) + 1) *
        Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * a / V))) := by
  -- `q` is outside the open ball of radius `2c`, whence `2c ≤ ‖q‖`
  have hq2 : 2 * c ≤ ‖q‖ := by
    by_contra h
    exact hq (by simpa [Metric.mem_ball, dist_eq_norm] using lt_of_not_ge h)
  have hqpos : 0 < ‖q‖ := by linarith
  have hr : 0 < ‖q‖ ^ 2 := by positivity
  -- hence `4 c ^ 2 ≤ ‖q‖ ^ 2`
  have h4 : 4 * c ^ 2 ≤ ‖q‖ ^ 2 := by
    have h : (2 * c) ^ 2 ≤ ‖q‖ ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * c), abs_of_nonneg (norm_nonneg q)]
      exact hq2
    nlinarith [h]
  have hsl : 0 ≤ Submission.BoseGases.fsKinCoeff c ‖q‖ :=
    Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖
  -- the coefficient is dominated by the square of the momentum
  have hfs : Submission.BoseGases.fsKinCoeff c ‖q‖ ≤ ‖q‖ ^ 2 := by
    show (max (‖q‖ - c) 0) ^ 2 ≤ ‖q‖ ^ 2
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith) (norm_nonneg q)) 2
  -- positivity of the produced weight
  have hWpos : 0 < V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
      + 2 * Ks * a / V) := by
    have h1 : 0 < 2 * Ks * a / V := by positivity
    have h2 : 0 ≤ 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) hsl
    exact mul_pos (mul_pos (by positivity) (by norm_num)) (by linarith)
  -- the key comparison `W ≤ D * ‖q‖ ^ 2`
  have hW : V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        + 2 * Ks * a / V)
      ≤ (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) * ‖q‖ ^ 2 := by
    have h1 : 1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
        ≤ 1 / ((N : ℝ) + 1) * ‖q‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hfs (by positivity)
    have h1' : V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖)
        ≤ V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * ‖q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h2 : 4 ≤ ‖q‖ ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < c ^ 2)]
      linarith
    have h2' : V ^ 2 * 2 * (2 * Ks * a / V) ≤ (Ks * a * V / c ^ 2) * ‖q‖ ^ 2 := by
      have hmul : Ks * a * V * 4 ≤ Ks * a * V * (‖q‖ ^ 2 / c ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      calc V ^ 2 * 2 * (2 * Ks * a / V) = Ks * a * V * 4 := by
            field_simp
            ring
        _ ≤ Ks * a * V * (‖q‖ ^ 2 / c ^ 2) := hmul
        _ = (Ks * a * V / c ^ 2) * ‖q‖ ^ 2 := by ring
    calc V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * a / V)
        = V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖)
          + V ^ 2 * 2 * (2 * Ks * a / V) := by ring
      _ ≤ V ^ 2 * 2 * (1 / ((N : ℝ) + 1) * ‖q‖ ^ 2) + (Ks * a * V / c ^ 2) * ‖q‖ ^ 2 :=
          add_le_add h1' h2'
      _ = (2 * V ^ 2 / ((N : ℝ) + 1) + Ks * a * V / c ^ 2) * ‖q‖ ^ 2 := by ring
  exact div_le_mul_div hr hWpos (sq_nonneg (g q)) hW

end Work.BoseFixB1B.pairRung
