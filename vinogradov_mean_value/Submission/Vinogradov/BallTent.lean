/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.BallAbsorb
import Submission.Vinogradov.AsymBilinear
import Submission.Vinogradov.CurveLayer

/-!
# The ball tent, the ball average, and the localised decoupling predicate

GLYZ's Corollary 3.7 (arXiv:1912.09798) is the *localised* form of Lemma 3.6:  the `L^{p_l}`
norm of the sum of the pieces is controlled not only in `L^{p_l}`, but in `L^{p_l}` against a
tent adapted to a ball of the critical radius `δ^{-l}`, with the pieces measured in the same
weighted norm.  This module fixes the vocabulary:

* `ballTent l A c R` — the `L¹`-normalised tent `|B|^{-1}(1 + dist(x,B)/R)^{-A}` adapted to the
  ball `B = Metric.ball c R` (the radius `R` plays the role of `δ^{-l}`);
* `ballAvg p c R F` — the average of `‖F‖^p` over `B` (the paper's `⍺_B |F|^p`);
* `CurveDecLoc l D m lam A C` — the localised decoupling inequality for a curve `D` of degree
  `l` at scale `m`, with plate enlargement `lam` and exponents `(A, C)`.

The main theorem of the companion module (`LocalisedDecoupling.lean`) is
`curveDecLoc_of_curveDec`: the localised inequality follows from the global one
(`CurveDec`) at twice the enlargement, by multiplying the pieces with a bump whose Fourier
transform is supported in a ball of radius `≍ 1/R` (the ball absorption of `BallAbsorb.lean`).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The ball tent -/

/-- The `L¹`-normalised tent adapted to the ball `Metric.ball c R`:
`Φ_B x = |B|^{-1} (1 + dist(x,B)/R)^{-A}`. -/
noncomputable def ballTent (l : ℕ) (A : ℝ) (c : E l) (R : ℝ) : E l → ℝ≥0∞ :=
  fun x => (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
    * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A))

lemma ballTent_apply (l : ℕ) (A : ℝ) (c : E l) (R : ℝ) (x : E l) :
    ballTent l A c R x = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
      * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := rfl

/-- The tent is nonnegative. -/
lemma ballTent_nonneg (l : ℕ) (A : ℝ) (c : E l) (R : ℝ) (x : E l) :
    0 ≤ ballTent l A c R x := by
  rw [ballTent_apply]
  positivity

/-- **The defining relation of the tent**: multiplying the tent by the volume of the ball
recovers the un-normalised tent `(1 + dist(x,B)/R)^{-A}`. -/
lemma ofReal_volume_mul_ballTent (l : ℕ) (A : ℝ) (c : E l) {R : ℝ} (hR : 0 < R) (x : E l) :
    ENNReal.ofReal (volume (Metric.ball c R)).toReal * ballTent l A c R x
      = ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by
  rw [ballTent_apply]
  have hpos : 0 < volume (Metric.ball c R) := Metric.measure_ball_pos (μ := volume) c hR
  have hne : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos hpos.ne' measure_ball_lt_top.ne
  have htop : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← mul_assoc, ENNReal.mul_inv_cancel hne htop, one_mul]

/-- On the ball, the tent is bounded below by `|B|^{-1}`. -/
lemma le_ballTent_of_mem (l : ℕ) (A : ℝ) (c : E l) {R : ℝ} {x : E l}
    (hx : x ∈ Metric.ball c R) :
    (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹ ≤ ballTent l A c R x := by
  rw [ballTent_apply]
  refine le_mul_of_one_le_right (by positivity) ?_
  refine ENNReal.one_le_ofReal.mpr ?_
  have h0 : Metric.infDist x (Metric.ball c R) = 0 := Metric.infDist_zero_of_mem hx
  rw [h0, zero_div, add_zero, Real.one_rpow]

/-! ## 2. The ball average -/

/-- The average of `‖F‖^p` over the ball `Metric.ball c R` (the paper's `⍺_B |F|^p`). -/
noncomputable def ballAvg (p : ℝ) {l : ℕ} (c : E l) (R : ℝ) (F : E l → ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
    * ∫⁻ x in Metric.ball c R, (‖F x‖₊ : ℝ≥0∞) ^ p

lemma ballAvg_apply (p : ℝ) {l : ℕ} (c : E l) (R : ℝ) (F : E l → ℂ) :
    ballAvg p c R F = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
      * ∫⁻ x in Metric.ball c R, (‖F x‖₊ : ℝ≥0∞) ^ p := rfl

lemma ballAvg_zero {p : ℝ} (hp : 0 < p) {l : ℕ} (c : E l) (R : ℝ) :
    ballAvg p c R (fun _ => 0) = 0 := by
  rw [ballAvg_apply]
  simp [ENNReal.zero_rpow_of_pos hp]

/-! ## 3. The localised decoupling predicate -/

/-- **GLYZ Corollary 3.7** in our dyadic parametrisation. -/
def CurveDecLoc (l : ℕ) (D : ℕ → ℝ → E l) (m : ℕ) (lam A : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (f : Fin m → E l → ℂ),
    (∀ j, IsFourierRep l (curvePlate l D (lam / (2 * m)) (pieceCenter m j)) (f j)) →
    ∀ (c : E l) (R : ℝ), (m : ℝ) ^ l ≤ R →
      ballAvg (plExp l) c R (fun x => ∑ j, f j x)
        ≤ C ^ (plExp l)
          * (∑ j : Fin m,
              (∫⁻ x, (‖f j x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x) ^ (2 / plExp l))
            ^ (plExp l / 2)

lemma CurveDecLoc_mono {l : ℕ} {D : ℕ → ℝ → E l} {m : ℕ} {lam A : ℝ} {C C' : ℝ≥0∞}
    (h : C ≤ C') (hD : CurveDecLoc l D m lam A C) : CurveDecLoc l D m lam A C' :=
  fun f hf c R hR =>
    (hD f hf c R hR).trans (mul_le_mul' (ENNReal.rpow_le_rpow h (plExp_nonneg l)) le_rfl)

end Submission.Vinogradov
