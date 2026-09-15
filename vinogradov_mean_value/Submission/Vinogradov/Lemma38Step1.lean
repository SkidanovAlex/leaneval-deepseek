/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymRefine
import Submission.Vinogradov.AsymFine

/-!
# GLYZ Lemma 3.8, step 1: the moving-ball decomposition

This module starts the assembly of GLYZ Lemma 3.8 (`AsymDecFine`), following the nine-step plan
recorded in `ROADMAP.lean` (session 52 (B)).  The bilinear expression

  `asymLHS k hk l N m m' q q' f
     = ∫⁻ x, (|f_I|^{p_l} ∗ Φ_I)(x) · (|f_{I'}|^{p_k − p_l} ∗ Φ_{I'})(x)`

is first rewritten in terms of the two factors `asymC1` (`p_l`-side) and `asymC2`
(complementary side), and then — **this is step 1** — the whole-space integral is replaced by the
average over the translates `H + z` of the integral over the `H`-ball of radius `r`, using the
moving-ball (Fubini) identity `AsymFine.lintegral_moving_ball_proj` (GLYZ (3.11)):

  `∫⁻ z, ∫⁻_{w ∈ B_H(0,r)} F (z + Ψ w) = |B_H(0,r)| · ∫⁻ x, F x`.

Equivalently,

  `asymLHS = |B|⁻¹ · ∫⁻ z, ∫⁻_{w ∈ B} C1(z + Ψ w) · C2(z + Ψ w)`,

which is the form the subsequent steps (sup comparison, convolution swap, Corollary 3.7 on each
translate, …) act on.
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

/-! ## 1. The two factors of the bilinear expression -/

/-- The `p_l`-side of the bilinear expression: the convolution of `|f_I|^{p_l}` with the plate
bump `Φ_I` of the coarse level `m`. -/
noncomputable def asymC1 (k : ℕ) (hk : 1 ≤ k) (l N m : ℕ) (q : Fin (2 ^ m))
    (f : Fin (2 ^ N) → E k → ℂ) : E k → ℝ≥0∞ :=
  convPow k (plExp l) (fun x => ∑ i ∈ blkFin N m q, f i x)
    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q))

/-- The complementary side (exponent `p_k − p_l`), at level `m'`. -/
noncomputable def asymC2 (k : ℕ) (hk : 1 ≤ k) (l N m' : ℕ) (q' : Fin (2 ^ m'))
    (f : Fin (2 ^ N) → E k → ℂ) : E k → ℝ≥0∞ :=
  convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q'))

lemma asymC1_apply (k : ℕ) (hk : 1 ≤ k) (l N m : ℕ) (q : Fin (2 ^ m))
    (f : Fin (2 ^ N) → E k → ℂ) (x : E k) :
    asymC1 k hk l N m q f x
      = ∫⁻ y, (‖∑ i ∈ blkFin N m q, f i (x - y)‖₊ : ℝ≥0∞) ^ (plExp l)
          * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) y := rfl

lemma asymC2_apply (k : ℕ) (hk : 1 ≤ k) (l N m' : ℕ) (q' : Fin (2 ^ m'))
    (f : Fin (2 ^ N) → E k → ℂ) (x : E k) :
    asymC2 k hk l N m' q' f x
      = ∫⁻ y, (‖∑ i ∈ blkFin N m' q', f i (x - y)‖₊ : ℝ≥0∞) ^ (pkExp k - plExp l)
          * platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q') y := rfl

/-- The bilinear expression is the integral of the product of the two factors. -/
lemma asymLHS_eq_integral (k : ℕ) (hk : 1 ≤ k) (l N m m' : ℕ) (q : Fin (2 ^ m))
    (q' : Fin (2 ^ m')) (f : Fin (2 ^ N) → E k → ℂ) :
    asymLHS k hk l N m m' q q' f
      = ∫⁻ x, asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x := rfl

/-! ## 2. Measurability of the two factors -/

lemma measurable_blkSum {k N m : ℕ} (q : Fin (2 ^ m)) {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x : E k => ∑ i ∈ blkFin N m q, f i x) :=
  Finset.measurable_sum _ fun i _ => hf i

lemma measurable_asymC1 (k : ℕ) (hk : 1 ≤ k) (l N m : ℕ) (q : Fin (2 ^ m))
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    Measurable (asymC1 k hk l N m q f) :=
  measurable_convPow k (plExp l) (measurable_blkSum q hf)
    (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable

lemma measurable_asymC2 (k : ℕ) (hk : 1 ≤ k) (l N m' : ℕ) (q' : Fin (2 ^ m'))
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    Measurable (asymC2 k hk l N m' q' f) :=
  measurable_convPow k (pkExp k - plExp l) (measurable_blkSum q' hf)
    (continuous_platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')).measurable

/-! ## 3. Step 1: the moving-ball decomposition -/

/-- **GLYZ Lemma 3.8, step 1 (the moving-ball decomposition).**  The bilinear expression is the
average, over the translates `H + z`, of the integral of `C1 · C2` over the `H`-ball of radius
`r > 0`:

  `asymLHS = |B|⁻¹ · ∫⁻ z, ∫⁻_{w ∈ B_H(0,r)} C1 (z + Ψ w) · C2 (z + Ψ w)`,

where `Ψ = projEmbedLin k l (torsionVec k l hlk ξ')`.  This is GLYZ (3.11). -/
theorem asymLHS_eq_movingBall {k l N m m' : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k)
    (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) {ξ' r : ℝ} (hr : 0 < r)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    asymLHS k hk l N m m' q q' f
      = (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))⁻¹ *
        ∫⁻ z : E k, ∫⁻ w in Metric.ball (0 : E l) r,
          asymC2 k hk l N m' q' f (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
            * asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w) := by
  have hF : AEMeasurable (fun x : E k =>
      asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x) :=
    ((measurable_asymC1 k hk l N m q hf).mul (measurable_asymC2 k hk l N m' q' hf)).aemeasurable
  have hmove := lintegral_moving_ball_proj (ξ' := ξ') hlk hr
    (fun x : E k => asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x) hF
  have hcomm : ∀ x : E k, asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x
      = asymC2 k hk l N m' q' f x * asymC1 k hk l N m q f x := fun x => mul_comm _ _
  simp only [hcomm] at hmove
  have hBpos : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) 0 hr).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hBtop : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hmain : (∫⁻ x : E k, asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x)
      = (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))⁻¹ *
        ∫⁻ z : E k, ∫⁻ w in Metric.ball (0 : E l) r,
          asymC2 k hk l N m' q' f (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
            * asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w) := by
    rw [show (∫⁻ x : E k, asymC1 k hk l N m q f x * asymC2 k hk l N m' q' f x)
        = ∫⁻ x : E k, asymC2 k hk l N m' q' f x * asymC1 k hk l N m q f x from
      lintegral_congr fun x => hcomm x]
    rw [hmove, ← mul_assoc, ENNReal.inv_mul_cancel hBpos hBtop, one_mul]
  rw [asymLHS_eq_integral, hmain]

end Submission.Vinogradov
