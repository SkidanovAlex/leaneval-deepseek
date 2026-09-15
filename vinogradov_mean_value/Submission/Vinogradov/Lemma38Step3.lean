/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step2
import Submission.Vinogradov.LowerDegree

/-!
# GLYZ Lemma 3.8, step 3: the convolution swap (lifting the `H`-ball average onto the bump)

Lane 3 of the §3.4 chain.  The ball average of the first factor `C1 = |f_I|^{p_l} ∗ Φ_I` is
rewritten as the integral of the bump `Φ_I` against the ball averages of `|f_I|^{p_l}`:

  `∫⁻_{w ∈ B_H(0,r)} C1 (z + Ψ w) = ∫⁻ t, Φ_I t · AV (z − t)`,

with `AV (u) := ∫⁻_{w ∈ B_H(0,r)} (‖f_I (u + Ψ w)‖₊)^{p_l}`.

The content is the pure Fubini identity `LowerDegree.lintegral_ball_convPow_swap`, applied with
`Ψ = projEmbedLin k l (torsionVec k l hlk ξ')` and `g = f_I` (the block sum).  The reason the
swap is available at all is that the *inner* integral has argument `(z − t) + Ψ w`, whose centre
`z − t` runs over all of `E k` as `t` does; no translation invariance and no isometry property of
`Ψ` is used.
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

/-- **GLYZ Lemma 3.8, step 3 (the convolution swap).**  For `r > 0`, every `z` and every
measurable tuple `f`,

  `∫⁻_{w ∈ B_H(0,r)} C1 (z + Ψ w)
     = ∫⁻ t, Φ_I t · ∫⁻_{w ∈ B_H(0,r)} (‖f_I ((z − t) + Ψ w)‖₊)^{p_l}`,

where `C1 = asymC1 k hk l N m q f` and `f_I = ∑_{i ∈ blkFin N m q} f i`. -/
theorem asymC1_movingBall_swap {k l N m : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k) (q : Fin (2 ^ m))
    {r : ℝ} (hr : 0 < r) {ξ' : ℝ} (z : E k) {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ w in Metric.ball (0 : E l) r,
        asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
      = ∫⁻ t, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
          * (∫⁻ w in Metric.ball (0 : E l) r,
              (‖∑ i ∈ blkFin N m q, f i ((z - t)
                  + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l)) := by
  have hg : Measurable (fun x : E k => ∑ i ∈ blkFin N m q, f i x) := measurable_blkSum q hf
  have h := lintegral_ball_convPow_swap (k := k) (l := l)
    (projEmbedLin k l (torsionVec k l hlk ξ')) hr (plExp l) hg
    (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable z
  rw [show (fun x : E k => ∑ i ∈ blkFin N m q, f i x) = (fun x => ∑ i ∈ blkFin N m q, f i x)
    from rfl] at h
  exact h

end Submission.Vinogradov
