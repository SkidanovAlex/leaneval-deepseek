/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step1
import Submission.Vinogradov.TentCompare
import Submission.Commons.Measure.Integral.lintegral_mul_le_moving_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 3.8, step 2: the sup comparison on the `H`-ball

Lane 2 of the §3.4 chain.  Starting from the moving-ball form of step 1
(`Lemma38Step1.asymLHS_eq_movingBall`), the second factor `C2` is replaced — pointwise on the
`H`-ball `B_H(0,r)` — by its value at the centre `z`, so that the ball average survives only on
the first factor `C1`:

  `asymLHS ≤ C_sup · ∫⁻ z, |B|⁻¹ · (∫⁻_{w ∈ B} C1 (z + Ψ w)) · C2 z`.

The sup comparison itself is `TentCompare.convPow_platePhi_shift_le` (the `ℝ≥0∞` form of
`TentShift.phiPlate_shift_le`, with the polar-plate containment
`PolarContain.gauge_plateGaugeLin_projEmbed_le`), and the passage from the pointwise comparison
to the integrated one is the commons lemma
`Commons.Measure.Integral.lintegral_mul_le_moving_ball` — which is steps 1 and 2 *combined*.

Note the two ways the comparison is consumed downstream: applied at `w` it gives the direction
used here, and applied at `−w` (the polar-plate condition is symmetric in `w`) it gives the
reverse direction used by lane 7.
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

/-- **GLYZ Lemma 3.8, step 2 (the sup comparison on the `H`-ball).**  For `ξ' ∈ [0,1]` at
distance at most `plateHalf m'` from the level-`m'` centre `pieceCenter (2^m') q'`, and a radius
`0 < r ≤ hBallR k l m'`, there is `C ≥ 0` with

  `asymLHS ≤ ofReal C · ∫⁻ z, |B_H(0,r)|⁻¹ · (∫⁻_{w ∈ B_H(0,r)} C1 (z + Ψ w)) · C2 z`,

where `Ψ = projEmbedLin k l (torsionVec k l hlk ξ')`. -/
theorem asymLHS_le_supMoving {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) {ξ' r : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
    (hr : 0 < r) (hrh : r ≤ hBallR k l m')
    (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      asymLHS k hk l N m m' q q' f
        ≤ ENNReal.ofReal C * ∫⁻ z : E k,
            (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))⁻¹ *
            (∫⁻ w in Metric.ball (0 : E l) r,
              asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨Csup, hCsup0, hCsup⟩ :=
    convPow_platePhi_shift_le (k := k) (l := l) hk hl hlk hξ' (pkExp k - plExp l)
  have hpc : pieceCenter (2 ^ m') q' ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q'
  refine ⟨Csup, hCsup0, ?_⟩
  have hC : ∀ z w, w ∈ Metric.ball (0 : E l) r →
      asymC2 k hk l N m' q' f (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal Csup * asymC2 k hk l N m' q' f z := by
    intro z w hw
    have hw' : ‖w‖ ≤ hBallR k l m' := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    exact hCsup m' (pieceCenter (2 ^ m') q') hpc hsep
      (fun x : E k => ∑ i ∈ blkFin N m' q', f i x) z w hw'
  have hcore := Commons.Measure.Integral.lintegral_mul_le_moving_ball k l
    (projEmbedLin k l (torsionVec k l hlk ξ'))
    (norm_projEmbedLin_eq (orthonormal_torsionVec k l hlk ξ')) hr
    (asymC1 k hk l N m q f) (asymC2 k hk l N m' q' f)
    (measurable_asymC1 k hk l N m q hf).aemeasurable
    (measurable_asymC2 k hk l N m' q' hf).aemeasurable hC
  rw [asymLHS_eq_integral]
  exact hcore

end Submission.Vinogradov
