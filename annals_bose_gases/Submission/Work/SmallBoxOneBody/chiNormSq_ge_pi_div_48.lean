import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BSKinetic.Defs
import Submission.Work.SmallBoxOneBody.base_with_small_mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SmallBoxOneBody.chiNormSq_ge_pi_div_48` — the *sharp* lower bound for `chiNormSq`

## Why this file exists

The requested lemma `Work.SmallBoxOneBody.chiNormSq_ge_sixth`
(`(1 : ℝ)/6 ≤ Submission.BoseGases.chiNormSq`) is **not provable** in this workspace, and the
obstruction is not missing analysis: it is the *definition* of `chiBase`.

`Submission/CubicChi.lean` sets `chiBase x = chiBump x`, where `chiBump : ContDiffBump 0` is the
`ContDiffBump` with `rIn = 1/4`, `rOut = 1/2`.  Unfolding `ContDiffBump.toFun`
(`#print Submission.BoseGases.chiBase`):

    chiBase x = (someContDiffBumpBase ℝ³).toFun 2 (4 • x),

and `someContDiffBumpBase E = Nonempty.some hb.out = Classical.choice hb.out`, where
`Classical.choice` is Lean's *choice axiom* `axiom Classical.choice : Nonempty α → α`, which
carries **no specification**: `Classical.choice ⟨X⟩ = X` is not provable (`rfl`, `simp` and
`norm_num` all fail on `Classical.choice (⟨3⟩ : Nonempty ℝ) = 3`).  Consequently the only
information about `chiBase` that any proof can extract is the list of `ContDiffBumpBase` fields
of the (unspecified) chosen base — exactly as `Submission/Work/ChiSmall.lean` records for the
boundary decay ("its explicit formula is hidden behind `Classical.choice` ... no boundary decay
of `χ` is provable").  For `chiNormSq` those fields give:

* `0 ≤ chiBase ≤ 1`, `chiBase = 1` on `ball 0 (1/4)`, `chiBase = 0` off `ball 0 (1/2)`
  (so `π/48 ≤ chiNormSq`, proved below, and `chiNormSq ≤ π/6`, already
  `Work.UBBInputs9.B.chiNormSq_le_pi_div_six`),

and **nothing else**: `ContDiffBumpBase.toFun` is unconstrained on the annulus `1 < ‖y‖ < 2`, so
the base with `toFun R y = smoothTransition ((R - ‖y‖)/(R - 1)) · η(‖y‖)` (`η` a smooth radial
factor equal to `1` near `0` and to a small `ε > 0` outside the unit ball) satisfies *all six*
fields while `(1/64)∫ (toFun 2)²` is arbitrarily close to `π/48 < 1/6`
(`Work.SmallBoxOneBody.base_with_small_mass` is the formal witness).  Since the choice axiom is
unconstrained, admissible models of this environment therefore have `chiNormSq < 1/6`, so no
proof of `chiNormSq_ge_sixth` can exist.

**The sharp statement that the definition *does* give** is `π/48 ≤ chiNormSq` — that is the
`L²`-mass of the plateau `‖x‖ ≤ 1/4` alone, and it cannot be improved by any argument that only
uses the fields (the thin base above shows exactly this).

## Contents

* `chiNormSq_ge_pi_div_48 : Real.pi / 48 ≤ chiNormSq`  (sharp, proved);
* `chiNormSq_ge_inv_sixteen : (1 : ℝ)/16 ≤ chiNormSq`  (the round-number corollary, which is the
  constant a caller can actually use: it gives `chiNormSq⁻¹ ≤ 16`);
* `someContDiffBumpBase_eq_choice`: the value of `someContDiffBumpBase ℝ³` is the same whichever
  `ContDiffBumpBase` is exhibited, i.e. the chosen base is *not* tied to any concrete formula.

A caller who needs `1/6` (or any constant `> π/48`) must first make `chiBase` an explicit
function, e.g. `chiBase x := Real.smoothTransition (2 - 4 * ‖x‖)` (the base
`ContDiffBumpBase.ofInnerProductSpace ℝ³` at `R = 2`), after which
`∫ x, (Real.smoothTransition (2 - 4 * ‖x‖))² ≈ 0.1868234 ≥ 1/6`; that computation, together with
the named repair-kit bump and its properties, is in
`Submission/Work/SmallBoxOneBody/chiBaseConc.lean`
(`Work.SmallBoxOneBody.chiBaseConc_sq_integral_ge_sixth`).  The full write-up of the finding is in
`Submission/Work/SmallBoxOneBody/NOTES_chiNormSq.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxOneBody

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-- `chiBase = 1` on `ball 0 (1/4)` (the `rIn`-ball of `chiBump`), so
`∫_{ball 0 (1/4)} chiBase²` is exactly the volume `π/48` of that ball. -/
theorem chiNormSq_ge_pi_div_48 : Real.pi / 48 ≤ Submission.BoseGases.chiNormSq := by
  have hf_int : Integrable (fun x : ℝ³ => (chiBase x) ^ 2) :=
    chiBase_sq_continuous.integrable_of_hasCompactSupport chiBase_sq_hasCompactSupport
  -- on the plateau the integrand is the constant `1`
  have hcongr : (∫ x in Metric.ball (0 : ℝ³) (1 / 4), (chiBase x) ^ 2)
      = ∫ x in Metric.ball (0 : ℝ³) (1 / 4), (1 : ℝ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hx' : ‖x‖ ≤ 1 / 4 := by
      have := Metric.mem_ball.mp hx
      simpa [dist_eq_norm] using le_of_lt this
    exact chiBase_sq_eq_one_of_norm_le hx'
  have hval : (∫ x in Metric.ball (0 : ℝ³) (1 / 4), (1 : ℝ)) = Real.pi / 48 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real_def, volume_ball_open_r3 (1 / 4) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  -- `chiNormSq` is the integral of the same integrand over the bigger ball `ball 0 (1/2)`
  have hzero : ∀ x ∉ Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 = 0 := by
    intro x hx
    have hx' : (1 : ℝ) / 2 ≤ ‖x‖ := by
      simp only [Metric.mem_ball, dist_eq_norm, not_lt, sub_zero] at hx
      exact hx
    have h0 : chiBase x = 0 :=
      chiBump.zero_of_le_dist (by simpa [chiBump, dist_eq_norm] using hx')
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hEq : Submission.BoseGases.chiNormSq =
      ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := by
    rw [chiNormSq]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- enlarge `ball 0 (1/4)` to `ball 0 (1/2)` by splitting off the nonnegative annulus
  have hsub : Metric.ball (0 : ℝ³) (1 / 4) ⊆ Metric.ball (0 : ℝ³) (1 / 2) :=
    Metric.ball_subset_ball (by norm_num)
  have hsplit : (∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2)
      = (∫ x in Metric.ball (0 : ℝ³) (1 / 4), (chiBase x) ^ 2)
        + ∫ x in Metric.ball (0 : ℝ³) (1 / 2) \ Metric.ball (0 : ℝ³) (1 / 4),
            (chiBase x) ^ 2 := by
    have hunion : Metric.ball (0 : ℝ³) (1 / 4)
        ∪ (Metric.ball (0 : ℝ³) (1 / 2) \ Metric.ball (0 : ℝ³) (1 / 4))
        = Metric.ball (0 : ℝ³) (1 / 2) := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hsub hx
        · exact hx.1
      · intro hx
        by_cases h : x ∈ Metric.ball (0 : ℝ³) (1 / 4)
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
    conv_lhs => rw [← hunion]
    exact MeasureTheory.setIntegral_union (s := Metric.ball (0 : ℝ³) (1 / 4))
      (t := Metric.ball (0 : ℝ³) (1 / 2) \ Metric.ball (0 : ℝ³) (1 / 4))
      disjoint_sdiff_self_right (measurableSet_ball.diff measurableSet_ball)
      (hf_int.integrableOn) (hf_int.integrableOn)
  have hann : 0 ≤ ∫ x in Metric.ball (0 : ℝ³) (1 / 2) \ Metric.ball (0 : ℝ³) (1 / 4),
      (chiBase x) ^ 2 :=
    MeasureTheory.setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball)
      (fun x _ => sq_nonneg _)
  calc Real.pi / 48 = ∫ x in Metric.ball (0 : ℝ³) (1 / 4), (chiBase x) ^ 2 := by rw [hcongr, hval]
    _ ≤ ∫ x in Metric.ball (0 : ℝ³) (1 / 2), (chiBase x) ^ 2 := by rw [hsplit]; linarith
    _ = Submission.BoseGases.chiNormSq := hEq.symm

/-- Round-number corollary: `chiNormSq ≥ 1/16`, equivalently `chiNormSq⁻¹ ≤ 16`. -/
theorem chiNormSq_ge_inv_sixteen : (1 : ℝ) / 16 ≤ Submission.BoseGases.chiNormSq := by
  have hpi : (1 : ℝ) / 16 ≤ Real.pi / 48 := by
    nlinarith [Real.pi_gt_three]
  exact le_trans hpi chiNormSq_ge_pi_div_48

/-- **The `ContDiffBumpBase` fields do not force `1/6`.**  There is a legitimate base whose
induced corpus bump (scale `rIn = 1/4`, ratio `rOut/rIn = 2`) has `L²` mass `< 64/6`, i.e. in a model
of the axioms where `someContDiffBumpBase ℝ³` is that base, `chiNormSq < 1/6`.  Since the choice
axiom is unspecified, that model is admissible and no proof of `1/6 ≤ chiNormSq` can exist; `π/48`
(the bound proved below) is the sharp field-consequence. -/
theorem not_forced_six_le_chiNormSq :
    ∃ X : ContDiffBumpBase ℝ³, (1 / 64 : ℝ) * ∫ y, (X.toFun 2 y) ^ 2 < (1 : ℝ) / 6 :=
  base_with_small_mass

/-- Caller-facing form of the sharp bound: `chiNormSq⁻¹ ≤ 16`. -/
theorem chiNormSq_inv_le_sixteen : (Submission.BoseGases.chiNormSq)⁻¹ ≤ 16 := by
  have h := (inv_le_inv₀ chiNormSq_pos (by norm_num : (0 : ℝ) < 1 / 16)).mpr chiNormSq_ge_inv_sixteen
  simpa using h

/-- The arithmetic step of the one-body tube bound that the sharp lower bound supports: for
`0 < d ≤ 1/8` one has `chiNormSq⁻¹ * d ≤ 2 + 2 * d` (the shape
`chiNormSq⁻¹ * winGrad (χ_{ℓd}) ≤ 2 · winGrad (χ_ℓ) + 2 · winGrad (χ_{ℓd})` reduces to, after
`winGrad (chiScale a) = a · winGrad χ`). -/
theorem chiNormSq_inv_mul_le {d : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) :
    (Submission.BoseGases.chiNormSq)⁻¹ * d ≤ 2 + 2 * d := by
  have h1 : (Submission.BoseGases.chiNormSq)⁻¹ * d ≤ 16 * d :=
    mul_le_mul_of_nonneg_right chiNormSq_inv_le_sixteen (le_of_lt hd)
  linarith

/-- **The chosen bump base is not tied to any exhibited base.**  For every
`X : ContDiffBumpBase ℝ³` the value of `someContDiffBumpBase ℝ³` is the same
`Classical.choice` applied to the corresponding `Nonempty` proof — the two proofs are equal by
proof irrelevance.  In particular no equation `someContDiffBumpBase ℝ³ = X` is available for a
concrete `X`, so no property of `chiBase` beyond the six `ContDiffBumpBase` fields is provable. -/
theorem someContDiffBumpBase_eq_choice (X : ContDiffBumpBase ℝ³) :
    someContDiffBumpBase ℝ³ = Classical.choice (⟨X⟩ : Nonempty (ContDiffBumpBase ℝ³)) := by
  unfold someContDiffBumpBase
  exact congrArg Classical.choice (Subsingleton.elim _ _)

end Work.SmallBoxOneBody
