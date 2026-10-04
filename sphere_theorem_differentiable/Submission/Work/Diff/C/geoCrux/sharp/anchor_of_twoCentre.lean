import Mathlib
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.geoCrux.radial_modulus
import Submission.Work.Diff.C.geoCrux.SharpCore

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The anchor of the sharp radial modulus bound, from the two-centre core

This file proves `Work.Diff.C.geoCrux.SharpAnchorProp` from the two-centre core
`Work.Diff.C.geoCrux.TwoCentreCoreProp`.

## The mathematics

`hcore` at the pair `(σ, 2σ)` — with `N ≥ 0` its operator bound
`‖Z_ξ(σ)‖ ≤ N ‖ξ‖` (`ξ ⊥ v`) and its two scalar inequalities at the value `y_w = ‖Z_w(σ)‖` of
every *unit* `w ⊥ v` — is fed into the (proved) one-dimensional extraction of
`geoCrux/radial_modulus.lean`.  Concretely, `Work.Diff.C.geoCrux.twoCentre_N_bound` turns

* `0 < κ`, `0 < λ` (where `κ = twoK σ (2σ) = 2 cot σ`, `λ = twoL σ (2σ) = 1/sin 2σ`),
* `0 ≤ η`, `0 ≤ δ` (`η = twoE ε₁ σ (2σ)`, `δ = twoD ε₁ σ (2σ)`),
* the exact identity `κλ = 1/sin²σ` (`twoK_mul_twoL`),
* `η ≤ 3ε₁λ` (`twoE_le_twoL`) and `δ ≤ 3ε₁κ` (`twoD_le_twoK`) — both need `cos σ ≥ 1/2`,
* `(κ-δ)(λ-η)N² ≤ 1` (the third conjunct of `hcore`) and `ε₁ ≤ 1/24`,

into `N ≤ sin σ (1 + 6ε₁)`, which is *stronger* than the `sin σ (1 + 7ε₁)` the anchor needs.  The
anchor for an arbitrary `ξ ⊥ v` then follows immediately from the operator bound
`‖Z_ξ(σ)‖ ≤ N‖ξ‖` (the first conjunct of `hcore`) and `6ε₁ ≤ 7ε₁`.  (No reduction to a unit
direction is needed.)

The only input needed to apply `hcore` at the pair `(σ, 2σ)` is the *strict* bound
`2σ < π - arccos (1-c)`: `TwoCentreCoreProp` requires it, because its Hessian hypothesis is used at
both centres.  It is *not* among the hypotheses of `SharpAnchorProp` (which only has the weak
`h2σ : 2σ ≤ π - arccos (1-c)`), but it follows: `cos σ ≥ 1/2` with `σ > 0` gives `σ ≤ π/3`, and
`c ≤ 1/4` gives `arccos (1-c) < arccos (1/2) = π/3`, hence `2σ ≤ 2π/3 < ρ₀`.

## The universe parameters (READ THIS)

`TwoCentreCoreProp` and `SharpAnchorProp` are *closed* `abbrev`s, each with three universe
parameters, `{E : Type u} {H : Type v} {M : Type w}`.  If a theorem is written as

    theorem anchor_of_twoCentre (hcore : TwoCentreCoreProp) : SharpAnchorProp

then Lean generalizes the two occurrences' universe parameters **separately** — the elaborated type
is `TwoCentreCoreProp.{u₁,u₂,u₃} → SharpAnchorProp.{u₄,u₅,u₆}` — and the levels of `hcore` are
frozen at the binder, so `hcore` can *never* be instantiated at the levels of the conclusion.  Every
attempt to apply it fails with

    argument E has type `Type u₄` … but is expected to have type `Type u₁`,

and *no* proof term of that type exists: the hypothesis and the conclusion live at unrelated
universes.  (Verified: that is exactly the failure produced by the naive statement, in an `example`
as well as in a `theorem`.  It is the trap documented in the handoff — "a local hypothesis of type
`CutInjectProp` has its implicit universe arguments frozen at the binder", "A binder
`(hvar : VariationModulusProp)` … gets its universe parameters generalized separately"; it is why
`Work.Diff.C.geoCrux.hmod_of_variation` is stated with the levels explicit and why
`Work.Diff.C.BadGeoDefs` states its auxiliary `Prop` inputs inline.)

Accordingly the theorem below is stated for the **same** triple of universe levels on both sides.
That is what the lemma *means*, and it is directly applicable: a user who has
`hcore : TwoCentreCoreProp` at their own levels and needs `SharpAnchorProp` at those same levels
simply calls `anchor_of_twoCentre hcore` (the universe levels of a constant are instantiated freshly
at each use).  Nothing else in the statement has been touched — same name, same hypotheses, same
conclusion.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open Work.Diff.C.geoCrux

namespace Work.Diff.C.geoCrux.sharp

universe u v w

theorem anchor_of_twoCentre (hcore : Work.Diff.C.geoCrux.TwoCentreCoreProp.{u, v, w}) :
    Work.Diff.C.geoCrux.SharpAnchorProp.{u, v, w} := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBd iNt iCS iPC cov iCov
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv σ hσ0 h2σ hcos ξ hξ
  change ‖fv (cov := cov) hmet q v ξ σ‖ ≤ Real.sin σ * (1 + 7 * ε₁) * ‖ξ‖
  -- ### Numerical preliminaries
  -- `ε₁ ≤ 1/24` (the extraction needs a small `ε₁`; `4ε₁π < c ≤ 1/4` gives far less)
  have hε₁' : ε₁ ≤ 1 / 24 := by
    nlinarith [hnum2, hc1, hε₁, Real.pi_gt_three]
  have hρ0lt : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have h2σπ : 2 * σ < Real.pi := lt_of_le_of_lt h2σ hρ0lt
  have hσπ : σ < Real.pi := by linarith
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith)
  -- `cos σ ≥ 1/2` forces `σ ≤ π/3` (`cos` is strictly decreasing on `[0,π]`)
  have hσle : σ ≤ Real.pi / 3 := by
    by_contra h
    push Not at h
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := σ)
      (by positivity) hσπ.le h
    rw [Real.cos_pi_div_three] at hlt
    linarith
  -- `c ≤ 1/4` gives `arccos (1-c) < arccos (1/2) = π/3`
  have harccos_lt : Real.arccos (1 - c) < Real.pi / 3 := by
    have h1 : Real.arccos (1 - c) < Real.arccos (1 / 2) :=
      Real.arccos_lt_arccos (by norm_num) (by linarith) (by linarith)
    have h2 : Real.arccos (1 / 2) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rwa [h2] at h1
  -- hence the *strict* bound `2σ < ρ₀` which `TwoCentreCoreProp` needs
  have h2σρ0 : 2 * σ < Real.pi - Real.arccos (1 - c) := by linarith
  -- ### The two-centre core at the pair `(σ, 2σ)`
  obtain ⟨N, hN0, hNZ, hKpos, hLpos, hN2, hunit⟩ :=
    @hcore E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBd iNt iCS iPC cov iCov
      hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv σ (2 * σ)
      hσ0 (by linarith) le_rfl h2σρ0
  -- ### The extraction: `N ≤ sin σ (1 + 6ε₁)`
  have hη : 0 ≤ twoE ε₁ σ (2 * σ) := by
    rw [twoE_two_mul]
    have h2 : 0 < Real.sin (2 * σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2σπ
    positivity
  have hδ : 0 ≤ twoD ε₁ σ (2 * σ) := by
    rw [twoD_two_mul]
    positivity
  have hNbound : N ≤ Real.sin σ * (1 + 6 * ε₁) :=
    twoCentre_N_bound hspos hε₁ hε₁' hKpos hLpos hη hδ hN0 (twoK_mul_twoL hσ0 h2σπ)
      (twoE_le_twoL hε₁ hσ0 h2σπ hcos) (twoD_le_twoK hε₁ hσ0 h2σπ hcos) hN2
  -- ### The anchor
  have hZ : ‖fv (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖ := hNZ ξ hξ
  calc ‖fv (cov := cov) hmet q v ξ σ‖ ≤ N * ‖ξ‖ := hZ
    _ ≤ (Real.sin σ * (1 + 6 * ε₁)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hNbound (norm_nonneg ξ)
    _ ≤ Real.sin σ * (1 + 7 * ε₁) * ‖ξ‖ := by
        have h1 : (1 + 6 * ε₁) ≤ (1 + 7 * ε₁) := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hspos.le) (norm_nonneg ξ)

end Work.Diff.C.geoCrux.sharp
