/-
# `Prop.l0_second` — the second-order angular estimate in the weak class

`Work.FTS.EllipticEst.Prop.l0_second` is the weak-class (`TT.EllWeakPos`) form of Step 2 of
Elgindi's `prop:H2`: given the first-order estimate `hfirst` (which supplies the Step-1 inputs
`Ψ`, `z∂_zΨ`, `Ψ/cos θ`, with the bound `‖Ψ‖ + α‖z∂_zΨ‖ + ‖Ψ/cos θ‖ ≤ C₁‖F‖`), one gets

  `‖∂_θθΨ‖_{ℋ⁰} ≤ C(‖F‖_{ℋ⁰} + α‖z∂_zΨ‖_{ℋ⁰})`.

## Route

`l0_second` is the paper's Step 2: multiply the equation by `-∂_θθΨ w²σ` and integrate
(the pairing identity `AngAWeak.I_identity_weak`), bound the five resulting pieces

* `I₁ = α²⟨z²∂_zzΨ, ∂_θθΨ⟩` (the coercivity: `Prop.i1_bare_hh`, proved),
* `I₂ = α(5+α)⟨z∂_zΨ, ∂_θθΨ⟩` and the source/`Ψ` slots (`AngSecond.IP_cauchy_schwarz`),
* `I₄ = ⟨∂_θ(tan θ·Ψ), ∂_θθΨ⟩` (`H2W.AeWAux.aeI4Of` applied to `H2W.AeWAux.i4SliceIneq`),

and solve the resulting quadratic inequality with the Step-1 data of `hfirst` — the assembly
`l0_second_of_i1hh` (in `Prop/l0_second_aux.lean`).

The `I₁` input is available because the weak class carries the *diagonal second-order honesty*
`HkMem α 0 (∂_θθ(z∂_zΨ))` as its tenth conjunct (`TT.EllWeakPos.memZPth2`): this is the clause
Step 2 consumes, and `Prop.i1_bare_hh` proves the coercivity from it plus the `HkMem α 0 (z∂_zΨ)`
slot that `hfirst` supplies.

The sibling interfaces `l0_second_of_i1sharp` (sharp `I₁`) and `l0_second_of_step2ang` (angular
Step-2 `Prop`) live in `Prop/l0_second_sharp.lean`.
-/

import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.Prop.l0_second_aux
import Submission.Work.FTS.EllipticEst.Prop.l0_second_sharp
import Submission.Work.FTS.EllipticEst.Prop.i1_bare_hh

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000
theorem l0_second (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  -- The `I₁` coercivity of Step 2 in the strengthened weak class: `Prop.i1_bare_hh` supplies it
  -- with the two first-order honesties, of which `EllWeakPos.memZPth2` is a field of the class
  -- and the other is part of `hfirst`; the assembly `l0_second_of_i1hh` then gives the target.
  exact l0_second_of_i1hh C₁ hC₁ i1_bare_hh hfirst

end Work.FTS.EllipticEst.Prop
