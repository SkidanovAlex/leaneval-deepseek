/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Place
import Submission.Work.PointlessTwist.All

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The class-(a) residual: the concrete local model at the place `5`

`Work.PointlessTwist.NumberFieldResidual 𝕜` is the residual of the number-field class (a) of
Lin–Shinder, *Motivic invariants of birational maps*, Annals of Math. 199 (1), 2024, Theorem 1.2:

  `∃ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5), HasReductionPlace (twistOf C₅ L)`,

i.e. there is a place of `L` at which the reduction of the points of `E = C₅.E` gives a non-zero
local obstruction to the twist.  `Place.lean` produces such a place from the local-model data
(`LocalModelData`, in `Conditional.lean`); this file records the residual in that form and proves
that it implies the residual of the chain.

## The concrete data of class (a)

Over `𝕜 = ℚ` the classical choices are

* `C₅`: the Tate normal form `y² + (1-c)xy - cy = x³ - cx²` with `c ∈ ℤ`, `5 ∤ c`,
  `5 ∤ c² - 11c - 1` (e.g. `c = 1`, an instance of which is pinned in `TateCurve.lean`); then
  `Δ = c⁵(c² - 11c - 1)` is a unit at `5`, the model has good reduction at `5`
  (`tateCurve_hasGoodReduction`), and the point `(0,0)` of order `5` reduces non-trivially
  (`Marker.tateCurve_redPoint_zero_ne_zero`);
* `L`: the degree-`5` subfield of `ℚ(ζ₂₅)`, cyclic over `ℚ` and **totally ramified** at `5`
  (`e = 5`, `f = 1`);
* `R`: the valuation ring of the place of `L` above `5`, so that `σ = L.gen ∈ Gal(L/ℚ)` preserves
  the valuation (the place is unique over `5`) and acts trivially on the residue field `𝔽₅`.

The structure `LocalModelData` names exactly these four facts; what remains of
`NumberFieldResidual` is a purely arithmetic statement about the concrete field `L ⊂ ℚ(ζ₂₅)` and
the prime `5` — no further elliptic-curve theory.

## Main results

* `NumberFieldReduction 𝕜 C₅ L` — the residual in local-model form.
* `hasReductionPlace_of_numberFieldReduction` — it gives the place datum of the chain.
* `numberFieldResidual_of_exists` — hence `Work.PointlessTwist.NumberFieldResidual 𝕜`.
* `hasPointlessTwist_of_numberFieldReduction` — hence the arithmetic half `HasPointlessTwist 𝕜`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The class-(a) residual in local-model form**: the local-model data at a place of the top
field of the twist `twistOf C₅ L`. -/
abbrev NumberFieldReduction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
    (L : Work.PointlessTwist.CyclicExtension 𝕜 5) :=
  LocalModelData (Work.PointlessTwist.twistOf C₅ L)

/-- **The local-model residual gives the place datum of the chain.** -/
theorem hasReductionPlace_of_numberFieldReduction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
    (L : Work.PointlessTwist.CyclicExtension 𝕜 5)
    (h : NumberFieldReduction C₅ L) :
    Work.PointlessTwist.HasReductionPlace (Work.PointlessTwist.twistOf C₅ L) :=
  hasReductionPlace_of_localModelData _ h

/-- **The class-(a) residual, from the local-model form.** -/
theorem numberFieldResidual_of_exists {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [NumberField 𝕜]
    (h : ∃ (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
      (L : Work.PointlessTwist.CyclicExtension 𝕜 5), Nonempty (NumberFieldReduction C₅ L)) :
    Work.PointlessTwist.NumberFieldResidual 𝕜 := by
  obtain ⟨C₅, L, ⟨hL⟩⟩ := h
  exact ⟨C₅, L, hasReductionPlace_of_numberFieldReduction C₅ L hL⟩

/-- **The arithmetic half of the paper's Theorem 1.2 (a), from the local-model residual.** -/
theorem hasPointlessTwist_of_numberFieldReduction {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    [NumberField 𝕜]
    (h : ∃ (C₅ : Work.PointlessTwist.FiveTorsionCurve 𝕜)
      (L : Work.PointlessTwist.CyclicExtension 𝕜 5), Nonempty (NumberFieldReduction C₅ L)) :
    Work.PointlessTwist.HasPointlessTwist 𝕜 :=
  Work.PointlessTwist.hasPointlessTwist_of_numberFieldResidual (𝕜 := 𝕜)
    (numberFieldResidual_of_exists h)

/-- **The residual of class (a) at `ℚ`, in local-model form.** -/
abbrev Residual_numberField : Prop :=
  ∃ (C₅ : Work.PointlessTwist.FiveTorsionCurve ℚ)
    (L : Work.PointlessTwist.CyclicExtension ℚ 5), Nonempty (NumberFieldReduction C₅ L)

/-- `Residual_numberField` gives the parent chapter's residual `Residual_numberField` of
`Work.PointlessTwist.Assembly`. -/
theorem numberFieldResidual_of_residual_numberField (h : Residual_numberField) :
    Work.PointlessTwist.Residual_numberField :=
  numberFieldResidual_of_exists h

end

end Work.SilvermanReduction
