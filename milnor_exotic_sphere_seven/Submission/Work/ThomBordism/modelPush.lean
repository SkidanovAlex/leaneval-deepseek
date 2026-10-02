import Submission.Work.ThomBordism.modelLevelOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the pushforward of local homology along a linear homeomorphism (the round-36 vocabulary)

`NOTE_MODEL_AND_SOUNDNESS.md` §20: the lead's round-36 bypass of the `HOF.chartTr` divergence defines
the model classes by **pushforward along a linear homeomorphism** `L` of `ℝ^N`.  This file provides
exactly that vocabulary and nothing else:

* `Work.ThomBordism.locPush L u` — the pushforward
  `H_N(ℝ^N, ℝ^N∖{u}) → H_N(ℝ^N, ℝ^N∖{L u})` induced by `L`, i.e. the `RelHmapOf` of the map of pairs.
  It is deliberately **not** `HOF.chartTr`: no chart, no `OpenPartialHomeomorph`, no instances to
  unify, hence (by §18–§20) no divergence.

The model-level consumers (`γ_B`, `β_B` and `δ_B γ_B = c • β_B` for the half-space `H = {x₀ ≥ 0}`)
are stated against this pushforward.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

/-- **The pushforward of local homology along a linear homeomorphism** of `ℝ^N`. -/
def locPush {N : ℕ} (L : Euc N ≃L[ℝ] Euc N) (u : Euc N) :
    Work.Orient.RelH (TopCat.of (Euc N)) N ({u} : Set (Euc N)) →ₗ[ℤ]
      Work.Orient.RelH (TopCat.of (Euc N)) N ({L u} : Set (Euc N)) :=
  Work.PTGeometric.HOF.RelHmapOf N (TopCat.ofHom ⟨L, L.continuous⟩) {u} {L u}
    (fun x hx h => hx (L.injective h))

/-- The pushforward of a local class along a linear homeomorphism. -/
theorem locPush_apply {N : ℕ} (L : Euc N ≃L[ℝ] Euc N) (u : Euc N)
    (z : Work.Orient.RelH (TopCat.of (Euc N)) N ({u} : Set (Euc N))) :
    locPush L u z
      = Work.PTGeometric.HOF.RelHmapOf N (TopCat.ofHom ⟨L, L.continuous⟩) {u} {L u}
          (fun x hx h => hx (L.injective h)) z := rfl

end

end Work.ThomBordism
