/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# `StarRegularEnvelope` for every countable group

All the fields of `Work.ORVonNeumann.StarRegularEnvelope` are theorems for the concrete model
`U(G) = N(G)[(N(G) \ {0})^{-1}]` (`Work.ORVonNeumann.Rep.countableGroupVonNeumann`):
`*`-regularity (`VonNeumannAlgebra.starRegularAffiliated`), positive definiteness
(`VonNeumannAlgebra.posDefAffiliated`), the faithful rank function
(`VonNeumannAlgebra.rankAffiliated`), the `*`-embedding `ℂ[G] ↪ U(G)`
(`VonNeumannAlgebra.toU` and its properties), and — for every subgroup `H ≤ G` — the inclusion
`U(H) ↪ U(G)` with Linnell independence
(`Work.ORVonNeumann.VonNeumannAlgebra.envelopeInclusionGeneral`, via the diagonal embedding
`Work.ORVonNeumann.Rep.exists_diagHom` and the Ore extension
`Work.ORVonNeumann.VonNeumannAlgebra.exists_envelopeInclusion_of_diagHom`).

## Main results

* `Work.ORVonNeumann.envelopeInclusionGeneral` — the subgroup data `sub H`;
* `Work.ORVonNeumann.countableStarRegularEnvelope` — **the envelope, unconditionally**, for
  every countable `G` carrying the measurable structure of the counting measure;
* `Work.ORVonNeumann.countableStarRegularEnvelopeOfCountable` — the same with only the
  hypothesis `[Countable G]` (the measurable structure being the discrete one).
-/
import Mathlib
import Submission.Work.ORVonNeumann.Envelope
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumannOre
import Submission.Work.ORVonNeumann.Rep.exists_diagHom
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.U
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.UStar
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.posDefAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.exists_envelopeInclusion_of_diagHom

set_option autoImplicit false

universe u

namespace Work.ORVonNeumann

/-- The concrete model of `N(G)` for a countable `G`, with its involution and `ℂ`-algebra
structure, and the subspace `ℂ[G] ⊆ U(G)` — spelled out once so that the statements below
stay readable. -/
noncomputable abbrev countableModel (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : GroupVonNeumannAlgebra G :=
  Rep.countableGroupVonNeumann (G := G)

/-- **The subgroup data of the envelope, for an arbitrary subgroup `H ≤ G`.**  `U(H)` is the
algebra of operators affiliated to `N(H)`, and it includes into `U(G)` with Linnell
independence: the diagonal embedding `N(H) ↪ N(G)` (`Work.ORVonNeumann.Rep.exists_diagHom`)
extends to `U(H) →+* U(G)` by the universal property of the Ore localisation, and the coset
decomposition of `ℓ²(G)` gives Linnell independence. -/
theorem envelopeInclusionGeneral {G : Type u} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) :
    Nonempty (EnvelopeInclusion G (countableModel G).affiliated
      (VonNeumannAlgebra.toU (countableModel G)) H) := by
  obtain ⟨C, Φ, hΦ, hΦstar, hΦinj, hΦform⟩ := Rep.exists_diagHom H
  exact VonNeumannAlgebra.exists_envelopeInclusion_of_diagHom H C Φ hΦ hΦstar hΦinj hΦform

/-- **The envelope from the subgroup data.**  Given, for every `H ≤ G`, the inclusion
`U(H) ⊆ U(G)` with Linnell independence, the concrete model produces a
`StarRegularEnvelope G`: all other fields are the theorems
`VonNeumannAlgebra.starRegularAffiliated`, `...posDefAffiliated`, `...rankAffiliated`. -/
noncomputable def countableStarRegularEnvelopeOf {G : Type u} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G]
    (hsub : ∀ H : Subgroup G,
      Nonempty (EnvelopeInclusion G (countableModel G).affiliated
        (VonNeumannAlgebra.toU (countableModel G)) H)) :
    StarRegularEnvelope G where
  U := (countableModel G).affiliated
  ι := VonNeumannAlgebra.toU (countableModel G)
  ι_injective := VonNeumannAlgebra.toU_injective (countableModel G)
  ι_star := fun x => (VonNeumannAlgebra.toU_star (countableModel G) x).symm
  ι_algebraMap := VonNeumannAlgebra.toU_algebraMap (countableModel G)
  starRegular := VonNeumannAlgebra.starRegularAffiliated (G := G)
  posDef := VonNeumannAlgebra.posDefAffiliated (G := G)
  rk := Classical.choose (VonNeumannAlgebra.rankAffiliated (G := G))
  rk_faithful := Classical.choose_spec (VonNeumannAlgebra.rankAffiliated (G := G))
  sub := fun H => Classical.choice (hsub H)

/-- **The analytic core of the one-relator coherence project, for every countable group.**
`U(G)` is the algebra of operators affiliated to the group von Neumann algebra `N(G)`,
`ℂ[G] ↪ U(G)` is its structure map, `U(G)` is `*`-regular and positive definite, it carries
the faithful extended rank function `rk_G`, and for every `H ≤ G` the subalgebra `U(H)` is
included in `U(G)` with Linnell independence. -/
noncomputable def countableStarRegularEnvelope {G : Type u} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] :
    StarRegularEnvelope G :=
  countableStarRegularEnvelopeOf (fun H => envelopeInclusionGeneral H)

/-- **The envelope for every countable group**, without any measurable structure in the
statement: the discrete `σ`-algebra is used. -/
theorem countableStarRegularEnvelopeOfCountable {G : Type*} [Group G] [Countable G] :
    Nonempty (StarRegularEnvelope G) := by
  letI : MeasurableSpace G := ⊤
  haveI : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  haveI : MeasurableMul G := ⟨fun _ => fun s _ => trivial, fun _ => fun s _ => trivial⟩
  exact ⟨countableStarRegularEnvelope⟩

end Work.ORVonNeumann
