/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `ORDivLoc` deliverable, with every side condition discharged

Collecting the files of this directory, the statement of the deliverable is:

for every countable group `G`, if

* (**N6**) for every finitely generated subgroup `G₀` of an arbitrary group, every
  `U` that is a positive definite `∗`-regular ring with a faithful Sylvester rank function, every
  `φ : ℂ[G₀] →+* U` that is epic and `∗`-compatible and satisfies the rank-free Hughes-freeness
  condition `IsHughesFreeEnv φ`, the induction environment `Thm61Step ℂ G₀ U φ H` exists for every
  finitely generated non-trivial `H ≤ G₀`
  — this is exactly `Work.ORHughesFree.Section6.thm61Step_nonempty`, the open gap of node N6, with
  Hughes-freeness supplied by [JZLA20, Proposition 3.11]; and
* (**Prop 3.11**) for every locally indicable `H ≤ G`, the structure map
  `ℂ[H] →+* U(G)` into the canonical envelope satisfies `IsHughesFreeEnv`
  — `Work.ORDivLoc.Prop311OnComplex G`, node ORP311's statement, or its equivalent
  `∗`-regular-closure form `Work.ORDivLoc.Prop311OnComplexClosure G`;

then `DivLoc K G φK` holds for every coefficient field `K : Type` with an embedding
`φK : K →+* ℂ`: the division closure `D_{K[H]}(U(G))` of the M1 bridge is a division ring for
every locally indicable `H ≤ G`.

No further hypothesis is needed: epicity of the structure map into the `∗`-regular closure over `ℂ`
is `Work.ORDivLoc.Closure.isEpic_starClosureCod_complex`, and positive definiteness, the faithful
rank function and the `∗`-compatibility at `V_ℂ` are all proved in this directory.  The reduction
from an arbitrary coefficient field `K` to `ℂ` is `Work.ORDivLoc.Complex`.
-/
import Submission.Work.ORDivLoc.Closure.isEpic_starClosureCod_complex
import Submission.Work.ORDivLoc.N6Criterion

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc

/-- The epicity of the structure map into the `∗`-regular closure over `ℂ`, for the canonical
envelope and every locally indicable subgroup. -/
theorem isEpic_starClosureCod_countableEnvelope {G : Type} [Group G] [Countable G] :
    ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
      Work.ORHughesFree.IsEpic
        (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H) :=
  fun _ _ => Closure.isEpic_starClosureCod_complex (Work.ORBridgeLinnell.countableEnvelope G) _

/-- **Node N6's raw input `HstepOnComplex`, with every side condition discharged.**

The only inputs are the engine's construction `hN6` (`thm61Step_nonempty`) and [JZLA20,
Proposition 3.11] in the `∗`-regular-closure vocabulary over `ℂ` (`hHF`). -/
theorem hstepOnComplex_of_thm61Step' {G : Type} [Group G] [Countable G]
    (hHF : Prop311OnComplexClosure G)
    (hN6 : ∀ {G₀ : Type} [Group G₀] [Work.ORHughesFree.LocallyIndicable G₀] {U : Type} [Ring U]
      [StarRing U] [Work.ORHughesFree.IsStarRegular U],
      Work.ORHughesFree.IsPositiveDefiniteStarRegular U →
      ∀ (φ : MonoidAlgebra ℂ G₀ →+* U) (rkU : Work.ORHughesFree.SylvesterRank U),
        rkU.IsFaithful →
      Work.ORHughesFree.IsEpic φ → Work.ORHughesFree.StarCompatible φ →
      Work.ORHughesFree.IsHughesFreeEnv φ →
      ∀ H₀ : Subgroup G₀, H₀.FG → H₀ ≠ ⊥ →
        Nonempty (Work.ORHughesFree.Thm61Step ℂ G₀ U φ H₀)) :
    HstepOnComplex G :=
  hstepOnComplex_of_thm61Step isEpic_starClosureCod_countableEnvelope hHF hN6

/-- **The deliverable of the subproject.**  From the engine's construction `hN6`
(`thm61Step_nonempty`) and [JZLA20, Proposition 3.11] (`hHF`), `DivLoc K G φK` holds for every
coefficient field `K : Type` with an embedding `φK : K →+* ℂ`. -/
theorem divLoc_of_thm61StepComplex' {G : Type} [Group G] [Countable G]
    (hHF : Prop311OnComplexClosure G)
    (hN6 : ∀ {G₀ : Type} [Group G₀] [Work.ORHughesFree.LocallyIndicable G₀] {U : Type} [Ring U]
      [StarRing U] [Work.ORHughesFree.IsStarRegular U],
      Work.ORHughesFree.IsPositiveDefiniteStarRegular U →
      ∀ (φ : MonoidAlgebra ℂ G₀ →+* U) (rkU : Work.ORHughesFree.SylvesterRank U),
        rkU.IsFaithful →
      Work.ORHughesFree.IsEpic φ → Work.ORHughesFree.StarCompatible φ →
      Work.ORHughesFree.IsHughesFreeEnv φ →
      ∀ H₀ : Subgroup G₀, H₀.FG → H₀ ≠ ⊥ →
        Nonempty (Work.ORHughesFree.Thm61Step ℂ G₀ U φ H₀))
    {K : Type} [Field K] (φK : K →+* ℂ) : DivLoc K G φK :=
  divLoc_of_hstepComplex_of_epic (hstepOnComplex_of_thm61Step' hHF hN6)
    isEpic_starClosureCod_countableEnvelope φK

/-- **The deliverable, with Proposition 3.11 in the `U(G)` vocabulary** — the form in which node
ORP311 states it (`Work.ORDivLoc.Prop311OnComplex`). -/
theorem divLoc_of_thm61StepComplexU {G : Type} [Group G] [Countable G]
    (h311 : Prop311OnComplex G)
    (hN6 : ∀ {G₀ : Type} [Group G₀] [Work.ORHughesFree.LocallyIndicable G₀] {U : Type} [Ring U]
      [StarRing U] [Work.ORHughesFree.IsStarRegular U],
      Work.ORHughesFree.IsPositiveDefiniteStarRegular U →
      ∀ (φ : MonoidAlgebra ℂ G₀ →+* U) (rkU : Work.ORHughesFree.SylvesterRank U),
        rkU.IsFaithful →
      Work.ORHughesFree.IsEpic φ → Work.ORHughesFree.StarCompatible φ →
      Work.ORHughesFree.IsHughesFreeEnv φ →
      ∀ H₀ : Subgroup G₀, H₀.FG → H₀ ≠ ⊥ →
        Nonempty (Work.ORHughesFree.Thm61Step ℂ G₀ U φ H₀))
    {K : Type} [Field K] (φK : K →+* ℂ) : DivLoc K G φK :=
  divLoc_of_thm61StepComplex' (prop311OnComplexClosure_of_complex h311) hN6 φK

end Work.ORDivLoc
