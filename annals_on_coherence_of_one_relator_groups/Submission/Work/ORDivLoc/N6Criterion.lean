/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Node N6's criterion over `C`: the inputs of `thm61Step_nonempty` at the `*`-regular closure

`Work.ORHughesFree.Section6.thm61Step_nonempty` constructs the induction environment
`Work.ORHughesFree.Thm61Step K G U phi H` from

* `hpos : IsPositiveDefiniteStarRegular U`,
* `rkU : SylvesterRank U` and `hfaith : rkU.IsFaithful`,
* `hphi : IsEpic phi`,
* `hstar : StarCompatible phi`,
* `hHF : IsHughesFreeEnv phi` ([JZLA20, Proposition 3.11]).

This file gathers the *side conditions* for the application at `(K := C, G := ↥H, U := V_C,
phi := starClosureCod ...)`, where `V_C = R(C[H], U(G))` is the `*`-regular closure of the image of
`C[H]` in `U(G)`:

* `hpos` -- `Work.ORDivLoc.isPositiveDefiniteStarRegular_starClosure`;
* `rkU`, `hfaith` -- `Work.ORDivLoc.Rank.exists_faithful_sylvesterRank_starClosure`;
* `hstar` -- `Work.ORDivLoc.starCompatible_starClosureCod`;
* `hphi` -- `Work.ORDivLoc.Closure.isEpic_starClosureCod_complex`;
* `hHF` -- `Work.ORDivLoc.Prop311OnComplexClosure`, i.e. [JZLA20, Proposition 3.11] over `C` in the
  `*`-regular-closure vocabulary (`Work.ORDivLoc.prop311OnComplexClosure_of_complex` converts it
  from the `U(G)`-vocabulary form `Work.ORDivLoc.Prop311OnComplex`, which is the statement node
  ORP311 proves).

The conclusion is `Work.ORDivLoc.HstepOnComplex G`, node N6's raw input for the whole group `G`.

## Why over `C` and not over an arbitrary `K`

The epicity of the structure map into the `*`-regular closure fails for a general coefficient field
`K` (the stars of the scalars need not be ring expressions in the image:
`Work.ORDivLoc.Closure.isEpic_starClosureCod`'s docstring has a counterexample with the trivial
group and `K = Q(alpha)`, `alpha` a non-real cube root of `2`); it holds over `C`, where
`C[↥H] -> U(G)` is a `*`-homomorphism.  `Work.ORDivLoc.Complex` then reduces an arbitrary
`phiK : K ->+* C` to the `C` statement by `V_K <= V_C` and division closedness.
-/
import Submission.Work.ORDivLoc.Complex
import Submission.Work.ORDivLoc.Prop311
import Submission.Work.ORDivLoc.Rank.exists_faithful_sylvesterRank_starClosure

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc

/-- **Node N6's raw input `HstepOnComplex`, from `thm61Step_nonempty`.**

`hN6` is the engine's construction of the induction environment, stated in the generality of
`Work.ORHughesFree.Section6.thm61Step_nonempty` (at `Type`, over `C`); `hEpic` is the epicity of
the structure map into the `*`-regular closure over `C`
(`Work.ORDivLoc.Closure.isEpic_starClosureCod_complex`); `hHF` is [JZLA20, Proposition 3.11] over
`C` (`Work.ORDivLoc.Prop311OnComplexClosure`).

The remaining side conditions are proved here: positive definiteness of `V_C`, the faithful
Sylvester rank function on `V_C`, the `*`-compatibility of the structure map, and the local
indicability of `↥H`. -/
theorem hstepOnComplex_of_thm61Step {G : Type} [Group G] [Countable G]
    (hEpic : ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
      Work.ORHughesFree.IsEpic
        (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H))
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
    HstepOnComplex G := by
  intro H hLI H₀ hfg hne
  haveI : Work.ORHughesFree.LocallyIndicable ↥H := locallyIndicable_of_orLocInd hLI
  obtain ⟨rkU, hfaith⟩ := Rank.exists_faithful_sylvesterRank_starClosure
    (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H
  exact hN6 (isPositiveDefiniteStarRegular_starClosure _ (RingHom.id ℂ) H)
    (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H) rkU hfaith
    (hEpic H hLI) (starCompatible_starClosureCod _ (RingHom.id ℂ) H) (hHF H hLI) H₀ hfg hne

/-- **The deliverable, with all of node N6's inputs explicit.**  From the construction
`thm61Step_nonempty` over `C` (as `hN6`), the epicity of the structure map, and
[JZLA20, Proposition 3.11] over `C` (as `hHF`), `DivLoc K G phiK` follows for every coefficient
field `K : Type` with an embedding `phiK : K ->+* C` -- hence the `hdiv` field of
`Work.ORFinal.FinalInput`. -/
theorem divLoc_of_thm61StepComplex {G : Type} [Group G] [Countable G]
    (hEpic : ∀ H : Subgroup G, Work.ORLocInd.Group.LocallyIndicable H →
      Work.ORHughesFree.IsEpic
        (starClosureCod (Work.ORBridgeLinnell.countableEnvelope G) (RingHom.id ℂ) H))
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
  divLoc_of_hstepComplex_of_epic (hstepOnComplex_of_thm61Step hEpic hHF hN6) hEpic φK

end Work.ORDivLoc
