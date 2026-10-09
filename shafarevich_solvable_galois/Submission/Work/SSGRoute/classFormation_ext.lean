import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_ext_cor_transfer
import Submission.Work.SSGRoute.e0b_bridge
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization
import Submission.NK.CFTLib.fundamentalClassElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class formation of the idèle class groups in the `Ext`/`Coeff` spelling

The Sylow descent `Work.SSGRoute.phi1_mono_sylow_in` needs one *arithmetic* input: for a finite
Galois extension `k ⊆ L` of number fields and a subgroup `S ≤ Gal(L/k)`, the corestriction
`cor : H²(S, C_L) → H²(Gal(L/k), C_L)` of the idèle class formation is injective (classically:
`Br(L/L^S) ↪ Br(L/k)`, the relative Brauer groups becoming `ℤ/[L:L^S] ↪ ℤ/[L:k]` under the
invariant map).

Here we transport both halves of `NK.GlobalCFT.CohomologicalFieldAxiom` for `L/k` — proved
unconditionally in NK from Hasse's fundamental class
(`NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement
NK.CFTLib.fundamentalClassElement`) — from the `ℤ`/group-cohomology spelling of `NK` to the
`Ext`/`Coeff` spelling of `Submission/Work/SSGRoute/PTDefs.lean` (`Coeff = ULift ℤ`), via

* the coefficient-ring transfer `NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer`
  (`classGroupRep = classesK` is `Rep.ofDistribMulAction CoeffInt G (Additive (IdeleClassGroup L))`,
  the same carrier with the same action as `IdeleClassGroup.rep`, so the transfer applies with
  `V := Additive (IdeleClassGroup L)`), and
* the `E0b` bridge `Work.SSGRoute.Bridge.E : groupCohomology A 2 ≃+ extH A 2`,

and then feed the result into `Work.SSGRoute.CorTransfer.extCor_injective_of_fundamental`
(`Submission/Work/SSGRoute/phi1_ext_cor_transfer.lean`), whose two hypotheses are exactly

* `Work.SSGRoute.extH_classesK_two_fundamental` (already on disk: `∃ α : extH (classesK k L) 2,
  addOrderOf α = Nat.card (L ≃ₐ[k] L)`), and
* `Work.SSGRoute.ClassFormation.extH_classesK_two_card_sub` (proved here:
  `Nat.card (extH (Rep.res S.subtype (classesK k L)) 2) = Nat.card ↥S`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace ClassFormation

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **The order of `H²(S, C_L)` in the `Ext` spelling.**  For a finite Galois extension `k ⊆ L` of
number fields and a subgroup `S ≤ Gal(L/k)`, the second cohomology of the idèle class group with
coefficients restricted to `S` has order the order of `S` (the order computation of the class
formation, `NK.GlobalCFT.CohomologicalFieldAxiom.h2_card`, transported along the coefficient-ring
transfer and the `E0b` bridge). -/
theorem extH_classesK_two_card_sub {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (S : Subgroup (L ≃ₐ[k] L)) :
    Nat.card (extH (Rep.res S.subtype (classesK k L)) 2) = Nat.card ↥S := by
  classical
  -- the class formation at the level `L/k`
  have hfc : NK.GlobalCFT.CohomologicalFieldAxiom k L :=
    NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement
      NK.CFTLib.fundamentalClassElement
  -- the order computation in the `ℤ`/group-cohomology spelling
  have h2 : Nat.card (groupCohomology (Rep.res S.subtype (NK.GlobalCFT.IdeleClassGroup.rep k L)) 2)
      = Nat.card ↥S := hfc.h2_card S
  -- the coefficient-ring transfer, at the group `↥S`
  obtain ⟨e₂⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer
    (k := Coeff) (k' := ℤ) (G := ↥S) (V := Additive (NK.GlobalCFT.IdeleClassGroup L))
  -- the `E0b` bridge, at the group `↥S`
  have hb := Bridge.E 2 ↥S (Rep.res S.subtype (classesK k L))
  calc Nat.card (extH (Rep.res S.subtype (classesK k L)) 2)
      = Nat.card (groupCohomology (Rep.res S.subtype (classesK k L)) 2) :=
        (Nat.card_congr hb.toEquiv).symm
    _ = Nat.card (groupCohomology (Rep.res S.subtype (NK.GlobalCFT.IdeleClassGroup.rep k L)) 2) :=
        Nat.card_congr e₂.toEquiv
    _ = Nat.card ↥S := h2

/-- **Corestriction is injective on the class formation.**

For a finite Galois extension `k ⊆ L` of number fields and a subgroup `S ≤ Gal(L/k)`, the
corestriction `cor : H²(S, C_L) → H²(Gal(L/k), C_L)` of the idèle class formation is injective
(classically `Br(L/L^S) ↪ Br(L/k)`).

This is the arithmetic input of the Sylow descent of `Work.SSGRoute.phi1_mono_sylow` /
`Work.SSGRoute.phi1_mono_sylow_in`: a value over `k' = K^P` whose corestriction to `Gal(L/k)`
vanishes must itself vanish.  No coprimality of `[k' : k]` with `p` is needed.

Proof: `Work.SSGRoute.CorTransfer.extCor_injective_of_fundamental`
(`Submission/Work/SSGRoute/phi1_ext_cor_transfer.lean`) reduces the injectivity to the existence of
an element `α` of `H²(Gal(L/k), C_L)` of order `|Gal(L/k)|` — the fundamental class, transported to
the `Ext` spelling in `Work.SSGRoute.extH_classesK_two_fundamental` — together with the order
computation `Nat.card (H²(S, C_L)) = |S|` of
`Work.SSGRoute.ClassFormation.extH_classesK_two_card_sub`. -/
theorem extCor_injective_classesK {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (S : Subgroup (L ≃ₐ[k] L)) [DecidableRel (QuotientGroup.rightRel S)]
    [Fintype ((L ≃ₐ[k] L) ⧸ S)] :
    Function.Injective (extCor S (unitRep (L ≃ₐ[k] L)) (classesK k L) 2) :=
  CorTransfer.extCor_injective_of_fundamental S (classesK k L) 2
    (extH_classesK_two_fundamental k L) (extH_classesK_two_card_sub S)

end ClassFormation

end Work.SSGRoute
