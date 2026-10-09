import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.sylow_descend
import Submission.Work.SSGRoute.ext_res_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

/-- Restricting the trivial `H'`-module `Coeff` along a group isomorphism `e : H ≃* H'` gives the
trivial `H`-module `Coeff`.  (Definitional: both representations have `ρ = 1`.) -/
theorem res_unitRep_eq {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    Rep.res e.toMonoidHom (unitRep H') = unitRep H := rfl

/-- Restricting `Rep Coeff (-)` along a group *isomorphism* is an equivalence of categories. -/
theorem resFunctor_isEquivalence_toMonoidHom {H H' : Type} [Group H] [Group H'] (e : H ≃* H') :
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.toMonoidHom).IsEquivalence :=
  Work.SSGRoute.resFunctor_isEquivalence (k := SSGRoute.PTExt.Coeff) e.symm

/-- **Change of groups along an isomorphism of groups on `Ext`-cohomology.**  For a group
isomorphism `e : H ≃* H'` and a `Coeff = ULift ℤ` representation `A` of `H'`, the cohomology
`Hⁿ(H', A) = extH A n` and the cohomology of the restriction `Rep.res e.toMonoidHom A` along `e`
are additively isomorphic.

Route.  `Work.SSGRoute.extRes e.toMonoidHom : extH A n → extH (Rep.res e.toMonoidHom A) n` and
`Work.SSGRoute.extRes e.symm.toMonoidHom` in the other direction are mutually inverse:
* `Work.SSGRoute.SylowDesc.extRes_comp_aux` gives
  `extRes (ψ.comp φ) x = extRes φ (extRes ψ x)`, so
  `extRes (e.symm.toMonoidHom.comp e.toMonoidHom) x = extRes e.toMonoidHom (extRes e.symm.toMonoidHom x)`;
* `e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H'` and
  `e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H` (by `MonoidHom.ext` +
  `e.symm_apply_apply` / `e.apply_symm_apply`);
* `Work.SSGRoute.extRes_id : extRes (MonoidHom.id G) x = x`.
Additivity of `extRes` is `Work.SSGRoute.extRes_add`, so the two maps assemble into an `AddEquiv`.
(The type displays `extH (Rep.res e.toMonoidHom A) n` for the target group; the underlying
`Abelian.Ext` spelling is `Rep.res e.toMonoidHom (unitRep H')`, which is definitionally
`unitRep H`.)

Here we obtain the same statement from the (stronger) categorical fact that
`Rep.resFunctor e.toMonoidHom` is an *equivalence* of abelian categories
(`Work.SSGRoute.resFunctor_isEquivalence_toMonoidHom`), so that its induced map on `Ext` is
bijective (`Functor.mapExt_bijective_of_preservesProjectiveObjects`) and hence — being additive —
an `AddEquiv`; the only point needing care is that `Rep.res e.toMonoidHom (unitRep H')` is
definitionally the trivial `H`-module, which is `res_unitRep_eq` (`rfl`). -/
theorem nonempty_extH_addEquiv_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (A : Rep SSGRoute.PTExt.Coeff H') (n : ℕ) :
    Nonempty (SSGRoute.PTExt.extH A n ≃+
      SSGRoute.PTExt.extH (Rep.res e.toMonoidHom A) n) := by
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence_toMonoidHom e
  refine ⟨AddEquiv.ofBijective
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.toMonoidHom).mapExtAddHom
      (SSGRoute.PTExt.unitRep H') A n) ?_⟩
  exact Functor.mapExt_bijective_of_preservesProjectiveObjects _ _ _ _

end Work.SSGRoute
