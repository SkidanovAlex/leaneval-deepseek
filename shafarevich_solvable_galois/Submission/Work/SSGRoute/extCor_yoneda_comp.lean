import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Have
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The projection formula for corestriction along the Yoneda pairing.**

For a finite group `G`, a subgroup `S ≤ G`, and `G`-modules `H`, `M`, `A`, the corestriction
`extCor S H A` on `Ext`-groups is compatible with right composition with a class
`x ∈ Ext^r_G(M, A)`: pulling `x` back to `S` and then corestricting the result is the same as
corestricting first and then composing with `x`.

This is the `H = unitRep G` case of the general statement, which is what
`extCor_yoneda_comp` needs (`cor (b ∘ res x) = (cor b) ∘ x`). -/
theorem extCor_comp_extRes {G : Type} [Group G] [Fintype G] (S : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    {H M A : Rep SSGRoute.PTExt.Coeff G} {r s : ℕ}
    (x : CategoryTheory.Abelian.Ext M A r)
    (y : CategoryTheory.Abelian.Ext (Rep.res S.subtype H) (Rep.res S.subtype M) s) :
    Work.SSGRoute.extCor S H A (s + r) (y.comp (SSGRoute.PTExt.extRes S.subtype x) rfl)
      = (Work.SSGRoute.extCor S H M s y).comp x rfl := by
  -- the naturality of the trace `Res ⋙ Coind ⟹ 𝟭` on `Ext`
  have hnat : (Abelian.Ext.mapExactFunctor
        (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype) x).comp
        (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S A)) (add_zero r)
      = (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S M)).comp x (zero_add r) :=
    Work.SSGRoute.ext_mapExactFunctor_naturality_aux (C := Rep SSGRoute.PTExt.Coeff G)
      (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype)
      (Work.SSGRoute.coindTraceNat S) r M A x
  -- `mapExactFunctor` is compatible with the composition of exact functors
  have hfc : Abelian.Ext.mapExactFunctor (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype)
      (Abelian.Ext.mapExactFunctor (Rep.resFunctor S.subtype) x) =
      Abelian.Ext.mapExactFunctor
        (Rep.resFunctor S.subtype ⋙ Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype) x :=
    Work.SSGRoute.ext_mapExactFunctor_comp_functor_aux (C := Rep SSGRoute.PTExt.Coeff G)
      (D := Rep SSGRoute.PTExt.Coeff S) (E := Rep SSGRoute.PTExt.Coeff G)
      (Rep.resFunctor S.subtype) (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype) r M A x
  rw [Work.SSGRoute.extCor_apply, Work.SSGRoute.extCor_apply]
  rw [SSGRoute.PTExt.extRes]
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [hfc]
  -- reassociate the left hand side and apply the naturality of the trace
  conv_lhs =>
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [hnat]
  let ηH := (Rep.resCoindAdjunction SSGRoute.PTExt.Coeff S.subtype).unit.app H
  let βy := Abelian.Ext.mapExactFunctor (Rep.coindFunctor SSGRoute.PTExt.Coeff S.subtype) y
  let Ar := (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S M)).comp x (zero_add r)
  let X := (Abelian.Ext.mk₀ ηH).comp βy (zero_add s)
  have step4 : (Abelian.Ext.mk₀ ηH).comp (βy.comp Ar rfl) (zero_add (s + r))
      = X.comp Ar rfl :=
    (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ ηH) βy Ar (zero_add s) rfl
      (by omega : 0 + s + r = s + r)).symm
  have step5 : X.comp Ar rfl
      = (X.comp (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S M)) (add_zero s)).comp x rfl :=
    (Abelian.Ext.comp_assoc X (Abelian.Ext.mk₀ (Work.SSGRoute.coindTrace S M)) x (add_zero s)
      (zero_add r) (by omega : s + 0 + r = s + r)).symm
  exact step4.trans step5

theorem extCor_yoneda_comp {G : Type} [Group G] [Fintype G] (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] {M A : Rep SSGRoute.PTExt.Coeff G} {r s : ℕ} (x : CategoryTheory.Abelian.Ext M A r) (b : CategoryTheory.Abelian.Ext (Rep.res S.subtype (SSGRoute.PTExt.unitRep G)) (Rep.res S.subtype M) s) : Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) A (s + r) (b.comp (SSGRoute.PTExt.extRes S.subtype x) rfl) = (Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) M s b).comp x rfl := by
  exact extCor_comp_extRes (H := SSGRoute.PTExt.unitRep G) S x b

end Work.SSGRoute
