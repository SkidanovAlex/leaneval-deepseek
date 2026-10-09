import Mathlib
import Submission.Work.SSGRoute.PT.e1aBetaCan_localAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (T2) of `PT/NOTE_e1aChainC_localComparison.md` §9.2: the `Ext`-transport along a group
# isomorphism, as a *named* map with its two computation rules

`Work.SSGRoute.ext_res_mulEquiv_n` supplies the transport `Ext (res X) (res Y) n ≃+ Ext X Y n` along
a group isomorphism `e` as a `Nonempty`-witness; the comparison square `(SQ)` of the E1a node
(`Submission/Work/SSGRoute/NOTE_e1a_session5.md` §0–§2) needs it as a *named* family with its rules
on the generators of the dictionary (`mk₀`-classes and the cover class `S.extClass`, hence
`PhiE = S.extClass.precomp …`).

Here the witness of `ext_res_mulEquiv_n` is exposed as a definition `resMulEquiv` and its two rules
are proved from Mathlib's `Ext.mapExactFunctor_mk₀` / `Ext.mapExactFunctor_comp` —
`F.mapExtAddHom` is `Ext.mapExactFunctor F` (`Functor.mapExtAddHom_apply`).  The `∃`-over-a-family
form of this statement (the prose statement of §9.2) times out in `whnf` when Lean tries to
synthesize the `AddCommGroup` instance for the `Ext`-family under the `∃`-binder; defining the
family first avoids that entirely.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- **The forward direction, named** (the witness of `ext_res_mulEquiv_n`). -/
def resMulEquivSymm {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} Coeff G) (n : ℕ) :
    Abelian.Ext X Y n ≃+
    Abelian.Ext (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) n :=
  haveI : (Rep.resFunctor (k := Coeff) e.symm.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence e
  AddEquiv.ofBijective ((Rep.resFunctor (k := Coeff) e.symm.toMonoidHom).mapExtAddHom X Y n)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
      (Rep.resFunctor (k := Coeff) e.symm.toMonoidHom) X Y n)

theorem resMulEquivSymm_apply {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} Coeff G) (n : ℕ) (z : Abelian.Ext X Y n) :
    resMulEquivSymm e X Y n z
      = (Rep.resFunctor (k := Coeff) e.symm.toMonoidHom).mapExtAddHom X Y n z :=
  AddEquiv.ofBijective_apply _ _ z

/-- **The `Ext`-transport along a group isomorphism, as a named map.**  This is the witness of
`Work.SSGRoute.ext_res_mulEquiv_n`, with its definition exposed so that its computation rules can be
stated. -/
def resMulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} Coeff G) (n : ℕ) :
    Abelian.Ext (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) n ≃+
    Abelian.Ext X Y n :=
  (resMulEquivSymm e X Y n).symm

theorem resMulEquiv_apply {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} Coeff G) (n : ℕ)
    (z : Abelian.Ext (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) n) :
    resMulEquiv e X Y n z = (resMulEquivSymm e X Y n).symm z := rfl

/-- **Rule (i) of (T2)**: the transport is the identity on `mk₀`-classes. -/
theorem resMulEquiv_mk₀ {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} Coeff G) (g : X ⟶ Y) :
    resMulEquiv e X Y 0
        (Abelian.Ext.mk₀ ((Rep.resFunctor e.symm.toMonoidHom).map g)) = Abelian.Ext.mk₀ g := by
  rw [resMulEquiv_apply, AddEquiv.symm_apply_eq, resMulEquivSymm_apply,
    Functor.mapExtAddHom_apply]
  simp only [CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]

/-- **Rule (ii) of (T2)**: the transport commutes with the Yoneda composition, in the form used by
the comparison square (the degree-`0` factor is an `mk₀`-class). -/
theorem resMulEquiv_comp_mk₀ {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y Z : Rep.{0} Coeff G) (g : X ⟶ Y) {b c : ℕ} (h : 0 + b = c)
    (z : Abelian.Ext (Rep.res e.symm.toMonoidHom Y) (Rep.res e.symm.toMonoidHom Z) b) :
    resMulEquiv e X Z c
        ((Abelian.Ext.mk₀ ((Rep.resFunctor e.symm.toMonoidHom).map g)).comp z h)
      = (Abelian.Ext.mk₀ g).comp (resMulEquiv e Y Z b z) h := by
  rw [resMulEquiv_apply, AddEquiv.symm_apply_eq, resMulEquivSymm_apply,
    Functor.mapExtAddHom_apply, CategoryTheory.Abelian.Ext.mapExactFunctor_comp]
  congr 1
  · simp only [CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀]
  · rw [resMulEquiv_apply]
    exact (AddEquiv.apply_symm_apply (resMulEquivSymm e Y Z b) z).symm

end

end Work.SSGRoute.ExtChain
