import Submission.Work.SSGRoute.E1aClean.BaseChangeTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The left-congruence of `Ext`

`Work.SSGRoute.ext_congr_right` covers the *second* (coefficient) variable of `Ext` and is stated as
a `Nonempty`.  The level-change transport also needs the *first*-variable congruence, i.e.
contravariance of `Ext` along an isomorphism `e : M ≅ M'` of the first variable.  This is the
`precomp`-mirror of `E1aClean.extPostIsoHom`: Yoneda composition with `mk₀ e.hom` on the left. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {G : Type} [Group G]

/-- **The left-congruence of the first variable of `Ext`**: for `e : M ≅ M'`,
`Ext M' N n →+ Ext M N n`, by Yoneda composition with `mk₀ e.hom` on the left. -/
def extCongrLeft {M M' N : Rep.{0} SSGRoute.PTExt.Coeff G} (e : M ≅ M') (n : ℕ) :
    Abelian.Ext M' N n →+ Abelian.Ext M N n where
  toFun x := Abelian.Ext.comp (Abelian.Ext.mk₀ e.hom) x (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp [Abelian.Ext.comp_add]

/-- The computation rule of `extCongrLeft`: it is Yoneda composition with `mk₀ e.hom`. -/
theorem extCongrLeft_apply {M M' N : Rep.{0} SSGRoute.PTExt.Coeff G} (e : M ≅ M') (n : ℕ)
    (x : Abelian.Ext M' N n) :
    extCongrLeft e n x = Abelian.Ext.comp (Abelian.Ext.mk₀ e.hom) x (zero_add n) := rfl

/-- **`extCongrLeft` is the identity on `mk₀`-classes.** -/
theorem extCongrLeft_mk₀ {M M' N : Rep.{0} SSGRoute.PTExt.Coeff G} (e : M ≅ M')
    (g : M' ⟶ N) :
    extCongrLeft e 0 (Abelian.Ext.mk₀ g) = Abelian.Ext.mk₀ (e.hom ≫ g) := by
  rw [extCongrLeft_apply]
  exact Abelian.Ext.mk₀_comp_mk₀ e.hom g

end

end Work.SSGRoute.E1aClean
