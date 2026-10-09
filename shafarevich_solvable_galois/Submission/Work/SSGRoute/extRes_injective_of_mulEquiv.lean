import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_res_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory

/-- **Restriction of `Ext` along a group isomorphism is injective.**

For a group isomorphism `e : H ≃* H'` and representations `X Y` of `H'`, the change-of-group map
`extRes e.toMonoidHom : Extⁿ_{H'}(X, Y) → Extⁿ_H(res e X, res e Y)` is injective.  (In fact it is a
bijection: `Rep.resFunctor e.toMonoidHom` is an equivalence of abelian categories, hence full,
faithful and projective-preserving, so `Functor.mapExt_bijective_of_preservesProjectiveObjects`
applies — see `Work.SSGRoute.resFunctor_isEquivalence` and the model proof in
`Work.SSGRoute.ext_res_mulEquiv`, which does the case `n = 1`.) -/
theorem extRes_injective_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (X Y : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff H') (n : ℕ) :
    Function.Injective (fun x : Abelian.Ext X Y n =>
      SSGRoute.PTExt.extRes e.toMonoidHom x) := by
  -- `Rep.resFunctor e.toMonoidHom` is an equivalence of categories (restriction along the inverse
  -- isomorphism is a quasi-inverse), hence full, faithful and projective-preserving.
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.toMonoidHom).IsEquivalence := by
    simpa using resFunctor_isEquivalence (k := SSGRoute.PTExt.Coeff) (e := e.symm)
  intro a b hab
  -- `extRes f x` is definitionally `x.mapExactFunctor (Rep.resFunctor f)`, which is
  -- `mapExtAddHom` evaluated at `x`; that map is bijective by the general criterion.
  have hbij := Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.toMonoidHom) X Y n
  exact hbij.1 hab

end Work.SSGRoute
