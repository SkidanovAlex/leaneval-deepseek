import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- **The weight of an image is transported by a residue-field matching bijection.**

If `e : A ≃ B` matches the residue fields of `A ⊆ X` and `B ⊆ Y` (`ResEquiv 𝕜 a (e a)`), and
`p : X → P`, `q : Y → Q` are injective maps sending `ResEquiv`-related points to `ResEquiv`-related
points, then the `𝕜`-weights (`Work.Motivic.wgt`: the number of points of a set whose residue field
is `𝕜`-isomorphic to `κ(w)`) of the two images agree.

This is the bookkeeping by which the class-preserving bijection of exceptional divisors
(`Work.CY3Stab.Prod.exists_bijection_of_ncard_of_resEquiv`) is transported to the cylinder points,
the cylinder map `x ↦ prodPt X x k` being injective with
`ResEquiv 𝕜 x y → ResEquiv 𝕜 (prodPt X x k) (prodPt Y y k)`.

Proof route: `Work.Motivic.wgt_eq_of_bijection` (in `Submission.Work.Motivic.cInv_add_defs`) applied
to the bijection `↥(p '' A) ≃ ↥(q '' B)` induced by `e` — send `p a ↦ q (e a)`; well defined by
`hp`, and the `ResEquiv` condition is `hpq (he a)`.  Constructing that bijection is the only work:
`(Equiv.Set.image p A hp).symm.trans (e.trans (Equiv.Set.image q B hq))`, or by hand with
`Set.ncard_congr`. -/
theorem wgt_image_eq_of_bijection {𝕜 : Type} [Field 𝕜]
    {X Y P Q W : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [P.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Q.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    {A : Set X} {B : Set Y} (p : X → P) (q : Y → Q)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (e : ↥A ≃ ↥B) (he : ∀ a : ↥A, ResEquiv 𝕜 a.1 (e a).1)
    (hpq : ∀ x y, ResEquiv 𝕜 x y → ResEquiv 𝕜 (p x) (q y)) (w : W) :
    Work.Motivic.wgt 𝕜 w (p '' A) = Work.Motivic.wgt 𝕜 w (q '' B) := by
  refine Work.Motivic.wgt_eq_of_bijection w
    ((Equiv.Set.image p A hp).symm.trans (e.trans (Equiv.Set.image q B hq))) ?_
  intro y
  -- `y` is `p a` for `a = (Equiv.Set.image p A hp).symm y`; the transported point is `q (e a)`.
  have hpy : p ((Equiv.Set.image p A hp).symm y).1 = y.1 :=
    congrArg Subtype.val ((Equiv.Set.image p A hp).apply_symm_apply y)
  rw [← hpy]
  exact hpq _ _ (he ((Equiv.Set.image p A hp).symm y))

end Work.CY3Stab.Prod
