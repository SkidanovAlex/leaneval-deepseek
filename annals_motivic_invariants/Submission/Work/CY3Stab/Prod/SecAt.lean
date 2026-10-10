import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Prod.ProdFibDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.SecAt` — the section of the cylinder over an arbitrary rational point

`Work.CY3Stab.Prod.sec` is the section of the cylinder `WX = 𝔸ᵏ × X` over the *origin* of `𝔸ᵏ`
(the fibre `{0} × X`, identified with `X` by the projection `p : WX ⟶ X`).  For the descent of
`IsIsoAt` along the cylinder one needs the analogous section over an arbitrary point
`s : Spec 𝕜 ⟶ 𝔸ᵏ` (a `𝕜`-rational point of affine space), i.e. the inclusion of the fibre
`q^{-1}(s) = X` of the second projection `q : WX ⟶ 𝔸ᵏ`.

`secAt k X s` is that inclusion.  It is a section of `q` (`secAt_q`) and, since `p` restricted to
`q^{-1}(s)` is an isomorphism onto `X`, a section of `p` as well (`secAt_p`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The section of the cylinder over a `𝕜`-rational point `s` of affine space**, i.e. the
inclusion of the fibre of `WX = 𝔸ᵏ ×_{Spec 𝕜} X ⟶ 𝔸ᵏ` over `s`.  The hypothesis `hs` says that
`s` is a section of the structure morphism `𝔸ᵏ ⟶ Spec 𝕜`, i.e. a `𝕜`-rational point. -/
noncomputable def secAt (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (s : Spec (CommRingCat.of 𝕜) ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)
    (hs : s ≫ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 _) :
    X ⟶ Work.CY3Stab.WProd (𝕜 := 𝕜) X k :=
  pullback.lift ((X ↘ Spec (CommRingCat.of 𝕜)) ≫ s) (𝟙 X) (by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- `secAt` is a section of the projection onto `X`. -/
theorem secAt_p (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (s : Spec (CommRingCat.of 𝕜) ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)
    (hs : s ≫ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 _) :
    secAt (𝕜 := 𝕜) k X s hs ≫ pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 X :=
  pullback.lift_snd _ _ _

/-- `secAt` lands over `s`: it is a section of `WX ⟶ 𝔸ᵏ` over `s`. -/
theorem secAt_q (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (s : Spec (CommRingCat.of 𝕜) ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k)
    (hs : s ≫ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 _) :
    secAt (𝕜 := 𝕜) k X s hs ≫ pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜)) = (X ↘ Spec (CommRingCat.of 𝕜)) ≫ s :=
  pullback.lift_fst _ _ _

/-- The origin section is `secAt` at the origin `wPt`. -/
theorem secAt_wPt (k : ℕ) (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] :
    secAt (𝕜 := 𝕜) k X (wPt (𝕜 := 𝕜) k) (wPt_over (𝕜 := 𝕜) k) = sec (𝕜 := 𝕜) k X := rfl

end

end Work.CY3Stab.Prod

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]


/-- The structure morphism `X ⟶ Spec 𝕜` of a scheme over the base field.  This is the scoped
notation `X ↘ Spec 𝕜` written out, so that statements can mention it without opening the
`AlgebraicGeometry` scope. -/
noncomputable abbrev overHom (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] :
    X ⟶ Spec (CommRingCat.of 𝕜) :=
  (inferInstance : X.Over (Spec (CommRingCat.of 𝕜))).hom

/-- **A `𝕜`-rational point of affine space**: a morphism `Spec 𝕜 ⟶ 𝔸ᵏ` which is a section of the
structure morphism.  Written with `CategoryStruct` primitives (rather than the category notation
`≫` and `𝟙`, which are available only after opening the `CategoryTheory` scope) so that statements
mentioning it can be elaborated in a bare environment. -/
def IsSection (k : ℕ) (s : Spec (CommRingCat.of 𝕜) ⟶ Work.CY3Stab.AffineK (𝕜 := 𝕜) k) : Prop :=
  CategoryTheory.CategoryStruct.comp s
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) =
    CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of 𝕜))


end

end Work.CY3Stab.Prod
