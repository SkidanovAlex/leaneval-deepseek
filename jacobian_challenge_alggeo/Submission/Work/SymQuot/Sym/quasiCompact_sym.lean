import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Prod.isProper_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Sym

open CategoryTheory AlgebraicGeometry

/-- **Quasi-compactness is reflected by surjective morphisms.**  If `f` is surjective and
`f ≫ g` is quasi-compact, then so is `g`: the preimage under `g` of a quasi-compact open set is
the image under `f` of a quasi-compact open set, hence quasi-compact. -/
lemma quasiCompact_of_surjective_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Surjective f) (h : QuasiCompact (f ≫ g)) : QuasiCompact g := by
  constructor
  intro U hU hc
  have h1 : IsCompact ((f ≫ g) ⁻¹' U) := h.isCompact_preimage U hU hc
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at h1
  have hsurj : f '' (f ⁻¹' (g ⁻¹' U)) = g ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x, hy, rfl⟩
  rw [← hsurj]
  exact h1.image f.continuous

/-- A proper morphism is quasi-compact. -/
lemma quasiCompact_of_isProper {X Y : Scheme} (f : X ⟶ Y) (h : IsProper f) : QuasiCompact f :=
  @instQuasiCompactOfUniversallyClosed _ _ f (@IsProper.toUniversallyClosed _ _ _ h)

theorem quasiCompact_sym {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) : AlgebraicGeometry.QuasiCompact (Work.SymQuot.Sym C n).hom := by
  refine quasiCompact_of_surjective_comp (Work.SymQuot.Sym.quot C n).left
    (Work.SymQuot.Sym C n).hom (Work.SymQuot.Sym.quot_surjective C n) ?_
  rw [Work.SymQuot.Sym.quot_hom]
  exact quasiCompact_of_isProper _ (Work.SymQuot.Prod.isProper_prod C.toOver n)

end Work.SymQuot.Sym
