import Mathlib
import Submission.Work.SymQuot.Sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



namespace Work.SymQuot.Sym

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

/-- The `1`-fold product of a curve with itself is the curve itself: the projection
`C¹ = C ×_K ⋯ ×_K C ⟶ C` is an isomorphism, with inverse the lift of the identity. -/
noncomputable def prodOneIso {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) :
    C.toOver ≅ Work.SymQuot.prod C.toOver 1 :=
  CategoryTheory.Iso.mk
    (CategoryTheory.Limits.Pi.lift (fun _ : Fin 1 => 𝟙 C.toOver))
    (Work.SymQuot.proj C.toOver 1 0)
    (CategoryTheory.Limits.Pi.lift_comp_π _ 0)
    (by
      apply CategoryTheory.Limits.Pi.hom_ext
      intro i
      rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π,
        CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp,
        show i = (0 : Fin 1) from Subsingleton.elim i 0])

/-- **`Sym¹ C = C`.**  The first symmetric power of a curve is the curve itself.

The group `S_1` is trivial, so the quotient `C¹/S_1` of the quotient construction
(`Submission.Work.SymQuot.SymData`) is `C¹`, and `C¹ ≅ C` (`prodOneIso`).  Concretely: the
projection `C¹ ⟶ C` is invariant, so it factors through the quotient map as
`Sym.quot C 1 ≫ u = proj`; the resulting `u : Sym C 1 ⟶ C` is an isomorphism, with inverse
`C ≅ C¹ ⟶ Sym C 1`.  The multiplicative identity `u ≫ u⁻¹ = 𝟙` is proved by the *uniqueness*
part of the universal property of the quotient (`Sym.desc`), applied to the quotient map
itself. -/
theorem sym_one {K : Type*} [Field K] (C : Work.CurveBasics.Curve K) :
    Nonempty (Work.SymQuot.Sym C 1 ≅ C.toOver) := by
  let e : C.toOver ≅ Work.SymQuot.prod C.toOver 1 := prodOneIso C
  have hinv : e.inv = Work.SymQuot.proj C.toOver 1 0 := rfl
  -- The projection `C¹ ⟶ C` is invariant under the (trivial) action of `S_1`.
  obtain ⟨u, hu, _⟩ := Work.SymQuot.Sym.desc C 1 e.inv (fun σ => by
    have h := Work.SymQuot.Product.permIso_hom_proj C.toOver σ.down (0 : Fin 1)
    rw [show σ.down.symm (0 : Fin 1) = 0 from Subsingleton.elim _ _] at h
    have h2 := congrArg CategoryTheory.Over.Hom.left h
    simp only [CategoryTheory.Over.comp_left] at h2
    rw [hinv]
    simpa [Work.SymQuot.symAction_hom, Work.SymQuot.permGAction, Work.SymQuot.proj] using h2)
  -- The quotient map is itself invariant, so it too factors through itself, uniquely.
  obtain ⟨_, _, hwuniq⟩ := Work.SymQuot.Sym.desc C 1 (Work.SymQuot.Sym.quot C 1)
    (fun σ => (Work.SymQuot.symData C 1).quotientMap_isInvariant σ)
  have h1 : Work.SymQuot.Sym.quot C 1
      ≫ (u ≫ (e.hom ≫ Work.SymQuot.Sym.quot C 1)) = Work.SymQuot.Sym.quot C 1 := by
    rw [← CategoryTheory.Category.assoc, hu, ← CategoryTheory.Category.assoc,
      CategoryTheory.Iso.inv_hom_id, CategoryTheory.Category.id_comp]
  have h2 : Work.SymQuot.Sym.quot C 1 ≫ 𝟙 (Work.SymQuot.Sym C 1)
      = Work.SymQuot.Sym.quot C 1 := CategoryTheory.Category.comp_id _
  refine ⟨CategoryTheory.Iso.mk u (e.hom ≫ Work.SymQuot.Sym.quot C 1) ?_ ?_⟩
  · rw [hwuniq _ h1, hwuniq _ h2]
  · rw [CategoryTheory.Category.assoc, hu]
    exact CategoryTheory.Iso.hom_inv_id e

end Work.SymQuot.Sym
