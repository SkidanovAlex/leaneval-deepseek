import Mathlib
import Submission.Work.SymQuot.CurveIso
import Submission.Work.SymQuot.Sym.sym_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SymQuot.Sym

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-- **The quotient map `C¹ ⟶ Sym¹ C` is an isomorphism.**

This is the content of `Sym.sym_one` (the group `S₁` is trivial, so `C¹/S₁ = C¹ ≅ C`) made
explicit: the invariance of the projection `C¹ ⟶ C` (which factors through the quotient map as
`quot ≫ u = proj`) and the *uniqueness* part of the universal property of the quotient applied to
the quotient map itself (which gives `u ≫ (C ≅ C¹ ⟶ Sym¹ C) = 𝟙`). -/
theorem isIso_quot_one {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [Work.SymQuot.CurveAffineCover C] : IsIso (Work.SymQuot.Sym.quot C 1) := by
  let e : C.toOver ≅ Work.SymQuot.prod C.toOver 1 := prodOneIso C
  have hinv : e.inv = Work.SymQuot.proj C.toOver 1 0 := rfl
  -- The projection `C¹ ⟶ C` is invariant under the (trivial) action of `S₁`.
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
  refine CategoryTheory.IsIso.mk ⟨u ≫ e.hom, ?_, ?_⟩
  · rw [← CategoryTheory.Category.assoc, hu, CategoryTheory.Iso.inv_hom_id]
  · rw [CategoryTheory.Category.assoc, hwuniq _ h1, hwuniq _ h2]

open CategoryTheory Limits AlgebraicGeometry in
theorem curveIso_isIso {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    [Work.SymQuot.CurveAffineCover C] : IsIso (Work.SymQuot.Sym.curveIso C) := by
  haveI hq : IsIso (Work.SymQuot.Sym.quot C 1) := isIso_quot_one C
  rw [Work.SymQuot.Sym.curveIso_eq]
  infer_instance

end Work.SymQuot.Sym
