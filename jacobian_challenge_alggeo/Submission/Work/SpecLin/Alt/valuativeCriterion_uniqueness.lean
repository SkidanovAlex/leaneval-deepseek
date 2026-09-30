import Mathlib
import Submission.Work.SpecLin.Alt.CurveAffine
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

namespace Work.SpecLin.Alt

/-- **Uniqueness part of the valuative criterion for `phi`.**

`C` a smooth proper geometrically irreducible curve over a field `K`, `W ⊆ C` an open subscheme,
`s` a section of the structure sheaf over `W`, and `phi W s : W ⟶ 𝔸¹_K` the morphism over
`Spec K` whose coordinate function is `s` (see `Submission/Work/SpecLin/Alt/CurveAffine.lean`).
Then two lifts of a valuative square over `phi W s` agree.

Proof.  Let `l₁ l₂ : Spec R ⟶ W.toScheme` be lifts of a valuative square over `phi W s`, with
`R` a valuation ring and fraction field `L`.  Composing with the open immersion `W.ι` gives two
lifts of the valuative square over `C.hom : C.left ⟶ Spec K` with top map `i₁ ≫ W.ι` and bottom
map `i₂ ≫ (𝔸¹_K ⟶ Spec K)` (use `phi_over : phi W s ≫ (𝔸¹_K ⟶ Spec K) = W.ι ≫ C.hom`).  Since
`C.hom` is proper (`Curve.instIsProper`), the uniqueness part of the valuative criterion for
`C.hom` (`AlgebraicGeometry.IsSeparated.valuativeCriterion`) gives `l₁ ≫ W.ι = l₂ ≫ W.ι`, and
`W.ι` is a monomorphism (`AlgebraicGeometry.IsOpenImmersion.mono`), so `l₁ = l₂`. -/
theorem valuativeCriterion_uniqueness {K : Type*} [Field K] {C : Work.CurveBasics.Curve K}
    (W : C.left.Opens) (s : C.left.presheaf.obj (Opposite.op W)) :
    AlgebraicGeometry.ValuativeCriterion.Uniqueness (Work.SpecLin.Alt.phi W s) := by
  intro S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  -- `W.ι ≫ C.hom = phi W s ≫ A1Over K`, the compatibility of `phi` with the structure maps.
  have hφ : W.ι ≫ C.hom = phi W s ≫ A1Over K := (phi_over C s).symm
  -- The valuative square over `C.hom` obtained by composing with `W.ι`.
  let S' : AlgebraicGeometry.ValuativeCommSq C.hom :=
    { R := S.R
      K := S.K
      i₁ := S.i₁ ≫ W.ι
      i₂ := S.i₂ ≫ A1Over K
      commSq := ⟨by
        rw [Category.assoc, hφ, ← Category.assoc, S.commSq.w, Category.assoc]⟩ }
  -- `C.hom` is separated, so the lifts of this square are unique.
  haveI : Subsingleton S'.commSq.LiftStruct :=
    AlgebraicGeometry.IsSeparated.valuativeCriterion C.hom S'
  let L₁ : S'.commSq.LiftStruct :=
    { l := l₁ ≫ W.ι
      fac_left := by rw [← Category.assoc, hl₁]
      fac_right := by rw [Category.assoc, hφ, ← Category.assoc, hl₁'] }
  let L₂ : S'.commSq.LiftStruct :=
    { l := l₂ ≫ W.ι
      fac_left := by rw [← Category.assoc, hl₂]
      fac_right := by rw [Category.assoc, hφ, ← Category.assoc, hl₂'] }
  have h : l₁ ≫ W.ι = l₂ ≫ W.ι := congrArg CommSq.LiftStruct.l (Subsingleton.elim L₁ L₂)
  exact CommSq.LiftStruct.ext ((cancel_mono W.ι).mp h)

end Work.SpecLin.Alt
