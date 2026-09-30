/-
# The valuative criterion with an explicit field of fractions

Two forms of the valuative criterion that are used in the construction of the branches of the
pencil at `h = 0`:

* `exists_extension_of_proper_field`: a `K`-point of a proper `k`-scheme `X`, where `R` is a
  valuation ring over `k` with field of fractions `K`, extends to an `R`-point;
* `eq_of_generic_eq`: if `X` is separated over `k` and two `R`-points agree after composing with
  the generic point `Spec K ⟶ Spec R`, then they are equal.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.exists_extension_of_proper

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.KeyLemma.Curve

/-- **Existence part of the valuative criterion, with an explicit field of fractions.** -/
theorem exists_extension_of_proper_field {k : Type u} [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra k R]
    {K : Type u} [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K]
    {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
    (x : Spec (CommRingCat.of K) ⟶ X.left)
    (hx : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ ρ : Spec (CommRingCat.of R) ⟶ X.left,
      (ρ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R))) ∧
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ ρ = x) := by
  have hVC : ValuativeCriterion X.hom := by
    have h : ((ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType)
        X.hom) := by
      rw [← IsProper.eq_valuativeCriterion]
      exact inferInstance
    exact h.1.1.1
  have hcomp : (algebraMap R K).comp (algebraMap k R) = algebraMap k K :=
    RingHom.ext fun c => (IsScalarTower.algebraMap_apply k R K c).symm
  have hcomm : x ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq X.hom :=
    { R := R
      K := K
      i₁ := x
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k R))
      commSq := ⟨hcomm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (ValuativeCriterion.existence hVC S).exists_lift
  exact ⟨l, hl₂, hl₁⟩

/-- **Uniqueness part of the valuative criterion**: two `R`-points of a separated `k`-scheme
which agree at the generic point are equal. -/
theorem eq_of_generic_eq {k : Type u} [Field k]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K]
    {X : Over (Spec (CommRingCat.of k))} [IsSeparated X.hom]
    {u v : Spec (CommRingCat.of R) ⟶ X.left}
    (hu : u ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (hv : v ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (h : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ u
        = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ v) :
    u = v := by
  have huniq := IsSeparated.valuativeCriterion X.hom
  have hcomp : (algebraMap R K).comp (algebraMap k R) = algebraMap k K :=
    RingHom.ext fun c => (IsScalarTower.algebraMap_apply k R K c).symm
  have hcomm : (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ u) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [Category.assoc, hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq X.hom :=
    { R := R
      K := K
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ u
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k R))
      commSq := ⟨hcomm⟩ }
  have : Subsingleton S.commSq.LiftStruct := huniq S
  have h1 : (⟨u, rfl, hu⟩ : S.commSq.LiftStruct) = ⟨v, h.symm, hv⟩ :=
    Subsingleton.elim _ _
  exact congrArg CommSq.LiftStruct.l h1

end Work.KeyLemma.Curve
