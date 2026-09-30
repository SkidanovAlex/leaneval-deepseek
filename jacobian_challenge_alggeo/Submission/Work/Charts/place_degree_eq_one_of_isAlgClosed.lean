import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Places of a curve over an algebraically closed field have degree one

Let `C` be a smooth, proper, geometrically irreducible curve over an algebraically
closed field `k`, and let `P` be a place of `C`, i.e. a closed point.  Then the
residue field `κ(P)` is a finite extension of `k`, and since `k` is algebraically
closed this forces `κ(P) = k`; equivalently the degree `[κ(P) : k]` of `P` is `1`.

The mathematical content is the Nullstellensatz: the residue field of a closed point
of a scheme locally of finite type over a field `k` is finite over `k` (this is the
argument of `Work.CurveBasics.Place.residueDegree_pos`).  Concretely, the structure
morphism `Spec κ(P) ⟶ Spec k` is finite, so the corresponding ring map
`k ⟶ κ(P)` is finite, hence `κ(P)` is an integral — a fortiori algebraic — extension
of `k`, and an algebraic extension of an algebraically closed field is trivial.

We prove this by identifying the ring map induced by `Spec κ(P) ⟶ Spec k` with the
`k`-algebra structure carried by the residue field, and then invoking
`IsAlgClosed.algebraMap_bijective_of_isIntegral`.
-/
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

universe u

/-- The ring homomorphism `R ⟶ κ(x)` induced by the structure morphism
`Spec κ(x) ⟶ Spec R` is the composite `R ≅ Γ(Spec R) ⟶ κ(x)`. -/
private lemma Spec_preimage_fromSpecResidueField (R : CommRingCat) (x : Spec R) :
    Spec.preimage ((Spec R).fromSpecResidueField x) =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x]
  rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map]
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv]
  rfl

/-- The ring homomorphism `k ⟶ κ(x)` corresponding to the composite
`Spec κ(x) ⟶ X ⟶ Spec k` is the composite of the structure map `k ⟶ κ(f x)` of
`Spec k` at `f x` with the residue field map `κ(f x) ⟶ κ(x)`.  This is exactly the
`k`-algebra structure put on `κ(x)` by
`Work.CurveBasics.Curve.Place.instAlgebraResidueField`. -/
private lemma Spec_preimage_fromSpecResidueField_comp {k : Type u} [Field k] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec (CommRingCat.of k)).Γevaluation (f x) ≫ f.residueFieldMap x := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x]
  rw [Spec.preimage_comp, Spec.preimage_map, Spec_preimage_fromSpecResidueField]
  simp only [Category.assoc]

theorem place_degree_eq_one_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (P : C.Place) : P.degree = 1 := by
  -- Reduce to the dimension of the residue field over `k`.
  rw [Work.CurveBasics.Place.degree_eq_finrank]
  -- `Spec κ(P) ⟶ Spec k` is finite: `Spec κ(P) ⟶ C` is locally of finite type because
  -- `P` is closed, `C ⟶ Spec k` is locally of finite type, and a morphism from the
  -- spectrum of a field to a Jacobson scheme which is locally of finite type is finite.
  have hfin_scheme : IsFinite (C.left.fromSpecResidueField P.point ≫ C.hom) := by
    have hloc : LocallyOfFiniteType (C.left.fromSpecResidueField P.point) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp P.isClosed
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    exact inferInstance
  -- Hence the corresponding ring homomorphism `k ⟶ κ(P)` is finite.
  have hpre_fin : (Spec.preimage (C.left.fromSpecResidueField P.point ≫ C.hom)).hom.Finite := by
    rw [← IsFinite.SpecMap_iff, Spec.map_preimage]
    exact hfin_scheme
  -- It agrees with the `k`-algebra structure on `κ(P)`.
  have hpre_eq : (Spec.preimage (C.left.fromSpecResidueField P.point ≫ C.hom)).hom
      = (algebraMap k (C.left.residueField P.point)) := by
    rw [Spec_preimage_fromSpecResidueField_comp C.hom P.point]
    rfl
  -- So `κ(P)` is finite, hence integral, over `k`.
  have hAlgFin : (algebraMap k (C.left.residueField P.point)).Finite := hpre_eq ▸ hpre_fin
  haveI : Module.Finite k (C.left.residueField P.point) := RingHom.finite_algebraMap.mp hAlgFin
  haveI : Algebra.IsIntegral k (C.left.residueField P.point) := Algebra.IsIntegral.of_finite k _
  -- An integral extension of an algebraically closed field is trivial.
  have hbij : Function.Bijective (algebraMap k (C.left.residueField P.point)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  -- A field with a bijective structure map has dimension one over its base.
  have hfr := LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective (Algebra.linearMap k (C.left.residueField P.point)) hbij)
  rw [Module.finrank_self k] at hfr
  exact hfr.symm

end Work.Charts
