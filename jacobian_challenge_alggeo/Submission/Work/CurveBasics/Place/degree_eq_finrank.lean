/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The degree of a place is the dimension of its residue field

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let `Q` be a
place of `C`.  The *degree* of `Q` is by definition the residue degree of the structure
morphism `C.left ⟶ Spec k` at `Q`, i.e. the dimension of the residue field `κ(Q)` over the
residue field of `Speck k` at the image point.

This file shows that this agrees with the more usual formula `[κ(Q) : k]`, i.e. that the
residue degree equals `Module.finrank k (C.left.residueField Q.point)` for the canonical
`k`-algebra structure on `κ(Q)`.

The mathematical content is that the canonical ring homomorphism
`k ⟶ κ(Spec k)` (the map on residue fields induced by `k ≅ Γ(Spec k, ⊤)`) is an isomorphism;
indeed `Spec k` is the spectrum of a field, so its residue field at its unique point is
`k` again.  Concretely we identify this map with `Spec.preimage (Spec.fromSpecResidueField x)`
for `x : Spec k` and use that for a field the canonical map `k ⟶ κ(x)` is bijective (it is
injective because `k` is a field, and we descend surjectivity from
`Spec.residueFieldIso` and `Ideal.algEquivResidueFieldOfField`).

Finally, dimensions of a module are unchanged when the base field is replaced by an
isomorphic field acting through a compatible scalar action; this is the content of the
auxiliary lemma `Work.CurveBasics.Place.finrank_eq_of_ringHom`.
-/
import Mathlib
import Submission.Work.CurveBasics.Place.Coheight

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.Place

/-- If `e : K →+* κ` is a bijective ring homomorphism of fields and the `K`-action on `M`
factors through `e` (i.e. `a • m = e a • m` for all `a : K`, `m : M`), then `M` has the
same dimension over `K` and over `κ`. -/
private lemma finrank_eq_of_ringHom {K κ M : Type*} [Field K] [Field κ] [AddCommGroup M]
    [Module κ M] [Module K M] (e : K →+* κ) (he : Function.Bijective e)
    (h : ∀ (a : K) (m : M), a • m = e a • m) :
    Module.finrank K M = Module.finrank κ M := by
  -- View `κ` as a `K`-algebra via `e`; then `M` is a `K`-`κ`-bimodule and the tower formula
  -- applies.  Since `e` is bijective, `κ` is one-dimensional over `K`.
  letI : Algebra K κ := e.toAlgebra
  haveI : IsScalarTower K κ M := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]
    exact (h x (y • z)).symm⟩
  have h1 : Module.finrank K κ = 1 := by
    have hbij : Function.Bijective (Algebra.linearMap K κ) := by
      have : ⇑(Algebra.linearMap K κ) = ⇑e := by
        ext a
        rw [Algebra.linearMap_apply]
        rfl
      rw [this]
      exact he
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap K κ) hbij)).symm.trans
      (Module.finrank_self K)
  have := Module.finrank_mul_finrank K κ M
  rw [h1, one_mul] at this
  exact this.symm

open Work.CurveBasics in
theorem degree_eq_finrank {k : Type*} [Field k] {C : Curve k} (Q : C.Place) :
    Q.degree = Module.finrank k (C.left.residueField Q.point) := by
  show C.hom.residueDegree Q.point = Module.finrank k (C.left.residueField Q.point)
  rw [AlgebraicGeometry.Scheme.Hom.residueDegree]
  -- Unfold the local algebra structure carried by the definition of `residueDegree` into a
  -- proper local instance, so that `Module.finrank` can be elaborated against it.
  letI : Algebra ((Spec (CommRingCat.of k)).residueField (C.hom Q.point))
      (C.left.residueField Q.point) :=
    (C.hom.residueFieldMap Q.point).hom.toAlgebra
  change Module.finrank ((Spec (CommRingCat.of k)).residueField (C.hom Q.point))
      (C.left.residueField Q.point) =
    Module.finrank k (C.left.residueField Q.point)
  -- It remains to compare the two base fields: `k` and `κ(Spec k, C.hom Q.point)`, which are
  -- identified by the canonical (bijective) map `k ⟶ κ(Spec k)`.
  refine (finrank_eq_of_ringHom (K := k)
    (κ := (Spec (CommRingCat.of k)).residueField (C.hom Q.point))
    (M := C.left.residueField Q.point) ?_ ?_ ?_).symm
  · exact ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Spec (CommRingCat.of k)).Γevaluation (C.hom Q.point)).hom
  · -- The canonical map `k ⟶ κ(Spec k, C.hom Q.point)` is bijective.
    have hpi : (show PrimeSpectrum k from (C.hom Q.point)).asIdeal.IsPrime :=
      (show PrimeSpectrum k from (C.hom Q.point)).isPrime
    -- Rewrite it as the composite `k ⟶ x.asIdeal.ResidueField ⟶ κ(Spec k, x)` and conclude
    -- that both factors are bijective.
    have hh := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of k) (C.hom Q.point)
    simp only [Scheme.Γevaluation, Scheme.evaluation]
    rw [← hh]
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact (Scheme.Spec.residueFieldIso (CommRingCat.of k) (C.hom Q.point)).symm.commRingCatIsoToRingEquiv.bijective.comp
      (Ideal.algEquivResidueFieldOfField (C.hom Q.point).asIdeal).bijective
  · intro a m
    show a • m = _
    simp only [Algebra.smul_def]
    rfl

end Work.CurveBasics.Place
