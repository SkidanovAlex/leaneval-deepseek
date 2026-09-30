import Mathlib
import Submission.Work.Normality.isIntegrallyClosed_invariants
import Submission.Work.Normality.isIntegrallyClosed_of_smooth_algebra
import Submission.Work.SymQuot.RelQuot.tensorIncl_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.JacClose

noncomputable section

universe u

/-- A tensor product of two smooth algebras over a field is smooth: the map `K ⟶ A ⊗[K] B` is the
composite of `K ⟶ A` (smooth by hypothesis) and `A ⟶ A ⊗[K] B` (the base change of `K ⟶ B`,
smooth by the stability of smoothness under base change). -/
theorem smooth_tensorProduct_algebra {K A B : Type u} [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Algebra.Smooth K A] [Algebra.Smooth K B] :
    Algebra.Smooth K (TensorProduct K A B) := by
  have h1 : (algebraMap K A).Smooth :=
    RingHom.smooth_algebraMap.mpr (inferInstance : Algebra.Smooth K A)
  have h2 : (algebraMap A (TensorProduct K A B)).Smooth :=
    RingHom.smooth_algebraMap.mpr (Algebra.Smooth.baseChange K B A)
  have h3 : ((algebraMap A (TensorProduct K A B)).comp (algebraMap K A)).Smooth :=
    RingHom.Smooth.comp h1 h2
  rw [← IsScalarTower.algebraMap_eq K A (TensorProduct K A B)] at h3
  exact RingHom.smooth_algebraMap.mp h3

/-- **Base change of invariants as a ring equivalence.**  For a finite group `G` acting on a
`K`-algebra `A` by `K`-algebra automorphisms and any `K`-algebra `B`, the canonical map
`A^G ⊗[K] B ⟶ (A ⊗[K] B)^G` (acting on the first factor) is a ring equivalence.  Injectivity is
`Work.SymQuot.RelQuot.tensorIncl_range`, surjectivity is that its range is the fixed points
(`Work.SymQuot.Invariants.tensor_fixedPoints_of_flat`). -/
noncomputable def fixedPoints_tensorProduct_equiv {K : Type u} [Field K] {A B : Type u}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {G : Type u} [Group G] [Fintype G]
    [MulSemiringAction G A] [SMulCommClass G K A] :
    TensorProduct K ↥(FixedPoints.subalgebra K A G) B ≃+*
      ↥(FixedPoints.subring (TensorProduct K A B) G) := by
  classical
  obtain ⟨hinj, hrange⟩ :=
    Work.SymQuot.RelQuot.tensorIncl_range (K := K) (Γ := G) A B
  let φ : TensorProduct K ↥(FixedPoints.subalgebra K A G) B →+*
      ↥(FixedPoints.subring (TensorProduct K A B) G) :=
    { toFun := fun x => ⟨Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x, by
        have hx : (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x) ∈
            {y : TensorProduct K A B | ∀ g : G,
              Work.SymQuot.RelQuot.tensorAct (K := K) (Γ := G) A B g y = y} := by
          rw [← hrange]
          exact ⟨x, rfl⟩
        exact hx⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hφval : ∀ x : TensorProduct K ↥(FixedPoints.subalgebra K A G) B,
      ((φ x : TensorProduct K A B)) =
        Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x :=
    fun x => rfl
  have hbij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      refine hinj ?_
      rw [← hφval x, ← hφval y]
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : TensorProduct K A B) ∈ Set.range
          (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B) := by
        rw [hrange]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact RingEquiv.ofBijective φ hbij

/-- **The tensor product of two invariant rings of smooth algebras over a field is a domain and
integrally closed.**  `A` and `B` are domains and smooth `K`-algebras (for a field `K`), the tensor
product `A ⊗[K] B` is assumed to be a domain, and `G`, `H` are finite groups acting on `A`, `B`
(compatibly with the `K`-structure).  Then `A^G ⊗[K] B^H` is a domain and integrally closed.

Suggested route: `A ⊗[K] B` is a smooth `K`-algebra (tensor product of smooth algebras) and a
domain, hence integrally closed (`Work.Normality.isIntegrallyClosed_of_smooth_algebra`); its
invariants under the finite group `G × H` are integrally closed
(`Work.Normality.isIntegrallyClosed_invariants`); identify `A^G ⊗[K] B^H` with `(A ⊗[K] B)^{G × H}`
by applying `Work.SymQuot.Invariants.tensor_fixedPoints_of_flat` (or
`Work.SymQuot.RelQuot.tensorIncl_range`) twice, once for `G` and once for `H`, and transfer along
the resulting ring isomorphism (`IsIntegrallyClosed.of_equiv`).  Domain: `A^G ⊗[K] B^H → A ⊗[K] B`
is injective (tensor product of injective maps of free modules over a field) with a domain target. -/
theorem tensor_fixedPoints_normal {K : Type u} [Field K]
    {A : Type u} [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A]
    {B : Type u} [CommRing B] [IsDomain B] [Algebra K B] [Algebra.Smooth K B]
    [IsDomain (TensorProduct K A B)]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    {H : Type u} [Group H] [Fintype H] [MulSemiringAction H B] [SMulCommClass H K B] :
    IsDomain (TensorProduct K ↥(FixedPoints.subalgebra K A G) ↥(FixedPoints.subalgebra K B H)) ∧
    IsIntegrallyClosed
      (TensorProduct K ↥(FixedPoints.subalgebra K A G) ↥(FixedPoints.subalgebra K B H)) := by
  -- `A ⊗[K] B` is a smooth `K`-algebra, hence (being a domain) integrally closed.
  haveI hsm : Algebra.Smooth K (TensorProduct K A B) := smooth_tensorProduct_algebra
  haveI hABic : IsIntegrallyClosed (TensorProduct K A B) :=
    Work.Normality.isIntegrallyClosed_of_smooth_algebra (K := K) (A := TensorProduct K A B)
  -- `(A ⊗[K] B)^G` is integrally closed, and a domain (a subring of the domain `A ⊗[K] B`).
  haveI h1ic : IsIntegrallyClosed ↥(FixedPoints.subring (TensorProduct K A B) G) :=
    Work.Normality.isIntegrallyClosed_invariants G
  -- hence `A^G ⊗[K] B` is integrally closed and a domain.
  haveI h2ic : IsIntegrallyClosed (TensorProduct K ↥(FixedPoints.subalgebra K A G) B) :=
    IsIntegrallyClosed.of_equiv
      (fixedPoints_tensorProduct_equiv (K := K) (A := A) (B := B) (G := G)).symm
  haveI h2dom : IsDomain (TensorProduct K ↥(FixedPoints.subalgebra K A G) B) :=
    Function.Injective.isDomain
      (fixedPoints_tensorProduct_equiv (K := K) (A := A) (B := B) (G := G)).toRingHom
      (fixedPoints_tensorProduct_equiv (K := K) (A := A) (B := B) (G := G)).injective
  -- and so is `B ⊗[K] A^G`, by commutativity of the tensor product.
  haveI h3dom : IsDomain (TensorProduct K B ↥(FixedPoints.subalgebra K A G)) :=
    Function.Injective.isDomain
      ((Algebra.TensorProduct.comm K B ↥(FixedPoints.subalgebra K A G)).toRingEquiv).toRingHom
      ((Algebra.TensorProduct.comm K B ↥(FixedPoints.subalgebra K A G)).toRingEquiv).injective
  haveI h3ic : IsIntegrallyClosed (TensorProduct K B ↥(FixedPoints.subalgebra K A G)) :=
    IsIntegrallyClosed.of_equiv
      ((Algebra.TensorProduct.comm K B ↥(FixedPoints.subalgebra K A G)).toRingEquiv).symm
  -- `(B ⊗[K] A^G)^H` is integrally closed and a domain.
  haveI h4ic : IsIntegrallyClosed
      ↥(FixedPoints.subring (TensorProduct K B ↥(FixedPoints.subalgebra K A G)) H) :=
    Work.Normality.isIntegrallyClosed_invariants H
  -- hence `B^H ⊗[K] A^G ≅ (B ⊗[K] A^G)^H` is integrally closed and a domain.
  haveI h5ic : IsIntegrallyClosed
      (TensorProduct K ↥(FixedPoints.subalgebra K B H) ↥(FixedPoints.subalgebra K A G)) :=
    IsIntegrallyClosed.of_equiv
      (fixedPoints_tensorProduct_equiv (K := K) (A := B)
        (B := ↥(FixedPoints.subalgebra K A G)) (G := H)).symm
  haveI h5dom : IsDomain
      (TensorProduct K ↥(FixedPoints.subalgebra K B H) ↥(FixedPoints.subalgebra K A G)) :=
    Function.Injective.isDomain
      (fixedPoints_tensorProduct_equiv (K := K) (A := B)
        (B := ↥(FixedPoints.subalgebra K A G)) (G := H)).toRingHom
      (fixedPoints_tensorProduct_equiv (K := K) (A := B)
        (B := ↥(FixedPoints.subalgebra K A G)) (G := H)).injective
  -- finally `A^G ⊗[K] B^H ≅ B^H ⊗[K] A^G`.
  haveI hFindom : IsDomain
      (TensorProduct K ↥(FixedPoints.subalgebra K A G) ↥(FixedPoints.subalgebra K B H)) :=
    Function.Injective.isDomain
      (((Algebra.TensorProduct.comm K ↥(FixedPoints.subalgebra K B H)
        ↥(FixedPoints.subalgebra K A G)).toRingEquiv).symm).toRingHom
      (((Algebra.TensorProduct.comm K ↥(FixedPoints.subalgebra K B H)
        ↥(FixedPoints.subalgebra K A G)).toRingEquiv).symm).injective
  haveI hFiic : IsIntegrallyClosed
      (TensorProduct K ↥(FixedPoints.subalgebra K A G) ↥(FixedPoints.subalgebra K B H)) :=
    IsIntegrallyClosed.of_equiv
      ((Algebra.TensorProduct.comm K ↥(FixedPoints.subalgebra K B H)
        ↥(FixedPoints.subalgebra K A G)).toRingEquiv)
  exact ⟨hFindom, hFiic⟩

end

end Work.JacClose
