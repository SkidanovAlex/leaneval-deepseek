import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SpecLin.Chart

open scoped TensorProduct

/-- For a `K`-algebra `A` and a domain `R` over the field `K`, the ring `A ⊗_K R` is a domain as
soon as `A ⊗_K Frac R` is: the natural map `A ⊗_K R → A ⊗_K Frac R` is injective, because
`R ↪ Frac R` is injective and `A` is a `K`-vector space, hence flat over the field `K`.

This is the first ingredient of the affine-chart analysis in
`Work.SpecLin.Core.linEquiv_of_sections`: for `A = Γ(C ∖ Q)` the ring `B = A ⊗_K R` must be a
domain in order to localise it at the prime `P = m·B`. -/
theorem isDomain_tensorProduct_fractionRing {K : Type u} [Field K] {A R : Type u} [CommRing A]
    [Algebra K A] [CommRing R] [IsDomain R] [Algebra K R]
    (h : IsDomain (A ⊗[K] FractionRing R)) : IsDomain (A ⊗[K] R) := by
  -- The `K`-algebra map `R → Frac R` is injective since `R` is a domain.
  let f : R →ₐ[K] FractionRing R := IsScalarTower.toAlgHom K R (FractionRing R)
  have hf' : Function.Injective f.toLinearMap := by
    rw [AlgHom.coe_toLinearMap]
    exact IsFractionRing.injective R (FractionRing R)
  -- The induced `K`-algebra map `A ⊗_K R → A ⊗_K Frac R`.
  let F : A ⊗[K] R →ₐ[K] A ⊗[K] FractionRing R :=
    Algebra.TensorProduct.map (AlgHom.id K A) f
  -- It agrees with `LinearMap.lTensor A f`, which is injective because `A` is flat over `K`.
  have hFeq : F.toLinearMap = LinearMap.lTensor A f.toLinearMap := by
    apply TensorProduct.ext'
    intro a r
    simp only [AlgHom.toLinearMap_apply, LinearMap.lTensor_tmul, F,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hF : Function.Injective F := by
    have hlin : Function.Injective (LinearMap.lTensor A f.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := A) (N := R)
        (P := FractionRing R) f.toLinearMap hf'
    intro x y hxy
    have hxy' : F.toLinearMap x = F.toLinearMap y := by simpa using hxy
    have h2 : LinearMap.lTensor A f.toLinearMap x = LinearMap.lTensor A f.toLinearMap y := by
      rw [← hFeq]
      exact hxy'
    exact hlin h2
  -- A subring of the domain `A ⊗_K Frac R` is a domain.
  exact Function.Injective.isDomain (α := A ⊗[K] FractionRing R) F hF

end Work.SpecLin.Chart
