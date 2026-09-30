import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SpecLin.Setup

open scoped TensorProduct

/-- If an element `y` of `A ⊗[K] R` becomes a pure tensor `1 ⊗ f` with `f ∈ Frac R` after extending
scalars along `R → Frac R`, then it is already of the form `1 ⊗ r` with `r ∈ R`.

The argument uses a `K`-linear retraction `π : A →ₗ[K] K` of the unit `1 : A` (which exists because
`A` is a free, hence projective, `K`-module as `K` is a field). Evaluating the base-changed element
along `π` produces an element `r = (π ⊗ id)(y) ∈ R` with `ρ r = f`; injectivity of the base-change
map `A ⊗[K] R → A ⊗[K] Frac R` (a consequence of flatness of `A` over the field `K`) then forces
`y = 1 ⊗ r`. -/
theorem tensorProductInf {K A R : Type u} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    [CommRing R] [IsDomain R] [Algebra K R] (y : TensorProduct K A R) (f : FractionRing R)
    (h : Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R)) y
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) f) :
    ∃ r : R, y = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r := by
  classical
  -- The structure map `R → Frac R` and the induced base change `A ⊗[K] R → A ⊗[K] Frac R`.
  let ρ : R →ₐ[K] FractionRing R := IsScalarTower.toAlgHom K R (FractionRing R)
  let ψ : A ⊗[K] R →ₐ[K] A ⊗[K] FractionRing R := Algebra.TensorProduct.map (AlgHom.id K A) ρ
  -- A `K`-linear retraction of the unit `1 : A` (exists as `A` is a free `K`-module).
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (x := (1 : A)) one_ne_zero
  -- The retractions `A ⊗[K] R → R` and `A ⊗[K] Frac R → Frac R` obtained from `π`.
  let evR : A ⊗[K] R →ₗ[K] R := TensorProduct.lift ((LinearMap.lsmul K R).comp π)
  let evT : A ⊗[K] FractionRing R →ₗ[K] FractionRing R :=
    TensorProduct.lift ((LinearMap.lsmul K (FractionRing R)).comp π)
  -- The two evaluations are compatible with base change.
  have key : ∀ z : A ⊗[K] R, evT (ψ z) = ρ (evR z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [evT, evR]
    | tmul a r =>
        simp only [evT, evR, ψ, ρ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        simp only [LinearMap.comp_apply, LinearMap.lsmul_apply, map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- The evaluation of the pure tensor `1 ⊗ f` is `f`.
  have hf : evT (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) f) = f := by
    simp only [evT, Algebra.TensorProduct.includeRight_apply]
    rw [TensorProduct.lift.tmul]
    simp only [LinearMap.comp_apply, hπ, LinearMap.lsmul_apply, one_smul]
  -- The base change map is injective (`A` is flat over the field `K`).
  have hinj : Function.Injective ψ := by
    have hρinj : Function.Injective ρ.toLinearMap := by
      rw [AlgHom.coe_toLinearMap]
      exact IsFractionRing.injective R (FractionRing R)
    have hflat : Function.Injective (LinearMap.lTensor A ρ.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := A) (N := R)
        (P := FractionRing R) ρ.toLinearMap hρinj
    have hψeq : ψ.toLinearMap = LinearMap.lTensor A ρ.toLinearMap := by
      apply TensorProduct.ext'
      intro a r
      simp only [AlgHom.toLinearMap_apply, LinearMap.lTensor_tmul, ψ,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    intro x y hxy
    have hxy' : ψ.toLinearMap x = ψ.toLinearMap y := hxy
    have h2 : LinearMap.lTensor A ρ.toLinearMap x = LinearMap.lTensor A ρ.toLinearMap y := by
      rw [← hψeq]; exact hxy'
    exact hflat h2
  -- The base change matches the two `includeRight`s.
  have hψinc : ∀ r : R, ψ (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r)
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) (ρ r) := by
    intro r
    simp only [ψ, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
  -- The key numerical identity `ρ (evR y) = f`.
  have hρr0 : ρ (evR y) = f := by
    rw [← key y]
    rw [show ψ y = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) f
        from h]
    exact hf
  refine ⟨evR y, ?_⟩
  refine (hinj ?_).symm
  rw [hψinc (evR y), hρr0]
  exact h.symm

end Work.SpecLin.Setup
