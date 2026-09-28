import Mathlib
import Submission.Work.StemsB.sphRatHomology

/-!
# Torsion integral `H₁` forces vanishing rational `H₁`

The change-of-coefficients theorem `H₁(X;ℚ) ≅ H₁(X;ℤ) ⊗[ℤ] ℚ` shows that the rational
homology of a space in degree `1` is the rationalisation of its integral homology in degree `1`.
Hence if every class of `H₁(X;ℤ)` has finite order — i.e. `H₁(X;ℤ)` is a torsion group — then
`H₁(X;ℚ) = 0`.

This is the exact converse of `Work.RatHurewicz.torsion_of_subsingleton_ratHomology`
(vanishing of rational homology implies torsion of integral homology), and it is the direction
used when a *geometric* torsion statement about integral homology is to be converted into a
rational vanishing statement.

## The mathematics

1. The singular chain complexes are related by the flat change of rings `ℤ → ℚ`:
   `C_*(X;ℚ) ≅ C_*(X;ℤ) ⊗[ℤ] ℚ` (`Work.StemsB.SphRat.chainComplexBaseChange`), and since
   `ℚ` is flat over `ℤ` this iso descends to homology
   (`Work.StemsB.SphRat.homologyMapBaseChange`), giving `H₁(X;ℚ) ≅ ℚ ⊗[ℤ] H₁(X;ℤ)`.
2. For a torsion `ℤ`-module `M`, the rationalisation `ℚ ⊗[ℤ] M` vanishes: if `N • m = 0` with
   `N > 0`, then in `ℚ ⊗[ℤ] M` the element `q ⊗ m` satisfies
   `N • (q ⊗ m) = q ⊗ (N • m) = 0` (additivity of the tensor product in the second variable:
   apply `map_nsmul` to the linear map `m ↦ q ⊗ m`), whence
   `q ⊗ m = ((N : ℚ)⁻¹ * N) • (q ⊗ m) = 0` because `ℚ ⊗[ℤ] M` is a `ℚ`-vector space.

The second step is carried out in `subsingleton_ratTensor_of_torsion` below, deliberately at the
level of the *additive* (natural-number) action and the `ℚ`-module structure of the tensor
product only: this avoids having to reconcile the two `ℤ`-module structures (`AddCommGroup`'s
canonical one and the bundled one of a `ModuleCat ℤ` object) that the tensor product of
`ModuleCat.extendScalars` is built with.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz

noncomputable section

/-- **The rationalisation of a torsion `ℤ`-module vanishes.**

If every element `m` of a `ℤ`-module `M` has a non-zero multiple `N • m = 0`, then
`M ⊗[ℤ] ℚ` (equivalently `ℚ ⊗[ℤ] M`, the underlying module of
`(ModuleCat.extendScalars (Int.castRingHom ℚ)).obj M`, which is the form in which the
base change of singular chains presents it) is a subsingleton.

For a pure tensor `q ⊗ m` with `N • m = 0`, the linear map `m' ↦ q ⊗ m'` sends `N • m = 0` to
`N • (q ⊗ m) = 0`; since `q ⊗ m = ((N : ℚ)⁻¹ * N) • (q ⊗ m)` and `ℚ ⊗[ℤ] M` is a `ℚ`-module,
this forces `q ⊗ m = 0`.  The pure tensors generate the tensor product additively. -/
theorem subsingleton_ratTensor_of_torsion (M : ModuleCat ℤ)
    (h : ∀ m : ↥M, ∃ N : ℕ, 0 < N ∧ N • m = 0) :
    Subsingleton ↥((ModuleCat.extendScalars (Int.castRingHom ℚ)).obj M) := by
  change Subsingleton (TensorProduct ℤ ℚ ↥M)
  refine ⟨fun x y => ?_⟩
  suffices ∀ z : TensorProduct ℤ ℚ ↥M, z = 0 by rw [this x, this y]
  intro z
  refine TensorProduct.induction_on (motive := fun z => z = 0) z rfl (fun q m => ?_)
    (fun x y hx hy => by rw [hx, hy, add_zero])
  obtain ⟨N, hNpos, hNm⟩ := h m
  -- the linear map `m' ↦ q ⊗ m'` sends `N • m = 0` to `N • (q ⊗ m) = 0`
  have hN : N • (q ⊗ₜ[ℤ] m) = 0 := by
    have h1 : (TensorProduct.mk ℤ ℚ ↥M q) (N • m) = 0 := by rw [hNm, map_zero]
    rwa [map_nsmul] at h1
  -- and `ℚ ⊗[ℤ] M` is a `ℚ`-module, so `N` can be divided out
  have hx : (N : ℚ) • (q ⊗ₜ[ℤ] m) = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℚ N]
    exact hN
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos)
  calc q ⊗ₜ[ℤ] m = ((N : ℚ)⁻¹ * N) • (q ⊗ₜ[ℤ] m) := by rw [inv_mul_cancel₀ hNq, one_smul]
    _ = (N : ℚ)⁻¹ • ((N : ℚ) • (q ⊗ₜ[ℤ] m)) := by rw [mul_smul]
    _ = 0 := by rw [hx, smul_zero]

/-- **Torsion integral homology in degree `1` forces vanishing rational homology in degree `1`.**

The rational singular chains of `X` are the integral ones with coefficients extended along
`ℤ → ℚ`; `ℚ` is flat over `ℤ`, so extension of scalars is exact and commutes with homology:

`H₁(X;ℚ) ≅ ℚ ⊗[ℤ] H₁(X;ℤ)`.

Under this isomorphism the rational homology is the rationalisation of the integral homology,
and the rationalisation of a torsion group is zero
(`Work.RatHurewicz.subsingleton_ratTensor_of_torsion`). -/
theorem isZero_ratH_one_of_torsion {X : Type} [TopologicalSpace X]
    (h : ∀ b : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology 1,
      ∃ N : ℕ, 0 < N ∧ N • b = 0) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology 1) := by
  -- `ℚ` is flat over `ℤ`, so extension of scalars is exact and preserves homology
  have hf : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : (ModuleCat.extendScalars (Int.castRingHom ℚ)).PreservesHomology := inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (Int.castRingHom ℚ)) := fun _ => inferInstance
  -- the comparison `C_*(X;ℤ) ⊗[ℤ] ℚ ≅ C_*(X;ℚ)` of chain complexes
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  let Y : TopCat := TopCat.of X
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ Y
  let L : ChainComplex (ModuleCat ℚ) ℕ := Work.Cohomology.singularChains ℚ Y
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Y)
        Work.StemsB.SphRat.extendScalarsIntRatIso
  -- which, `ℚ` being flat, identifies `H₁(X;ℚ)` with the rationalisation of `H₁(X;ℤ)`
  have hΨ : L.homology 1 ≅ F.obj (K.homology 1) :=
    (HomologicalComplex.homologyMapIso hΦ 1).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange F K 1).some
  -- the rationalisation of the torsion module `H₁(X;ℤ)` is trivial
  haveI : Subsingleton ↥(F.obj (K.homology 1)) := subsingleton_ratTensor_of_torsion _ h
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton (F.obj (K.homology 1))) hΨ

end

end Work.RatHurewicz
