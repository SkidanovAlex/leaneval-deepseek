/-
# The unit step of the affine-chart core of specialisation of linear equivalence

Let `K` be a field, `A` a nontrivial `K`-algebra, `R` a valuation ring which is a `K`-algebra,
`B = A ⊗[K] R` *the* relative chart, and `P = 𝔪_R · B` the prime ideal defining the generic point
of the special fibre.  We prove

> if `x ∈ B ∖ P` and `x · b = ι s` for some `b ∈ B` and some `0 ≠ s ∈ R`
> (where `ι : R → B` is `Algebra.TensorProduct.includeRight`), then `x` is a unit of `B`.

This is the *unconditional* form of the content-normalisation lemma
`Work.SpecLin.Setup.isUnit_of_mul_eq_of_notMem_maximalIdeal_map` (`Setup/keyUnit.lean`), which
assumes in addition that the numerator `b` is itself primitive modulo `P`.  Here we remove that
hypothesis: content-normalise `b = c • b₁` with `b₁ ∉ P`
(`Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map`, using that `B` is free over `R`,
`Work.SpecLin.Core.module_free_chartTensor`), so that `x·b₁ = s/c` holds in the generic fibre
`A ⊗[K] Frac R`; the direct-summand fact `B ∩ Frac R = R`
(`exists_includeRight_of_map_eq_fractionRing` below, the same statement as
`Work.SpecLin.Setup.tensorProductInf`) shows `s/c ∈ R∖{0}`, and then `keyUnit` applies to the
*primitive* pair `(b₁, s/c)`.

Only the two structural inputs `B` free over `R` and `B ⧸ P` a domain are used; no Noetherianity,
no dimension theory.
-/
import Mathlib
import Submission.Work.SpecLin.Setup.keyUnit
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Core.module_free_chartTensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.SpecLin.Setup

universe u

/-- **The direct summand fact `B ∩ Frac R = R`.**

If `y ∈ B = A ⊗[K] R` becomes a *constant* `1 ⊗ f` (i.e. the image of the scalar `f ∈ Frac R`)
in the generic fibre `A ⊗[K] Frac R`, then `y` itself is `1 ⊗ r` for some `r ∈ R`.

The proof uses a `K`-linear retraction `π : A → K` of `1 : A` (which exists since `A` is a free,
hence projective, `K`-module): the base change `π ⊗ id` is a retraction of `A ⊗[K] R → A ⊗[K] F`
compatible with `R → Frac R`, so it produces `r = (π ⊗ id)(y) ∈ R` with `ρ r = f`; injectivity of
the base change map (flatness of `A` over the field `K`) then gives `y = 1 ⊗ r`. -/
private lemma exists_includeRight_of_map_eq_fractionRing {K A R : Type u} [Field K] [CommRing A]
    [Algebra K A] [Nontrivial A] [CommRing R] [IsDomain R] [Algebra K R]
    (y : TensorProduct K A R) (f : FractionRing R)
    (h : Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R)) y
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) f) :
    ∃ r : R, y = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r := by
  classical
  -- a `K`-linear retraction of `1 : A`
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (V := A) (x := (1 : A)) one_ne_zero
  -- the evaluations `A ⊗[K] R → R` and `A ⊗[K] Frac R → Frac R`
  let Φ : A ⊗[K] R →ₗ[K] R :=
    (TensorProduct.lid K R).toLinearMap.comp (TensorProduct.map π (LinearMap.id : R →ₗ[K] R))
  let ΦF : A ⊗[K] FractionRing R →ₗ[K] FractionRing R :=
    (TensorProduct.lid K (FractionRing R)).toLinearMap.comp
      (TensorProduct.map π (LinearMap.id : FractionRing R →ₗ[K] FractionRing R))
  have hΦFι : ∀ r : FractionRing R,
      ΦF (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R) r) = r := by
    intro r
    simp [ΦF, Algebra.TensorProduct.includeRight_apply, TensorProduct.map_tmul,
      TensorProduct.lid_tmul, hπ]
  -- the two evaluations are compatible with the base change `R → Frac R`
  have hcompat : ∀ z : A ⊗[K] R,
      ΦF (Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R)) z)
        = (IsScalarTower.toAlgHom K R (FractionRing R)) (Φ z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a r =>
        simp [Φ, ΦF, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
          TensorProduct.lid_tmul, IsScalarTower.coe_toAlgHom']
    | add x y hx hy => simp [map_add, hx, hy]
  -- the base change map is injective (`A` is flat over the field `K`)
  have hψtm : (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K R (FractionRing R))).toLinearMap
      = LinearMap.lTensor A (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap := by
    refine TensorProduct.ext' ?_
    intro a r
    simp [LinearMap.lTensor_tmul]
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R))) := by
    have : Module.Free K A := Module.Free.of_divisionRing K A
    have : Module.Flat K A := Module.Flat.of_free
    have hρinj : Function.Injective (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap := by
      simpa [AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom'] using
        IsFractionRing.injective R (FractionRing R)
    have h1 : Function.Injective
        (LinearMap.lTensor A (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hρinj
    intro a b hab
    refine h1 ?_
    rw [← hψtm]
    exact hab
  have hψι : ∀ r : R, (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K R (FractionRing R)))
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) r)
      = Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing R)
          ((IsScalarTower.toAlgHom K R (FractionRing R)) r) := by
    intro r
    simp [Algebra.TensorProduct.includeRight_apply]
  have key : (IsScalarTower.toAlgHom K R (FractionRing R)) (Φ y) = f := by
    have h1 := hcompat y
    rw [h, hΦFι f] at h1
    exact h1.symm
  refine ⟨Φ y, hinj ?_⟩
  rw [h, hψι (Φ y), key]

theorem unitOfGenericUnit {K A R : Type u} [Field K] [CommRing A]
    [Algebra K A] [Nontrivial A] [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    (hdom : IsDomain (TensorProduct K A R ⧸
      (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (x : TensorProduct K A R)
    (hx : x ∉ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
    (hinv : ∃ (b : TensorProduct K A R) (s : R), s ≠ 0 ∧
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) s = x * b) :
    IsUnit x := by
  classical
  obtain ⟨b, s, hs, hxb⟩ := hinv
  -- the `R`-algebra structure on `B = A ⊗[K] R` (second factor), so that `B` is free over `R`
  letI : Algebra R (TensorProduct K A R) :=
    Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
  haveI hfree : Module.Free R (TensorProduct K A R) :=
    Work.SpecLin.Core.module_free_chartTensor (K := K) (A := A) (R := R)
  -- content normalisation of the numerator `b`
  obtain ⟨c, b₁, hbc, hb₁⟩ := Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map (R := R) b
  let ιR : R →ₐ[K] TensorProduct K A R :=
    Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)
  have hι : algebraMap R (TensorProduct K A R) = ιR :=
    Algebra.TensorProduct.algebraMap_eq_includeRight
  rw [hι] at hb₁
  -- `includeRight` is injective on `R → A ⊗[K] R`
  have hιinj : Function.Injective ιR := by
    have : Module.Free K R := Module.Free.of_divisionRing K R
    have : Module.Flat K R := Module.Flat.of_free
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := R)
      (RingHom.injective (algebraMap K A))
  have hbne : b ≠ 0 := by
    intro hb0
    refine hs (hιinj ?_)
    rw [hxb, hb0, mul_zero, map_zero]
  have hcne : c ≠ 0 := by
    intro hc0
    exact hbne (by rw [hbc, hc0, zero_smul])
  -- the generic fibre
  let F := FractionRing R
  let ρ : R →ₐ[K] F := IsScalarTower.toAlgHom K R F
  let ψ : TensorProduct K A R →ₐ[K] TensorProduct K A F :=
    Algebra.TensorProduct.map (AlgHom.id K A) ρ
  let ιF : F →ₐ[K] TensorProduct K A F :=
    Algebra.TensorProduct.includeRight (R := K) (A := A) (B := F)
  have hbc' : b = ιR c * b₁ := by
    rw [hbc, Algebra.smul_def, hι]
    rfl
  have hψι : ∀ r : R, ψ (ιR r) = ιF (ρ r) := by
    intro r
    simp [ψ, ιR, ιF, ρ, Algebra.TensorProduct.map_tmul]
  have hρc : ρ c ≠ 0 := fun h0 =>
    hcne (IsFractionRing.injective R F (by simpa [ρ, IsScalarTower.coe_toAlgHom'] using h0))
  have hρs : ρ s ≠ 0 := fun h0 =>
    hs (IsFractionRing.injective R F (by simpa [ρ, IsScalarTower.coe_toAlgHom'] using h0))
  -- the equation `x·b₁ = s/c` in the generic fibre
  have h2 : ιF (ρ s) = ιF (ρ c) * ψ (x * b₁) := by
    have h1 : ψ (ιR s) = ψ (x * b) := by rw [hxb]
    have h3 : ψ (x * b) = ψ x * (ιF (ρ c) * ψ b₁) := by
      rw [hbc', map_mul, map_mul, hψι c]
    rw [hψι s] at h1
    rw [h3] at h1
    rw [h1, map_mul]
    ring
  have hinvF : ιF ((ρ c)⁻¹) * ιF (ρ c) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hρc, map_one]
  have hEq : ψ (x * b₁) = ιF ((ρ c)⁻¹ * ρ s) := by
    calc ψ (x * b₁) = ιF ((ρ c)⁻¹) * (ιF (ρ c) * ψ (x * b₁)) := by
          rw [← mul_assoc, hinvF, one_mul]
      _ = ιF ((ρ c)⁻¹) * ιF (ρ s) := by rw [← h2]
      _ = ιF ((ρ c)⁻¹ * ρ s) := by rw [map_mul]
  -- the direct-summand fact: `x·b₁` is already the image of an element of `R`
  obtain ⟨r, hr⟩ := exists_includeRight_of_map_eq_fractionRing (x * b₁) ((ρ c)⁻¹ * ρ s) hEq
  have hιFinj : Function.Injective ιF := by
    have : Module.Free K F := Module.Free.of_divisionRing K F
    have : Module.Flat K F := Module.Flat.of_free
    exact Algebra.TensorProduct.includeRight_injective (R := K) (A := A) (B := F)
      (RingHom.injective (algebraMap K A))
  have hrne : r ≠ 0 := by
    intro hr0
    have hzero : ιF ((ρ c)⁻¹ * ρ s) = 0 := by
      rw [← hEq, hr, hr0]
      simp
    exact (mul_ne_zero (inv_ne_zero hρc) hρs) (hιFinj (hzero.trans (map_zero ιF).symm))
  -- apply the content-normalised unit lemma to the primitive numerator `b₁`
  exact isUnit_of_mul_eq_of_notMem_maximalIdeal_map hdom x hx ⟨b₁, r, hb₁, hrne, hr.symm⟩

end Work.SpecLin.Setup
