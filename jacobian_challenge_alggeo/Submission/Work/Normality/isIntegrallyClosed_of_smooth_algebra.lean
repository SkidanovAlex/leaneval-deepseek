import Mathlib
import Submission.Work.Normality.isIntegrallyClosed_of_smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open scoped nonZeroDivisors TensorProduct
open CategoryTheory Limits AlgebraicGeometry

universe u v

namespace Work.Normality

noncomputable section

/-- **A domain which is standard smooth over a field is integrally closed**, in a
universe-polymorphic form: unlike `Work.Normality.isIntegrallyClosed_of_isStandardSmooth`, the
field and the algebra are allowed to live in *different* universes.

The proof is the one of `Work.Normality.isIntegrallyClosed_of_smooth`, which for convenience we
repeat here with the two universes kept apart: given a submersive presentation of `A` over `K`,
let `P₀` be the polynomial ring over `K` on the generators which do not occur among the relations.
Then `A` is étale over `P₀`, so `A ⊗[P₀] FractionRing P₀` is a field (and a domain) containing `A`,
and Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth` shows that `A` is integrally
closed in it. -/
theorem isIntegrallyClosed_of_isStandardSmooth_flex {K : Type u} {A : Type v} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.IsStandardSmooth K A] :
    IsIntegrallyClosed A := by
  obtain ⟨ι, σ, hσfin, _hιfin, ⟨Pr⟩⟩ := Algebra.IsStandardSmooth.out (R := K) (S := A)
  haveI : Finite σ := hσfin
  -- `P₀` is the polynomial ring on the generators which do not occur among the relations
  let P₀ := MvPolynomial ↥(Set.range Pr.map)ᶜ K
  let φ : P₀ →ₐ[K] A := MvPolynomial.aeval fun k => Pr.val k.1
  letI : Algebra P₀ A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K P₀ A :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have hgen : ∀ k : ↥(Set.range Pr.map)ᶜ,
      algebraMap P₀ A (MvPolynomial.X k) = Pr.val k.1 := fun k => by
    rw [RingHom.algebraMap_toAlgebra]
    exact MvPolynomial.aeval_X _ k
  -- the Kähler differentials of `A` over `P₀` are the base change of those of `P₀` over `K`
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange K P₀ A) :=
    bijective_mapBaseChange_complement (K := K) (A := A) Pr hgen
  haveI : Algebra.FormallySmooth K A := inferInstance
  haveI : Algebra.FormallySmooth P₀ A := formallySmooth_of_bijective_mapBaseChange hbij
  haveI : Algebra.FiniteType P₀ A :=
    Algebra.FiniteType.of_restrictScalars_finiteType K P₀ A
  haveI : Algebra.FinitePresentation P₀ A :=
    (Algebra.FinitePresentation.of_finiteType (R := P₀) (A := A)).mp ‹Algebra.FiniteType P₀ A›
  haveI : Algebra.Smooth P₀ A := ⟨‹Algebra.FormallySmooth P₀ A›, ‹Algebra.FinitePresentation P₀ A›⟩
  haveI : Module.Flat P₀ A := Algebra.Smooth.flat P₀ A
  -- `Ω[A⁄P₀] = 0`, so `A` is étale over `P₀`
  have hker : LinearMap.ker (KaehlerDifferential.map K P₀ A A) = ⊤ := by
    rw [(KaehlerDifferential.exact_mapBaseChange_map K P₀ A).linearMap_ker_eq,
      LinearMap.range_eq_top.mpr hbij.2]
  have hsub : Subsingleton Ω[A⁄P₀] := ⟨fun x y => by
    obtain ⟨z, rfl⟩ := KaehlerDifferential.map_surjective K P₀ A x
    obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective K P₀ A y
    have hz : KaehlerDifferential.map K P₀ A A z = 0 := by
      rw [← LinearMap.mem_ker, hker]; trivial
    have hw : KaehlerDifferential.map K P₀ A A w = 0 := by
      rw [← LinearMap.mem_ker, hker]; trivial
    rw [hz, hw]⟩
  haveI : Algebra.FormallyUnramified P₀ A := Algebra.FormallyUnramified.mk hsub
  haveI : Algebra.Etale P₀ A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr
      ⟨‹Algebra.FormallyUnramified P₀ A›, ‹Algebra.Smooth P₀ A›⟩
  -- base change to the fraction field of `P₀`
  haveI : IsIntegrallyClosed P₀ := inferInstance
  let L := FractionRing P₀
  let B := TensorProduct P₀ A L
  have hB : IsIntegrallyClosedIn A B :=
    isIntegrallyClosedIn_tensorProduct_fractionRing (P := P₀) (A := A)
  have hinj : Function.Injective (algebraMap A B) :=
    injective_algebraMap_tensorProduct_fractionRing (P := P₀) (A := A)
  have hdom : IsDomain B := isDomain_tensorProduct_fractionRing (P := P₀) (A := A)
  -- `B` is étale over the field `L`: transfer along the swap isomorphism.  The `L`-algebra
  -- structure on `B` (given by the *second* factor) is only introduced locally, so that it does
  -- not interfere with the (global) `A`-algebra structure used below.
  have hfield : IsField B := by
    letI : Algebra L B := Algebra.TensorProduct.rightAlgebra
    let e : B ≃ₐ[L] TensorProduct P₀ L A :=
      { (Algebra.TensorProduct.comm P₀ A L) with
        commutes' := fun l => by
          show (Algebra.TensorProduct.comm P₀ A L) ((algebraMap L B) l) = _
          rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.comm_tmul,
            Algebra.TensorProduct.algebraMap_apply]
          simp }
    haveI : Algebra.Etale L (TensorProduct P₀ L A) := Algebra.Etale.baseChange P₀ A L
    haveI : Algebra.Etale L B := Algebra.Etale.of_equiv e.symm
    exact isField_of_etale_of_isDomain (L := L) (B := B)
  exact isIntegrallyClosed_of_isIntegrallyClosedIn_field hfield hinj hB

/-- A domain which is a smooth algebra over a field is integrally closed.

Proof sketch: use `IsIntegrallyClosed.of_localization_maximal`; for a maximal ideal `m` of `A`,
`Algebra.IsSmoothAt.exists_notMem_isStandardSmooth` (apply it to `m`; it needs
`Algebra.FinitePresentation K A`, which holds since `Algebra.Smooth K A`) gives `f ∉ m` with
`Algebra.IsStandardSmooth K (Localization.Away f)`; that localisation is a domain, so
`Work.Normality.isIntegrallyClosed_of_isStandardSmooth` gives `IsIntegrallyClosed (Localization.Away f)`
and then `isIntegrallyClosed_of_isLocalization` applied to the submonoid
`(Ideal.primeCompl m).map (algebraMap A (Localization.Away f))` (whose elements are non-zero
divisors, as `Localization.Away f` is a domain) shows that the localisation of `Localization.Away f`
at that submonoid — which is `Localization.AtPrime m`, as `f ∉ m` — is integrally closed. -/
theorem isIntegrallyClosed_of_smooth_algebra {K : Type*} [Field K] {A : Type*} [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.Smooth K A] : IsIntegrallyClosed A := by
  refine IsIntegrallyClosed.of_localization_maximal fun m hm hmax => ?_
  obtain ⟨f, hfm, hstd⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (R := K) (S := A) m
  have hf0 : f ≠ 0 := fun h => hfm (by rw [h]; exact m.zero_mem)
  let B := Localization.Away f
  let T := Localization.AtPrime m
  -- `Localization.Away f` is a domain and standard smooth over `K`, hence integrally closed
  haveI : IsDomain B := Localization.Away.isDomain hf0
  haveI : Algebra.IsStandardSmooth K B := hstd
  haveI : IsIntegrallyClosed B := isIntegrallyClosed_of_isStandardSmooth_flex (K := K) (A := B)
  -- `f` is invertible in `T = Localization.AtPrime m`, so `T` is a `B`-algebra
  have hfm' : f ∈ m.primeCompl := Ideal.mem_primeCompl_iff.mpr hfm
  have hunit : IsUnit (algebraMap A T f) :=
    IsLocalization.map_units (M := m.primeCompl) T ⟨f, hfm'⟩
  have hpow : ∀ y : ↥(Submonoid.powers f), IsUnit ((IsScalarTower.toAlgHom K A T) (y : A)) :=
    fun y => by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (z := f) (y : A)).mp y.2
      rw [← hk, map_pow]
      exact hunit.pow k
  let φ : B →ₐ[K] T := IsLocalization.liftAlgHom (A := K) (M := Submonoid.powers f) (S := B)
    (P := T) (f := IsScalarTower.toAlgHom K A T) hpow
  -- `letI`, not `haveI`: the instance has to be definitionally transparent below
  letI : Algebra B T := φ.toRingHom.toAlgebra
  have hφ : ∀ a : A, φ (algebraMap A B a) = algebraMap A T a := fun a =>
    IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) hpow a
  haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun a => (hφ a).symm
  -- `T` is the localisation of `B` at the image of `m.primeCompl`
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (Submonoid.powers f)) T :=
    IsLocalization.of_le_isUnit fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (z := f) a).mp ha
      rw [← hk, map_pow]
      exact hunit.pow k
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B m.primeCompl) T :=
    IsLocalization.commutes B T T (Submonoid.powers f) m.primeCompl
  -- the image of `m.primeCompl` in the domain `B` consists of non-zero-divisors
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective (M := Submonoid.powers f) B fun x hx => by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (z := f) x).mp hx
      rw [← hk]
      exact pow_ne_zero k hf0
  have hM' : Algebra.algebraMapSubmonoid B m.primeCompl ≤ B⁰ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    obtain rfl : a = 0 := hinj (hzero.trans (map_zero _).symm)
    exact ha m.zero_mem
  exact isIntegrallyClosed_of_isLocalization T (Algebra.algebraMapSubmonoid B m.primeCompl) hM'

end

end Work.Normality
