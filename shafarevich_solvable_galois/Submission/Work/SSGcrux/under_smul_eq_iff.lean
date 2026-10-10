import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.Sha2Lib.liesOver_iff_mem_orbitFinset
import Submission.Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two Galois translates of a prime have the same contraction to `K`

This file proves `Work.SSGcrux.under_smul_eq_iff`, the (elementary) Galois-theoretic input of
Shafarevich's theorem that is used when comparing the blocks of two elements of `Gal(L/k)`:

for a tower of number fields `k ⊆ K ⊆ L` with `L/k` Galois (so `K/k` and `L/K` Galois), a prime
`q'` of `𝓞 L` and `σ τ : Gal(L/k)`,

`(σ • q') ∩ 𝓞 K = (τ • q') ∩ 𝓞 K` iff `σ = h τ δ` with `h ∈ Gal(L/K)` (fixing `K` pointwise) and
`δ` in the decomposition group of `q'`.

The mathematical content is:

* two primes of `L` above the same prime of `K` are conjugate under `Gal(L/K)`
  (`Work.SSGRoute.Sha2Lib.liesOver_iff_mem_orbitFinset`),
* `Ideal.under` of a `Gal(L/k)`-translate is transported to `𝓞 K` by `σ|_K`
  (`Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum`).

The two `Gal(L/k)`-actions in play — the "Čebotarev" action `NK.Chebotarev.instSMulPrimeIdeal` on
`𝓞 L`-primes (which the statement uses) and `NK.GlobalCFT.Place.smulHeightOneSpectrum` (the one
carried by `Place`, which the imported lemmas use) — agree, see
`smul_primeIdeal_eq_smulHeightOneSpectrum'`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField

namespace Work.SSGcrux

/-- `Place.ringOfIntegersEquiv` is `galRestrict`, as ring homomorphisms of `𝓞 L`. -/
theorem ringHom_ringOfIntegersEquiv_eq_galRestrict {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    ((NK.GlobalCFT.Place.ringOfIntegersEquiv σ :
        NumberField.RingOfIntegers L ≃+* NumberField.RingOfIntegers L) :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) =
      (galRestrict (NumberField.RingOfIntegers k) k L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  rw [NK.GlobalCFT.Galois.ringOfIntegersEquiv_eq_galRestrict σ]
  rfl

/-- **The two `Gal(L/k)`-actions on the finite places of `L` agree**: the "Čebotarev" action
`NK.Chebotarev.instSMulPrimeIdeal` (image prime under the induced automorphism of `𝓞 L`) is
`NK.GlobalCFT.Place.smulHeightOneSpectrum`. -/
theorem smul_primeIdeal_eq_smulHeightOneSpectrum' {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (σ : L ≃ₐ[k] L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (σ • q) = NK.GlobalCFT.Place.smulHeightOneSpectrum σ q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.Chebotarev.smul_primeIdeal_asIdeal, NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
      ← ringHom_ringOfIntegersEquiv_eq_galRestrict σ]
  rfl

/-- The action function `smulHeightOneSpectrum` does not see the base field: viewing an
`L`-automorphism over `K` or over the smaller base `k` gives the same action on finite places. -/
theorem smulHeightOneSpectrum_restrictScalars {k K L : Type} [Field k] [Field K] [Field L]
    [NumberField k] [NumberField K] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (g : L ≃ₐ[K] L)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum (AlgEquiv.restrictScalars k g) Q =
      NK.GlobalCFT.Place.smulHeightOneSpectrum g Q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  rfl

/-- The action law for `smulHeightOneSpectrum`: a product acts by the composite action. -/
theorem smulHeightOneSpectrum_mul' {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (σ τ : L ≃ₐ[k] L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum (σ * τ) q =
      NK.GlobalCFT.Place.smulHeightOneSpectrum σ
        (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q) := by
  refine NK.GlobalCFT.Place.ofFinite_inj.mp ?_
  rw [← NK.GlobalCFT.Place.smul_ofFinite, ← NK.GlobalCFT.Place.smul_ofFinite,
      ← NK.GlobalCFT.Place.smul_ofFinite]
  exact mul_smul σ τ (NK.GlobalCFT.Place.ofFinite q)

/-- The identity acts trivially on finite places. -/
theorem smulHeightOneSpectrum_one' {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    NK.GlobalCFT.Place.smulHeightOneSpectrum (1 : L ≃ₐ[k] L) q = q := by
  refine NK.GlobalCFT.Place.ofFinite_inj.mp ?_
  rw [← NK.GlobalCFT.Place.smul_ofFinite]
  exact one_smul (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)

/-- `ringOfIntegersEquiv` of the identity is the identity. -/
theorem ringOfIntegersEquiv_one {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] :
    NK.GlobalCFT.Place.ringOfIntegersEquiv (1 : K ≃ₐ[k] K) = 1 := by
  ext x
  rw [NK.GlobalCFT.Place.ringOfIntegersEquiv_apply]
  rfl

/-- **The decomposition group of a finite place** is the stabiliser of the underlying prime, i.e.
membership is fixing the prime. -/
theorem mem_decompK_ofFinite_iff {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (δ : L ≃ₐ[k] L) :
    δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q) ↔
      NK.GlobalCFT.Place.smulHeightOneSpectrum δ q = q := by
  rw [SSGRoute.PTExt.decompK, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]

/-- **Two Galois translates of a prime have the same contraction to `K` iff they differ by an
element fixing `K` pointwise and an element of the decomposition group of `q'`.** -/
theorem under_smul_eq_iff {k K L : Type} [Field k] [Field K] [Field L] [NumberField k]
    [NumberField K] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k K]
    [IsGalois k K] [IsGalois K L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ τ : L ≃ₐ[k] L) :
    ((σ • q').asIdeal.under (NumberField.RingOfIntegers K)
        = (τ • q').asIdeal.under (NumberField.RingOfIntegers K)) ↔
      ∃ h : L ≃ₐ[k] L, (∀ x : K, h (algebraMap K L x) = algebraMap K L x) ∧
        ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L)
            (NK.GlobalCFT.Place.ofFinite q'), σ = h * τ * δ := by
  classical
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  rw [smul_primeIdeal_eq_smulHeightOneSpectrum' σ q',
      smul_primeIdeal_eq_smulHeightOneSpectrum' τ q']
  constructor
  · -- forward: the two primes lie over the same prime of `𝓞 K`
    intro h
    have hOver : (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q').asIdeal.LiesOver
        ((NK.GlobalCFT.Place.smulHeightOneSpectrum τ q').asIdeal.under
          (NumberField.RingOfIntegers K)) :=
      Ideal.LiesOver.mk h.symm
    have hmem : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q' ∈
        Work.SSGRoute.HSRow.orbitFinset (k := K) (K := L)
          (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q') :=
      (Work.SSGRoute.Sha2Lib.liesOver_iff_mem_orbitFinset K L _ _).mp hOver
    rw [Work.SSGRoute.HSRow.orbitFinset] at hmem
    obtain ⟨g₀, -, hg₀⟩ := Finset.mem_image.mp hmem
    -- `g₀ : Gal(L/K)` carries `τ • q'` to `σ • q'`
    have hg : NK.GlobalCFT.Place.smulHeightOneSpectrum (AlgEquiv.restrictScalars k g₀)
        (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q')
        = NK.GlobalCFT.Place.smulHeightOneSpectrum σ q' := by
      rw [smulHeightOneSpectrum_restrictScalars g₀
            (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q')]
      exact hg₀
    have hg₂ : NK.GlobalCFT.Place.smulHeightOneSpectrum
        (AlgEquiv.restrictScalars k g₀ * τ) q'
        = NK.GlobalCFT.Place.smulHeightOneSpectrum σ q' := by
      rw [smulHeightOneSpectrum_mul']
      exact hg
    refine ⟨AlgEquiv.restrictScalars k g₀, ?_, (AlgEquiv.restrictScalars k g₀ * τ)⁻¹ * σ, ?_, ?_⟩
    · -- fixes `K` pointwise
      intro x
      rw [AlgEquiv.restrictScalars_apply]
      exact AlgEquiv.commutes g₀ x
    · -- the remaining factor lies in the decomposition group of `q'`
      rw [mem_decompK_ofFinite_iff q' _]
      rw [smulHeightOneSpectrum_mul']
      rw [← hg₂]
      rw [← smulHeightOneSpectrum_mul', inv_mul_cancel, smulHeightOneSpectrum_one']
    · -- the factorisation
      group
  · -- converse
    rintro ⟨h, hfix, δ, hδmem, hσeq⟩
    have hδ : NK.GlobalCFT.Place.smulHeightOneSpectrum δ q' = q' :=
      (mem_decompK_ofFinite_iff q' δ).mp hδmem
    -- `σ • q' = h • (τ • q')`
    have h1 : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q' =
        NK.GlobalCFT.Place.smulHeightOneSpectrum h
          (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q') := by
      rw [hσeq, smulHeightOneSpectrum_mul']
      rw [smulHeightOneSpectrum_mul', hδ]
    rw [h1]
    -- `h ∈ Gal(L/K)`, so it does not change the contraction to `𝓞 K`
    have hres : AlgEquiv.restrictNormal h K = 1 := by
      refine AlgEquiv.ext fun x => ?_
      refine (algebraMap K L).injective ?_
      rw [AlgEquiv.restrictNormal_commutes h K x, hfix x]
      rfl
    rw [Work.SSGRoute.Sha2Lib.under_smul_heightOneSpectrum h
        (NK.GlobalCFT.Place.smulHeightOneSpectrum τ q')]
    rw [hres, ringOfIntegersEquiv_one]
    rw [show ((1 : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers K) :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) = RingHom.id _ from by
      ext x; rfl, Ideal.map_id]

end Work.SSGcrux
