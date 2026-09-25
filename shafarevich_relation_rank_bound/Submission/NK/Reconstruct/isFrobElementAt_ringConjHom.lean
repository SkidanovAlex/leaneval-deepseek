import Mathlib
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.conjLevel
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff
import Submission.NK.Chebotarev.IsFrobAtConj

/-!
# The Frobenius property of `IsFrobElementAt` is preserved by conjugation by a ring automorphism

Let `K` be a number field with separable closure `K'`, `L ⊆ K'` a finite (number field) level and
`θ : K' ≃+* K'` a ring automorphism preserving `L` as a set.  Write `δ = θ|_L` for the induced
automorphism of `L` and `g ↦ θ g θ⁻¹` for the conjugation action of `θ` on `Gal(K'/L)`
(`NK.Reconstruct.ringConjHom`).

The main result of this file is `NK.Reconstruct.isFrobElementAt_ringConjHom`: if `σ ∈ Gal(K'/L)`
is a Frobenius element at the prime `𝔭` of `𝓞 L` over the base `L` (`NK.Reconstruct.IsFrobElementAt`,
Serre's notion), then the conjugate `θ σ θ⁻¹` is a Frobenius element at the transported prime
`δ(𝔭) = primeTransport δ 𝔭`.

The proof reduces, level by level over `L`, to the transport of primes along the level isomorphism
`θ : θ⁻¹M ≃+* M` (`NK.Reconstruct.conjLevelRingEquiv`) supplied by
`NK.Reconstruct.isFrobAt_primeTransport_iff`: applying the hypothesis to the conjugate level `θ⁻¹M`
produces a prime `P | 𝔭` at which `σ|_{θ⁻¹M}` is a Frobenius element, and transporting `P` along `θ`
gives a prime at which `θ σ θ⁻¹|_M = θ σ|_{θ⁻¹M} θ⁻¹` is a Frobenius element
(`NK.Reconstruct.conjLevelAlgEquivHom_restrictNormalHom`).  The only bookkeeping is the prime
below the transported prime, `NK.Reconstruct.under_primeTransport_conjLevel` below.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped NumberField

/-- Membership in `Ideal.map` of a ring equivalence, in terms of the inverse image. -/
private lemma mem_idealMap_iff_symm_mem {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    (I : Ideal R) (y : S) : y ∈ Ideal.map e I ↔ e.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rwa [← hxy, RingEquiv.symm_apply_apply]
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

/-- **The prime below a transported prime, for the level `θ⁻¹M`.**

The ring isomorphism `θ : θ⁻¹M ≃+* M` (`NK.Reconstruct.conjLevelRingEquiv`) is compatible with
the automorphism `δ = θ|_L` of the base field `L`, so transporting a prime `P` of `θ⁻¹M` along `θ`
transports the prime of `L` below `P` along `δ`. -/
private theorem under_primeTransport_conjLevel {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') [NumberField ↥L]
    (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L) (M : IntermediateField ↥L K')
    [NumberField ↥M] (P : NK.Chebotarev.PrimeIdeal ↥(conjLevel L θ hθ M)) :
    (primeTransport (conjLevelRingEquiv L θ hθ M) P).asIdeal.under (𝓞 ↥L)
      = Ideal.map (ringOfIntegersEquiv (thetaOnL L θ hθ)) (P.asIdeal.under (𝓞 ↥L)) := by
  have hkey : ∀ y : 𝓞 ↥L,
      (ringOfIntegersEquiv (conjLevelRingEquiv L θ hθ M)).symm
          (algebraMap (𝓞 ↥L) (𝓞 ↥M) y)
        = algebraMap (𝓞 ↥L) (𝓞 ↥(conjLevel L θ hθ M))
            ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y) := by
    intro y
    rw [RingEquiv.symm_apply_eq]
    have hsq : ringOfIntegersEquiv (conjLevelRingEquiv L θ hθ M)
        (algebraMap (𝓞 ↥L) (𝓞 ↥(conjLevel L θ hθ M))
          ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y))
        = algebraMap (𝓞 ↥L) (𝓞 ↥M) y := by
      rw [show ringOfIntegersEquiv (conjLevelRingEquiv L θ hθ M)
            (algebraMap (𝓞 ↥L) (𝓞 ↥(conjLevel L θ hθ M))
              ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y))
          = algebraMap (𝓞 ↥L) (𝓞 ↥M)
              (ringOfIntegersEquiv (thetaOnL L θ hθ)
                ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y)) from by
        apply NumberField.RingOfIntegers.ext
        rw [ringOfIntegersEquiv_apply]
        apply Subtype.ext
        rw [conjLevelRingEquiv_apply_coe]
        rw [show ((algebraMap (𝓞 ↥L) (𝓞 ↥(conjLevel L θ hθ M))
              ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y) : 𝓞 ↥(conjLevel L θ hθ M))
              : ↥(conjLevel L θ hθ M))
            = algebraMap ↥L ↥(conjLevel L θ hθ M)
                (((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y : 𝓞 ↥L) : ↥L) from rfl]
        rw [show ((algebraMap (𝓞 ↥L) (𝓞 ↥M)
              (ringOfIntegersEquiv (thetaOnL L θ hθ)
                ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y)) : 𝓞 ↥M) : ↥M)
            = algebraMap ↥L ↥M
                ((ringOfIntegersEquiv (thetaOnL L θ hθ)
                  ((ringOfIntegersEquiv (thetaOnL L θ hθ)).symm y) : 𝓞 ↥L) : ↥L) from rfl]
        rw [ringOfIntegersEquiv_apply]
        rfl]
      rw [RingEquiv.apply_symm_apply]
    exact hsq.symm
  ext x
  rw [Ideal.under_def, Ideal.mem_comap]
  show (algebraMap (𝓞 ↥L) (𝓞 ↥M) x)
      ∈ Ideal.map (ringOfIntegersEquiv (conjLevelRingEquiv L θ hθ M)) P.asIdeal ↔
    x ∈ Ideal.map (ringOfIntegersEquiv (thetaOnL L θ hθ)) (P.asIdeal.under (𝓞 ↥L))
  rw [mem_idealMap_iff_symm_mem, hkey x, ← Ideal.mem_under]
  exact (mem_idealMap_iff_symm_mem (ringOfIntegersEquiv (thetaOnL L θ hθ))
    (P.asIdeal.under (𝓞 ↥L)) x).symm

/-- **The `L`-levels of `θ σ θ⁻¹` are the `θ`-conjugates of the `L`-levels of `σ`.**

For every finite normal level `M` over `L`, the restriction of the conjugate `θ σ θ⁻¹` to `M` is the
conjugate (by `θ : θ⁻¹M ≃+* M`) of the restriction of `σ` to the conjugate level `θ⁻¹M`.  This is
`NK.Reconstruct.conjLevelAlgEquivHom_restrictNormalHom`, with the conjugation map identified with
`conjAlgEquiv`. -/
private lemma conjAlgEquiv_conjLevelRingEquiv_restrictNormalHom {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K')
    [NumberField ↥L] (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (M : FrobLevel ↥L K') (hτ : MapsBaseLevel (conjLevel L θ hθ M.L) M.L
      (conjLevelRingEquiv L θ hθ M.L)) (σ : Gal(K'/↥L)) :
    conjAlgEquiv (conjLevelRingEquiv L θ hθ M.L) hτ
        (AlgEquiv.restrictNormalHom ↥(conjLevel L θ hθ M.L) σ)
      = AlgEquiv.restrictNormalHom ↥(M.L) (ringConjHom L θ hθ σ) := by
  haveI : IsSepClosure ↥L K' := ⟨IsSepClosure.sep_closed K, inferInstance⟩
  change conjAlgEquiv (conjLevelRingEquiv L θ hθ M.L) hτ
      (AlgEquiv.restrictNormalHom ↥(conjLevel L θ hθ M.L) σ)
    = AlgEquiv.restrictNormalHom ↥(M.L) (ringConjAlgEquiv L θ hθ σ)
  rw [← conjLevelAlgEquivHom_restrictNormalHom L θ hθ M σ]
  ext x
  rw [conjAlgEquiv_apply, conjLevelAlgEquivHom_apply]

/-- **The Frobenius property of `IsFrobElementAt` is preserved by conjugation by a ring
automorphism of `K'` preserving the level `L`.**

Let `K` be a number field with separable closure `K'`, `L ⊆ K'` a finite (number field) level and
`θ : K' ≃+* K'` a ring automorphism preserving `L` as a set.  Then for every `σ ∈ Gal(K'/L)` which
is a Frobenius element at `𝔭`, the conjugate `θ σ θ⁻¹ ∈ Gal(K'/L)` is a Frobenius element at the
transported prime `δ(𝔭)`, `δ = θ|_L`. -/
theorem isFrobElementAt_ringConjHom {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') [NumberField ↥L]
    (θ : K' ≃+* K') (hθ : ∀ x : K', x ∈ L ↔ θ x ∈ L)
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L) (σ : Gal(K'/↥L))
    (hσ : NK.Reconstruct.IsFrobElementAt 𝔭 σ) :
    NK.Reconstruct.IsFrobElementAt
      (NK.Reconstruct.primeTransport (NK.Reconstruct.thetaOnL L θ hθ) 𝔭)
      (NK.Reconstruct.ringConjHom L θ hθ σ) := by
  haveI hscL : IsSepClosure ↥L K' := ⟨IsSepClosure.sep_closed K, inferInstance⟩
  intro M hMfin hMnorm hMnum
  let Mf : FrobLevel ↥L K' := ⟨M, hMfin, hMnorm, hMnum⟩
  obtain ⟨P, hPlies, hPfrob⟩ := hσ (conjLevel L θ hθ M)
  let τ := conjLevelRingEquiv L θ hθ M
  have hτ : MapsBaseLevel (conjLevel L θ hθ M) M τ := by
    constructor
    · intro a
      refine ⟨thetaOnL L θ hθ a, ?_⟩
      ext
      rw [conjLevelRingEquiv_apply_coe]
      rfl
    · intro b
      refine ⟨(thetaOnL L θ hθ).symm b, ?_⟩
      ext
      rw [conjLevelRingEquiv_symm_apply_coe]
      rfl
  have hQunder : (primeTransport τ P).asIdeal.under (𝓞 ↥L)
      = Ideal.map (ringOfIntegersEquiv (thetaOnL L θ hθ)) (P.asIdeal.under (𝓞 ↥L)) :=
    under_primeTransport_conjLevel L θ hθ M P
  have hconjEq : conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom ↥(conjLevel L θ hθ M) σ)
      = AlgEquiv.restrictNormalHom ↥M (ringConjHom L θ hθ σ) :=
    conjAlgEquiv_conjLevelRingEquiv_restrictNormalHom L θ hθ Mf hτ σ
  refine ⟨primeTransport τ P, ?_, ?_⟩
  · refine ⟨?_⟩
    change Ideal.map (ringOfIntegersEquiv (thetaOnL L θ hθ)) 𝔭.asIdeal
      = (primeTransport τ P).asIdeal.under (𝓞 ↥L)
    rw [hQunder, hPlies.over]
  · rw [← hconjEq]
    exact (isFrobAt_primeTransport_iff hτ
      (AlgEquiv.restrictNormalHom ↥(conjLevel L θ hθ M) σ) P).mp hPfrob

end NK.Reconstruct
