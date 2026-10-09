import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ZDataMupClean.Hprinc
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.ZDataMupClean_KernelLeId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId
import Submission.Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic case of the conductor drop at the ramified primes

The requested theorem `cyclicCaseStatement_ramifiedSupport_clean` is the statement that the conductor of
a finite cyclic extension `L / K` of number fields is supported on the ramified primes (Neukirch,
*Algebraic Number Theory*, V.6.1; Lang, *Algebraic Number Theory*, X §4).

## The obstruction, and how it is removed

Write `R` for the set of ramified primes of `L / K`, `P(R)` for the rational primes below them and
`R̂ = {𝔮 : p(𝔮) ∈ P(R)}`.  The hypothesis `hramM` says `R ⊆ supp(M)`, and since the support of a
principal ℕ-ideal `(M)` is a union of full fibres over the rational primes, `R̂ ⊆ supp(M)` as well.
The conductor of `L/K` is the *ideal*

  `𝔪 = ∏_{𝔭 ∈ R} 𝔭^{v_𝔭(M)}`,

whose support is exactly `R`, and the theorem is exactly `P(𝔪) ⊆ ker ψ`: the congruence condition
of the hypothesis `hcong` is imposed at the primes in `R` only.  No natural-number modulus can
express `𝔪`, because `supp(m)` for `m : ℕ` is a union of full fibres (this is the obstruction
recorded in `NOTE_conductorDrop_obstruction.md`).  The present file therefore goes through the
*ideal*-modulus theory of `Submission/Work/.../ArtinReciprocity/IdealModulus/`:

* `Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal` turns the product condition at `M`
  into admissibility of `M` (this is where `hprincM` is used);
* `NK.CFTLib.ArtinReciprocityIdeal.exists_idealModulus_of_natModulus`
  (`ramifiedPart` plus `dictionary_ramifiedPart`, on disk) produces the ramified-part ideal `𝔪` of
  `(M)`, admissible for the ideal-modulus theory, with `CongrOneId 𝔪 b` deduced from `hcong` and
  `hpos`;
* `Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId_clean` is Lang's crux for the ideal
  modulus (`ker ψ ∩ I(𝔪) ⊆ P(𝔪)·𝔑(𝔪)`, Lang X §2 Theorem 2 / Childress Proposition 2.2);
* `Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId` is the cyclic norm
  index inequality `[L:K] ≤ [I(𝔪) : P(𝔪)·𝔑(𝔪)]` for the ideal modulus;
* `NK.CFTLib.ArtinReciprocityIdeal.artinSym_spanSingleton_eq_one_of_congrOneId_clean` (on disk) is the
  index assembly `ker ⊆ P·𝔑`, `[I : P·𝔑] ≥ n`, surjectivity of `ψ` on `I(𝔪)`
  (`NK.CFTLib.ArtinReciprocityIdeal.surjId`) that converts the crux into `P(𝔪) ⊆ ker ψ`.

The degenerate case `M = 1` is handled uniformly: then `hramM` says that every finite prime is
unramified and one takes the modulus `𝔪 = ⊤`, for which `I(𝔪) = P(𝔪) = Frac K` and
`CongrOneId ⊤ b` is just total positivity — the classical conductor drop at the trivial modulus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-- Every height one prime ideal of `𝓞 K` is a proper ideal, so `1` is never one of its elements. -/
private lemma one_notMem_heightOneSpectrum (K : Type*) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (1 : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal :=
  fun h => 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/-- The whole ring is a nonzero ideal of `𝓞 K`. -/
private lemma top_ne_bot_ringOfIntegers (K : Type*) [Field K] [NumberField K] :
    (⊤ : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
  intro h
  have h1 : (1 : NumberField.RingOfIntegers K) = 0 := by
    simpa [h] using (show (1 : NumberField.RingOfIntegers K) ∈
      (⊤ : Ideal (NumberField.RingOfIntegers K)) from trivial)
  exact one_ne_zero h1

/-- The congruence condition `CongrOneId ⊤ b` is total positivity. -/
private lemma congrOneId_top (K : Type*) [Field K] [NumberField K] {b : Kˣ}
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.ArtinReciprocityIdeal.CongrOneId (⊤ : Ideal (NumberField.RingOfIntegers K)) b :=
  ⟨fun 𝔭 h => absurd (top_le_iff.mp h) 𝔭.isPrime.ne_top, hpos⟩

/-- The ideal modulus `⊤` is admissible: it has no prime divisor. -/
private lemma isAdmissibleId_top (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L)
      (⊤ : Ideal (NumberField.RingOfIntegers K)) :=
  fun 𝔭 h => absurd (top_le_iff.mp h) 𝔭.isPrime.ne_top

theorem cyclicCaseStatement_ramifiedSupport_clean
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprincM : NK.CFTLib.artinKillsPrincipal K L M)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hM.ne') with hMeq | hMlt
  · -- ## The degenerate case `M = 1`: every finite prime is unramified, and the modulus is `⊤`.
    have hram1 : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
        Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
      intro 𝔭
      refine hramM 𝔭 ?_
      rw [← hMeq]
      simpa using one_notMem_heightOneSpectrum K 𝔭
    exact NK.CFTLib.ArtinReciprocityIdeal.artinSym_spanSingleton_eq_one_of_congrOneId_clean
      (K := K) (L := L) hcomm ⊤ (top_ne_bot_ringOfIntegers K)
      (fun 𝔭 h => absurd (hram1 𝔭) h)
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId_clean (K := K) (L := L)
        hcomm ⊤ (top_ne_bot_ringOfIntegers K) (isAdmissibleId_top K L) (fun 𝔭 h => absurd (hram1 𝔭) h))
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId (K := K) (L := L)
        ⊤ (top_ne_bot_ringOfIntegers K) (fun 𝔭 h => absurd (hram1 𝔭) h)
        (isAdmissibleId_top K L)).1
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId (K := K) (L := L)
        ⊤ (top_ne_bot_ringOfIntegers K) (fun 𝔭 h => absurd (hram1 𝔭) h)
        (isAdmissibleId_top K L)).2
      b (congrOneId_top K hpos)
  · -- ## The case `1 < M`: the ramified-part ideal of `(M)`.
    have hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible (K := K) (L := L) M :=
      Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal (K := K) (L := L)
        hcomm M hM hramM hprincM
    obtain ⟨𝔪, h𝔪, hadmId, hramId, _hsupp, hcongId⟩ :=
      NK.CFTLib.ArtinReciprocityIdeal.exists_idealModulus_of_natModulus (K := K) (L := L)
        M hMlt hramM hadm
    have hker := Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId_clean (K := K) (L := L)
      hcomm 𝔪 h𝔪 hadmId hramId
    obtain ⟨hPNI, hIdx⟩ :=
      Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId (K := K) (L := L)
        𝔪 h𝔪 hramId hadmId
    exact NK.CFTLib.ArtinReciprocityIdeal.artinSym_spanSingleton_eq_one_of_congrOneId_clean
      (K := K) (L := L) hcomm 𝔪 h𝔪 hramId hker hPNI hIdx b (hcongId b hcong hpos)

end Work.SSGRoute.ZDataMup.ArtinReciprocity
