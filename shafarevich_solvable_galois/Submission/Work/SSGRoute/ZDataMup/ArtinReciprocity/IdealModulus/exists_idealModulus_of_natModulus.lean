/-
# From a natural-number modulus to the ideal modulus supported on the ramified primes

Composition of `ramifiedPart` (for `M > 1` unramified outside `(M)`, produce the ideal
`𝔪 = ∏_{𝔭 ramified} 𝔭^{v_𝔭(M)}`, whose prime support is *exactly* the ramified primes and whose
`𝔭`-adic valuations agree with `(M)`) with `dictionary_ramifiedPart` (that `𝔪` is admissible for the
ideal modulus, and the congruence at the ramified primes at level `M` gives `CongrOneId 𝔪`).

This is the bridge from finding (A) — `mRam`, its admissibility and strong support — to the
ideal-modulus lane, where the idèlic construction is Frobenius-normalised at *every* prime not
dividing `𝔪`, i.e. at every unramified prime.
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ramifiedPart
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.dictionary_ramifiedPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **The ideal modulus supported exactly on the ramified primes**, with its admissibility and the
congruence consequence. -/
theorem exists_idealModulus_of_natModulus
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) (hM : 1 < M)
    (hramM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      (M : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1)
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible (K := K) (L := L) M) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ ∧
      NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪 ∧
      NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪 ∧
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K),
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 ↔
          Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) ≠ 1) ∧
      (∀ b : Kˣ,
        (∀ 𝔮 : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ 𝔮.asIdeal →
          Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 L) ≠ 1 →
          Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
            ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K)) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal),
          0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
                (algebraMap K w.Completion ((b : Kˣ) : K))) →
        NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 b) := by
  classical
  obtain ⟨𝔪, h𝔪, hsupp, hcount, hram⟩ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ramifiedPart (K := K) (L := L) M hM hramM
  have hadmId : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪 := by
    refine (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.dictionary_ramifiedPart (K := K) (L := L) M hM 𝔪 h𝔪
      hsupp hcount hadm 1 ?_ ?_).1
    · intro 𝔮 _ _
      simp
    · intro w hw
      simp
  exact ⟨𝔪, h𝔪, hadmId, hram, hsupp, fun b hb hp =>
    (Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.dictionary_ramifiedPart (K := K) (L := L) M hM 𝔪 h𝔪
      hsupp hcount hadm b hb hp).2⟩

end NK.CFTLib.ArtinReciprocityIdeal
