import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coprimality to an ideal modulus descends along the relative norm

`FracCoprimeId 𝔪 A` says that the fractional ideal `A` of `K` has no prime factor dividing the
ideal modulus `𝔪`.  The lemma proved here is the descent statement for the relative norm: if an
integral ideal `I ≠ 0` of `L` is coprime to the extension `𝔪·𝓞 L` of the modulus, then its relative
norm `N_{L/K} I` is coprime to `𝔪`.

Indeed, the `𝔭`-adic exponent of the relative norm is the weighted sum
`∑_{𝔓 | 𝔭} f(𝔓/𝔭) · v_𝔓(I)` (`NK.CFTLib.ARL.count_relNormFI`), and each prime `𝔓 | 𝔭` of `L` above
a prime `𝔭 | 𝔪` still satisfies `𝔓 | 𝔪·𝓞 L` (because `𝔪 ⊆ 𝔭` and `𝔓` lies over `𝔭`), so every
exponent in the sum vanishes.

The auxiliary lemma `dvdPrime_map_of_liesOver` records the first half of that: divisibility of the
modulus is inherited by the base change at every prime above.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- **Divisibility of the modulus is preserved by base change.** If `𝔓` is a prime of `L` above the
prime `𝔭` of `K` and `𝔭 | 𝔪`, then `𝔓 | 𝔪·𝓞 L`. -/
lemma dvdPrime_map_of_liesOver {𝔪 : Ideal (NumberField.RingOfIntegers K)}
    {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {𝔓 : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : 𝔓.asIdeal.LiesOver 𝔭.asIdeal)
    (h𝔭 : NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭) :
    NK.CFTLib.ArtinReciprocityIdeal.DvdPrime
      (Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔪) 𝔓 := by
  rw [NK.CFTLib.ArtinReciprocityIdeal.DvdPrime] at h𝔭 ⊢
  rw [Ideal.map_le_iff_le_comap]
  rw [show Ideal.comap (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)) 𝔓.asIdeal = 𝔭.asIdeal from ?_]
  · exact h𝔭
  · rw [← Ideal.under_def]
    exact ((Ideal.liesOver_iff 𝔓.asIdeal 𝔭.asIdeal).mp h).symm

theorem fracCoprimeId_relNorm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) {I : Ideal (NumberField.RingOfIntegers L)}
    (hI : I ≠ ⊥)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := L)
      (Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) 𝔪)
      (NK.CFTLib.ArtinReciprocityIdeal.idealUnit I hI)) :
    NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪
      (NK.CFTLib.ArtinReciprocityIdeal.idealUnit (Ideal.relNorm (NumberField.RingOfIntegers K) I)
        (fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h))) := by
  intro 𝔭 h𝔭
  rw [show ((NK.CFTLib.ArtinReciprocityIdeal.idealUnit
        (Ideal.relNorm (NumberField.RingOfIntegers K) I) _ :
        NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      ((Ideal.relNorm (NumberField.RingOfIntegers K) I :
        Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) from rfl]
  rw [← NK.CFTLib.ARL.relNormFI_coeIdeal (K := K) (L := L) I hI]
  rw [NK.CFTLib.ARL.count_relNormFI]
  rw [NK.CFTLib.ARL.relNormExp]
  apply Finset.sum_eq_zero
  intro 𝔓 h𝔓
  have hlies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)).mp h𝔓
  have hdvd := dvdPrime_map_of_liesOver hlies h𝔭
  have hc : FractionalIdeal.count L 𝔓 ((I : Ideal (NumberField.RingOfIntegers L)) :
      FractionalIdeal (NumberField.RingOfIntegers L)⁰ L) = 0 := hcop 𝔓 hdvd
  rw [hc, mul_zero]

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
