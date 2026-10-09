import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.fracCoprimeId_relNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coprimality to an ideal modulus descends along the relative norm of a fractional ideal

`FracCoprimeId 𝔪 A` says that the fractional ideal `A` of `K` has no prime factor dividing the
ideal modulus `𝔪`.  The lemma below is the general (fractional-ideal) form of the descent statement
for the relative norm `N_{L/K}`: if a fractional ideal `A` of `L` is coprime to the extension
`𝔪·𝓞 L` of the modulus, then its relative norm `N_{L/K} A` is coprime to `𝔪`.

This specialises `Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.fracCoprimeId_relNorm`
(which treats the integral ideal `A = idealUnit I hI`) to an arbitrary element of the group of
fractional ideals of `L`.  The argument is the same: the `𝔭`-adic exponent of the relative norm is
the weighted sum `∑_{𝔓 | 𝔭} f(𝔓/𝔭) · v_𝔓(A)` (`NK.CFTLib.ARL.count_relNormFI`), and every prime
`𝔓 | 𝔭` of `L` above a prime `𝔭 | 𝔪` still satisfies `𝔓 | 𝔪·𝓞 L`
(`Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.dvdPrime_map_of_liesOver`), so every exponent
in the sum vanishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

theorem fracCoprimeId_relNormUnit {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {𝔪 : Ideal (NumberField.RingOfIntegers K)}
    {A : NK.CFTLib.ArtinReciprocityIdeal.Frac L}
    (hA : NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := L)
      (Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) 𝔪) A) :
    NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId (K := K) 𝔪
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A) := by
  intro 𝔭 h𝔭
  -- rewrite the `𝔭`-adic exponent through the exponent vector of the relative norm
  rw [show ((NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A :
        NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      NK.CFTLib.ARL.relNormFI (K := K) (L := L)
        (A : FractionalIdeal (NumberField.RingOfIntegers L)⁰ L) from rfl]
  rw [NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero fun 𝔓 h𝔓 => ?_
  have hlies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)).mp h𝔓
  have hdvd := dvdPrime_map_of_liesOver hlies h𝔭
  rw [hA 𝔓 hdvd, mul_zero]

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer
