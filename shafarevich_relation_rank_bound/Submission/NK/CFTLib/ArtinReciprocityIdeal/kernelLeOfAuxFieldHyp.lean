import Mathlib
import Submission.NK.NUV2.ARL.transferSelfContained

/-!
# The transfer from the auxiliary-field hypothesis (Lang, ANT X §2, Theorem 2)

This file records `NK.CFTLib.ArtinReciprocityIdeal.kernelLeOfAuxFieldHyp`: the kernel
containment `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)` for a finite cyclic extension `L/K` of number fields at a
modulus `m` supported on the ramified primes, deduced from the auxiliary-field hypothesis
`NK.CFTLib.ARL.AuxFieldHyp K L m` of Artin's lemma (Childress, *Class Field Theory*, Prop. 2.2;
Lang, *Algebraic Number Theory*, X §2, Theorem 2).

The transfer argument is carried out in `Submission/Work/NUV2/ARL/transferSelfContained.lean`
(`NK.NUV2.ARL.SC.kernelLeOfAuxFieldSC`, complete and axiom-clean): factor `A = ∏_{𝔭 ∈ s} 𝔭^{e𝔭}`, pick
`𝔅 ∈ I(E)` over the auxiliary field `E ⊆ L(ζ_M)` whose Artin symbol in `L(ζ_M)/E` is a lift of a
generator `σ` of `Gal(L/K)`, and let `𝔟 = N_{E/K}𝔅`; for each `𝔭 ∈ s` the ideal
`𝔘𝔭 := 𝔓𝔭^{e𝔭}·(N_{E/E𝔭}𝔅)^{-e𝔭s𝔭}` (with `𝔓𝔭 | 𝔭` splitting completely in `E𝔭/K`) has
trivial Artin symbol in `E𝔭·L/E𝔭`, so the cyclotomic cell `cellAtAuxField` puts it in `P·𝔑`; its
norm down is `X𝔭 = 𝔭^{e𝔭}𝔟^{-e𝔭s𝔭}`, and finally `A = (∏𝔭 X𝔭)·𝔟^{∑ e𝔭s𝔭}` with `n ∣ ∑ e𝔭s𝔭` and
`𝔟^n = N_{L/K}(𝔟𝒪_L) ∈ 𝔑(m)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem kernelLeOfAuxFieldHyp (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [IsMulCommutative (Gal(L/K))]
    (m : ℕ) (hm : 0 < m) (haux : NK.CFTLib.ARL.AuxFieldHyp K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  NK.NUV2.ARL.SC.kernelLeOfAuxFieldSC K L m hm haux hram

end NK.CFTLib.ArtinReciprocityIdeal
