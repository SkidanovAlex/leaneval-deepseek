import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.CyclicCaseStatement
import Submission.Work.SSGRoute.ZDataMup.abelian_of_cyclicCase
import Submission.Work.SSGRoute.ZDataMup.KLMine.cyclicCaseMine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

/-- **The cyclic case of the conductor drop.**

For a cyclic extension `L/K`, the reciprocity law at `M` (`hprincM`, i.e.
`NK.CFTLib.artinKillsPrincipal K L M`) forces `M` to be *admissible*
(`Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal`); one then passes to the
ideal modulus `𝔪` carried by the ramified part of `(M)`, where Lang's conductor theorem
(`Work.SSGRoute.ZDataMup.KLMine.kernelLeIdMine`, Lang X §2 Thm. 2 / Childress Prop. 2.2) and the
cyclic norm index inequality (`…IdealModulus.langCyclicRelIndexId`) give `P(𝔪) ⊆ ker ψ`.

This is `Work.SSGRoute.ZDataMup.KLMine.cyclicCaseMine` (axiom-clean: the ideal-modulus crux is
proved, so no natural-number-modulus support obstruction remains). -/
theorem cyclicCaseStatement_lane : CyclicCaseStatement :=
  Work.SSGRoute.ZDataMup.KLMine.cyclicCaseMine

/-- **The conductor of `L/K` is supported on the ramified primes** (Neukirch, *Algebraic Number
Theory*, V.6.1; Lang, *Algebraic Number Theory*, X §4).

Let `m > 0` be a modulus for which (i) every prime `𝔭 ∤ (m)` is unramified in `L` (`hram`) and
(ii) the ideal-theoretic Artin symbol kills every congruence-principal ideal `(a)` with `a ≡ 1 mod m`
and `a` totally positive (`hprinc`, i.e. `NK.CFTLib.artinKillsPrincipal K L m`).  Then for
`b : Kˣ` which is `≡ 1 mod m` **at the ramified primes dividing `(m)` only** (`hcong`) and totally
positive (`hpos`), the Artin symbol of the principal ideal `(b)` is trivial.

Note: this is the same statement as `Work.SSGRoute.ZDataMup.conductorDrop_ramifiedCongr`; it is
restated here (at a fresh path, so as not to touch that module) because it is the isolated
arithmetic input of the local–global Artin map lane. -/
theorem conductorDrop_ramifiedCongrLane
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 := by
  exact abelian_of_cyclicCase cyclicCaseStatement_lane hcomm m hm hram hprinc b hcong hpos

end Work.SSGRoute.ZDataMup
