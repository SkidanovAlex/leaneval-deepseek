import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleArl
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinSymAux
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
import Submission.Work.SSGRoute.ZDataMup.MupAux.Base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cycle of an ideal modulus supported exactly on the ramified primes

Given an ideal modulus `𝔪 ≠ ⊥` of `K` whose prime divisors are *exactly* the primes ramified in a
finite Galois extension `L/K` (`hsupp`), and such that the ideal-theoretic Artin symbol kills every
principal ideal `(b)` with `b ≡ 1 mod* 𝔪` (`hdrop`), there is a **cycle** `c` (Lang's ideal
modulus, `Work.SSGRoute.ZDataMup.Cycle`) whose support is exactly the set of ramified primes, whose
levels are positive on that support, and whose congruence-`1` subgroup is that of `𝔪` — so that the
conductor drop `hdrop` holds for the cycle `c`.

The cycle is the `𝔪`-cycle `c = ∏_{𝔭 | 𝔪} 𝔭^{v_𝔭(𝔪)}`: support the primes `𝔭 | 𝔪`
(`Ideal.finite_factors`), level the `𝔭`-adic exponent `count K 𝔭 𝔪` of `𝔪`
(`FractionalIdeal.count_coe_nonneg`, `dvdPrime_count_pos`). The dictionary between `c` and `𝔪` is
then immediate from `𝔭 ∈ c.supp ↔ 𝔭 | 𝔪` and `(c.lev 𝔭 : ℤ) = count K 𝔭 𝔪`, and the
unramified vocabulary transfers along
`isUnramified_iff_ramificationIdxIn_eq_one_Id` (`MupAux/Base.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

/-- **A cycle attached to an ideal modulus supported exactly on the ramified primes.** -/
theorem cycleOfIdealModulus
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 ↔
        Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) ≠ 1)
    (hdrop : ∀ b : Kˣ, NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 b →
      NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((b : Kˣ) : K)) = 1) :
    ∃ c : Work.SSGRoute.ZDataMup.Cycle K,
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q → Q ∈ c.supp) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Q ∈ c.supp → ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) Q) ∧
      (∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭) ∧
      (∀ b : Kˣ, c.CongrOne b →
        NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            ((b : Kˣ) : K)) = 1) := by
  classical
  -- ## finiteness of the primes dividing `𝔪`
  have hfin : {Q : HeightOneSpectrum (𝓞 K) |
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 Q}.Finite := by
    refine (Ideal.finite_factors (I := 𝔪) ?_).subset ?_
    · simpa [Ideal.zero_eq_bot] using h𝔪
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact Ideal.dvd_iff_le.mpr hp
  -- ## the cycle `c = ∏_{𝔭 | 𝔪} 𝔭^{v_𝔭(𝔪)}`
  let c : Work.SSGRoute.ZDataMup.Cycle K :=
    ⟨hfin.toFinset, fun Q => (FractionalIdeal.count K Q (𝔪 : FractionalIdeal (𝓞 K)⁰ K)).toNat⟩
  have hc : ∀ Q : HeightOneSpectrum (𝓞 K),
      Q ∈ c.supp ↔ NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 Q :=
    fun Q => hfin.mem_toFinset
  have hlevcast : ∀ Q : HeightOneSpectrum (𝓞 K),
      ((c.lev Q : ℕ) : ℤ) = FractionalIdeal.count K Q (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
    fun Q => Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K Q 𝔪)
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · -- every ramified prime divides `𝔪`, hence belongs to the support
    intro Q hQ
    refine (hc Q).mpr ((hsupp Q).mpr ?_)
    intro h1
    exact hQ ((NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
      (K := K) (L := L) Q).mpr h1)
  · -- the support consists of ramified primes only
    intro Q hQ hunr
    exact (hsupp Q).mp ((hc Q).mp hQ)
      ((NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one_Id
        (K := K) (L := L) Q).mp hunr)
  · -- the levels are positive on the support
    intro Q hQ
    have h := NK.CFTLib.ArtinReciprocityIdeal.dvdPrime_count_pos (K := K) h𝔪 ((hc Q).mp hQ)
    have h0 : (0 : ℤ) ≤ FractionalIdeal.count K Q (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
      le_trans (by norm_num) h
    simpa [c] using (Int.le_toNat h0).mpr h
  · -- the congruence-`1` subgroup of the cycle `c` is that of `𝔪`
    intro b hb
    refine hdrop b ⟨fun Q hQ => ?_, hb.2⟩
    have h2 := hb.1 Q ((hc Q).mpr hQ)
    rwa [hlevcast Q] at h2

end Work.SSGRoute.ZDataMup
