import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ramifiedPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dictionary: the ramified part `𝔪` of `(M)` is an admissible modulus

`Defs.lean` introduces the vocabulary of Lang's conductor theory for an **ideal** modulus
(`DvdPrime`, `CongrOneId`, `IsAdmissibleId`, ...), and `ramifiedPart.lean` produces, for a finite
Galois extension `L / K` and `M > 1` unramified outside `(M)`, an ideal

  `𝔪 = ∏_{𝔭 ramified} 𝔭^{v_𝔭(M)}`

whose prime support is *exactly* the ramified primes of `L / K` and whose `𝔭`-adic valuations agree
with those of the principal modulus `(M)` at the primes dividing it.

This file proves the **dictionary**: for such an `𝔪`, admissibility of the natural-number modulus
`M` (`IsAdmissible`, the hypothesis `hadm` of the cyclic-case arguments) upgrades to admissibility
of the ideal modulus (`IsAdmissibleId`), and the congruence condition at the ramified primes for
`M` upgrades to `CongrOneId` for `𝔪`.

The only mathematical input is that the `𝔭`-adic valuation of the rational integer `M` in the
completion of `K` at `𝔭` is `exp (-(count K 𝔭 (M)))`, where `(M)` is the principal ideal; this is
`val_natCast_adicCompletion_eq_exp_neg_count_span` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open IsDedekindDomain NumberField

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

variable {K : Type*} [Field K] [NumberField K]

/-- **The `𝔭`-adic valuation of the integer `M` in the completion.**  For `M ≠ 0` and a height one
prime `𝔭` of `𝓞 K`, the valuation of `M` in the `𝔭`-adic completion of `K` is
`exp (-(count K 𝔭 (M)))`, where `(M) = Ideal.span {(M : 𝓞 K)}` is the principal ideal. -/
lemma val_natCast_adicCompletion_eq_exp_neg_count_span (M : ℕ) (hM : M ≠ 0)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((M : ℕ) : 𝔭.adicCompletion K)) =
      WithZero.exp (-(FractionalIdeal.count K 𝔭
        ((Ideal.span {(M : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) : ℤ)) := by
  have hM0 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hspan0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hM0
  rw [show ((M : ℕ) : 𝔭.adicCompletion K)
        = algebraMap K (𝔭.adicCompletion K) ((M : ℕ) : K) from
      (map_natCast (algebraMap K (𝔭.adicCompletion K)) M).symm,
    Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔭 ((M : ℕ) : K),
    show ((M : ℕ) : K) = algebraMap (𝓞 K) K ((M : ℕ) : 𝓞 K) from
      (map_natCast (algebraMap (𝓞 K) K) M).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  rw [HeightOneSpectrum.intValuation_if_neg 𝔭 hM0,
    ← FractionalIdeal.count_coe K 𝔭 (J := Ideal.span {(M : 𝓞 K)}) (by simpa using hspan0)]

theorem dictionary_ramifiedPart
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) (hM : 1 < M)
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 ↔
        Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) ≠ 1)
    (hcount : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 →
        FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
          = FractionalIdeal.count K 𝔭
              ((Ideal.span {(M : NumberField.RingOfIntegers K)}) :
                FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
    (hadm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible (K := K) (L := L) M)
    (b : Kˣ)
    (hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((M : ℕ) : 𝔮.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪 ∧
      NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 b := by
  classical
  have hM0 : (M : ℕ) ≠ 0 := by omega
  have hspan0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hM0
  -- The valuation of `M` in the completion at `𝔭` is the level `exp (-(count K 𝔭 (M)))`.
  have hvalM := val_natCast_adicCompletion_eq_exp_neg_count_span (K := K) M hM0
  -- Every prime dividing `𝔪` divides `(M)`, because the two moduli have the same `count` there.
  have hmemM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 → (M : 𝓞 K) ∈ 𝔭.asIdeal := by
    intro 𝔭 h𝔭
    have h1 : 0 < FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (𝓞 K)⁰ K) :=
      (ideal_le_iff_count_pos h𝔪 𝔭).mp h𝔭
    have h2 : 0 < FractionalIdeal.count K 𝔭
        ((Ideal.span {(M : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hcount 𝔭 h𝔭]; exact h1
    exact (Ideal.span_singleton_le_iff_mem 𝔭.asIdeal).mp
      ((ideal_le_iff_count_pos hspan0 𝔭).mpr h2)
  refine ⟨?_, ?_, hpos⟩
  · -- Admissibility of the ideal modulus `𝔪`
    intro 𝔭 h𝔭 𝔮 h𝔮 x hx
    refine hadm 𝔭 (hmemM 𝔭 h𝔭) 𝔮 h𝔮 x ?_
    rw [hvalM 𝔭, ← hcount 𝔭 h𝔭]
    exact hx
  · -- The congruence condition for `b` at the primes dividing `𝔪`
    intro 𝔭 h𝔭
    have hram : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) ≠ 1 := (hsupp 𝔭).mp h𝔭
    have h := hcong 𝔭 (hmemM 𝔭 h𝔭) hram
    rwa [hvalM 𝔭, ← hcount 𝔭 h𝔭] at h

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
