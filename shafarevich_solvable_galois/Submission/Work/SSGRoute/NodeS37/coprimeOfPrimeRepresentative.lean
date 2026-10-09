import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_localNormalise
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coprimality of `z = b y²` from a prime representative

This is the elementary divisor-arithmetic half of the *representative normalisation* of
Schmidt--Wingberg's p. 16 computation (`ACTION_claimOfPreTwo_p16_carve_session39.md` §4.3, §7 and
§9 item 2).

Input: the divisor of `b` is `𝔮 · A²` (`hb`, the `(DIV)` form of condition (1)), a unit `y` with
`A · (y) = Q'` for a prime `Q'` (`hy`, the output of the Chebotarev/class-field input
`NodeS37.exists_prime_datum_of_idealClass`), and the three freshness conditions

* `placeSmul ρ Q' ≠ Q'` (the prime is not ρ-fixed),
* `placeSmul ρ 𝔮 ≠ 𝔮`,
* `Q' ≠ placeSmul ρ 𝔮`.

Conclusion: for `z := b y²`, whose divisor is `𝔮 · Q'²`, the supports of `z` and of `ρz` are
disjoint, and `ρ𝔮 ∉ supp z`.  These are exactly the hypotheses under which SW's Σ-dichotomy works
at the ρ-fixed primes (`v_P(a) = 0` for `P | X`), and they are the conclusion of
`TwoRec.exists_coprime_representative_two`.

The two `count` lemmas used are the proved
`Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_mul_unit` and
`Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_pow_unit`.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute
open scoped Classical

/-- **The divisor of a unit is Galois-equivariant**: conjugating the unit by `ρ` and the prime by
`ρ` does not change the `count`.  (The `placeSmul` form of `H9.swCount_conjUnit`.) -/
theorem count_placeSmul_eq_count {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ρ : L ≃ₐ[k] L) (y : Lˣ)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    FractionalIdeal.count L (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
          ((Units.map ρ.toRingEquiv.toMonoidHom y : Lˣ) : L))
      = FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
          (y : L)) := by
  rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := L)
      (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) (Units.ne_zero _),
    Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := L) P (Units.ne_zero y),
    show (Units.map ρ.toRingEquiv.toMonoidHom y : L) = ρ (y : L) from rfl,
    show Commons.NumberTheory.NumberField.Completion.placeSmul ρ P =
      Submission.NeukirchUchida.Local.placeSmul ρ P from rfl,
    Submission.NeukirchUchida.Local.heightOneSpectrum_valuation_placeSmul (K := k) (L := L) ρ P (y : L)]

/-- **`placeSmul ρ⁻¹` undoes `placeSmul ρ`** — the Galois transport on the height-one spectra is an
action of `Gal(L/k)`.  (No hypothesis on `ρ` is needed, only `ρ⁻¹ * ρ = 1`.) -/
theorem placeSmul_inv_placeSmul {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ρ : L ≃ₐ[k] L)
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P) = P := by
  rw [← Commons.NumberTheory.NumberField.Completion.placeSmul_mul, inv_mul_cancel,
    Commons.NumberTheory.NumberField.Completion.placeSmul_one]

/-- **The coprimality of `z = b y²` from a prime representative.**  If `div(b) = 𝔮 · A²`, if `y`
realises the prime `Q'` as `A · (y) = Q'`, and if `Q'` is neither ρ-fixed, nor `ρ𝔮`, nor `𝔮`
(the last is not needed), then for `z = b y²` the supports of `z` and `ρz` are disjoint and `ρ𝔮`
does not lie in the support of `z`. -/
theorem coprimeOfPrimeRepresentative {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (ρ : L ≃ₐ[k] L) (hρ2 : ρ ^ 2 = 1) (b y : Lˣ)
    (𝔮 Q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers L)) L)
    (hb : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) (b : L))
      = (if P = 𝔮 then 1 else 0) + 2 * FractionalIdeal.count L P A)
    (hy : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      FractionalIdeal.count L P A + FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) (y : L))
      = (if P = Q' then 1 else 0))
    (hQ : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ Q')
    (h𝔮 : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ 𝔮)
    (hQ𝔮 : Q' ≠ Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮) :
    (∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        FractionalIdeal.count L P
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
            (((b * y ^ 2 : Lˣ)) : L)) ≠ 0 →
      FractionalIdeal.count L (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
          (((b * y ^ 2 : Lˣ)) : L)) = 0) ∧
    FractionalIdeal.count L (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L))
          (((b * y ^ 2 : Lˣ)) : L)) = 0 := by
  set z : Lˣ := b * y ^ 2 with hzdef
  -- the divisor of `z` is `𝔮 · Q'²`
  have hz : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      FractionalIdeal.count L P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) (z : L))
      = (if P = 𝔮 then 1 else 0) + 2 * (if P = Q' then 1 else 0) := by
    intro P
    have h1 := Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_mul_unit (K := L) P b (y ^ 2)
    have h2 := Work.SSGRoute.ZDataTwo.TwoRec.count_spanSingleton_pow_unit (K := L) P y 2
    have h3 := hb P
    have h4 := hy P
    rw [hzdef]
    rw [h1, h2]
    push_cast
    linarith
  -- the prime `ρ𝔮` is neither `𝔮` nor `Q'`
  have hrhoqQ : Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮 ≠ Q' :=
    fun h => hQ𝔮 h.symm
  constructor
  · intro P hP
    -- `P ∈ supp z` forces `P = 𝔮` or `P = Q'`
    rw [hz P] at hP
    have hcase : P = 𝔮 ∨ P = Q' := by
      by_contra h
      push_neg at h
      rw [if_neg h.1, if_neg h.2] at hP
      norm_num at hP
    rw [hz (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)]
    rcases hcase with hcaseq | hcaseQ
    · -- `P = 𝔮`: `ρ𝔮 ≠ 𝔮` and `ρ𝔮 ≠ Q'`
      rw [hcaseq, if_neg h𝔮, if_neg hrhoqQ]
      norm_num
    · -- `P = Q'`: `ρQ' ≠ Q'`, and `ρQ' ≠ 𝔮` since `ρ⁻¹` undoes `ρ`
      have hQnu : Commons.NumberTheory.NumberField.Completion.placeSmul ρ Q' ≠ 𝔮 := by
        intro h
        have h' := congrArg (Commons.NumberTheory.NumberField.Completion.placeSmul ρ⁻¹) h
        rw [placeSmul_inv_placeSmul, inv_eq_of_mul_eq_one_right hρ2] at h'
        exact hQ𝔮 h'
      rw [hcaseQ, if_neg hQnu, if_neg hQ]
      norm_num
  · -- `ρ𝔮 ∉ supp z`
    rw [hz (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔮)]
    rw [if_neg h𝔮, if_neg hrhoqQ]
    norm_num

end Work.SSGRoute.NodeS37
