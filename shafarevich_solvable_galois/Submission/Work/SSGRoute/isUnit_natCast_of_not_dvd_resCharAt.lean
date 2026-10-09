import Mathlib
import Submission.Work.SSGRoute.InertiaArithImports
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An integer prime to the residue characteristic is a unit of the valuation ring

Let `k` be a number field, `Ω` a field with an algebra structure over `k`, and `A ≤ Ω` a valuation
subring of `Ω` whose restriction to `k` is a *finite* place of `k`, i.e.
`A.comap (algebraMap k Ω) ≠ ⊤` (`SSGRoute.IsFinPlace k A`).  Write
`𝔭 = Submission.NeukirchUchida.primeOf A hA` for the height-one prime of `𝓞 k` below `A`, and
`NK.TameStructureDeep.Tame.resCharAt 𝔭` for the residue characteristic of the completion at `𝔭`
(the characteristic of the residue field, i.e. the rational prime below `𝔭`).

We prove:

> if `resCharAt 𝔭 ∤ n` then `(n : ↥A)` is a unit of the valuation ring `↥A`.

This is the local arithmetic input (`hunit`) of `Work.SSGRoute.mem_localInertia_iff_isInertia`: the
integers prime to the residue characteristic have to be recognised as units of the local ring.

The proof has three ingredients:

* `charP_quot_resCharAt` — the residue field `𝓞 k ⧸ 𝔭` (which is the residue field of the
  completion, by `Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists`) has
  characteristic `resCharAt 𝔭`, hence `resCharAt 𝔭 ∣ n ↔ (n : 𝓞 k ⧸ 𝔭) = 0`;
* `resCharAt_dvd_iff_mem_of_numberField` — `resCharAt 𝔭 ∣ n ↔ (n : 𝓞 k) ∈ 𝔭`;
* `valuation_lt_one_iff_mem_primeOf_of_numberField` — for `x : 𝓞 k`, the inequality
  `A.valuation x < 1` is membership of `x` in `𝔭`.

Since `n ∈ 𝓞 k ⊆ A` (the ring of integers of a number field lies in every valuation subring of an
extension, `Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top`), the value
`A.valuation (n : Ω)` is `≤ 1`, and it is not `< 1` because that would force `𝔭 ∣ n`; hence it is
`1`, which for a valuation subring says exactly `IsUnit`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-! ## The prime of `𝓞 k` below a finite place of `Ω` -/

/-- **The defining property of `Submission.NeukirchUchida.primeOf`, in the generality needed
here.**  The restriction of `A` to `k` is exactly the valuation subring cut out by the prime
`primeOf A hA`.  (The corresponding lemma `Submission.NeukirchUchida.primeOf_spec` is stated under
an `IsSepClosure k Ω` hypothesis that its *proof* uses, but its statement does not; the statement
is therefore reproduced here by unfolding the definition, which is precisely the `choose_spec` of
`exists_heightOneSpectrum_eq_valuationSubringAtPrime`.) -/
theorem primeOf_spec_general (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (Submission.NeukirchUchida.primeOf A hA) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap k Ω)) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hA)).choose_spec

/-! ## The residue characteristic versus membership in `𝔭` -/

/-- **The residue field of `𝓞 k ⧸ 𝔭` has characteristic `resCharAt 𝔭`.**

The residue field of the completion `𝓞 k ⧸ 𝔭` is `𝓞 k ⧸ 𝔭` (up to a ring equivalence,
`Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists`), and `resCharAt 𝔭` is
*defined* as the `ringChar` of the residue field of the completion.  Transporting the `CharP`
instance along the ring equivalence gives the claim. -/
theorem charP_quot_resCharAt (k : Type) [Field k] [NumberField k]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    CharP ((NumberField.RingOfIntegers k) ⧸ 𝔭.asIdeal)
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔭
  haveI : CharP (𝔭.adicCompletionIntegers k ⧸ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers k))
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) := inferInstance
  refine ⟨fun x => ?_⟩
  have hx : (x : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) =
      e (x : 𝔭.adicCompletionIntegers k ⧸ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers k)) :=
    (map_natCast e x).symm
  rw [hx, RingEquiv.map_eq_zero_iff]
  exact CharP.cast_eq_zero_iff _ _ x

/-- **`resCharAt 𝔭` divides `n` exactly when `n` vanishes at `𝔭`.**

Both sides are the assertion that the image of `n` in the residue field `𝓞 k ⧸ 𝔭` is zero:
`CharP.cast_eq_zero_iff` for the characteristic `resCharAt 𝔭` of that residue field, and
`Ideal.Quotient.eq_zero_iff_mem` for the quotient map. -/
theorem resCharAt_dvd_iff_mem_of_numberField (k : Type) [Field k] [NumberField k]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (n : ℕ) :
    NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n ↔
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal := by
  haveI := charP_quot_resCharAt k 𝔭
  have h1 : (n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) = 0 ↔
      NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n := CharP.cast_eq_zero_iff _ _ n
  have h2 : ((n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) = 0) ↔
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal := by
    rw [show (n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) =
        Ideal.Quotient.mk 𝔭.asIdeal (n : NumberField.RingOfIntegers k) from
      (map_natCast (Ideal.Quotient.mk 𝔭.asIdeal) n)]
    exact Ideal.Quotient.eq_zero_iff_mem
  exact h1.symm.trans h2

/-- **Membership in `𝔭` is the inequality `A.valuation · < 1` on `𝓞 k`.**

The restriction `A.comap (algebraMap k Ω)` of `A` to `k` is the valuation subring at `𝔭`
(`primeOf_spec_general`), so its valuation is `IsEquiv` to the `𝔭`-adic valuation of `k`; `IsEquiv`
preserves the inequality `< 1`.  Transferring `x : 𝓞 k` back and forth along
`𝓞 k → k → Ω` (using `comap_valuation_lt_one_iff` and `IsScalarTower.algebraMap_apply`) yields the
claim. -/
theorem valuation_lt_one_iff_mem_primeOf_of_numberField (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x : NumberField.RingOfIntegers k) :
    A.valuation (algebraMap (NumberField.RingOfIntegers k) Ω x) < 1 ↔
      x ∈ (Submission.NeukirchUchida.primeOf A hA).asIdeal := by
  set 𝔭 := Submission.NeukirchUchida.primeOf A hA with h𝔭
  have hspec : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
    rw [h𝔭]
    exact primeOf_spec_general k Ω A hA
  have heq : ((A.comap (algebraMap k Ω)).valuation).IsEquiv
      (IsDedekindDomain.HeightOneSpectrum.valuation k 𝔭) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation,
      hspec, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := k) 𝔭 x).symm]
  rw [← heq.lt_one_iff_lt_one]
  rw [comap_valuation_lt_one_iff A (algebraMap (NumberField.RingOfIntegers k) k x)]
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers k) k Ω x]

/-! ## The target lemma -/

theorem isUnit_natCast_of_not_dvd_resCharAt (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (n : ℕ)
    (hn : ¬ (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA)) ∣ n) :
    IsUnit (n : ↥A) := by
  -- `n ∈ 𝓞 k ⊆ A`, so `A.valuation n ≤ 1`.
  have hmemA : (n : Ω) ∈ A := by
    have h1 := Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
      (A.comap (algebraMap k Ω)) hA (n : NumberField.RingOfIntegers k)
    rw [ValuationSubring.mem_comap] at h1
    simpa [IsScalarTower.algebraMap_apply] using h1
  have hle : A.valuation (n : Ω) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff A (n : Ω)).mpr hmemA
  -- `A.valuation n < 1` would force `resCharAt 𝔭 ∣ n`.
  have hnotlt : ¬ A.valuation (n : Ω) < 1 := by
    intro hlt
    have hmem : (n : NumberField.RingOfIntegers k) ∈
        (Submission.NeukirchUchida.primeOf A hA).asIdeal :=
      (valuation_lt_one_iff_mem_primeOf_of_numberField k Ω A hA
        (n : NumberField.RingOfIntegers k)).mp (by simpa using hlt)
    exact hn ((resCharAt_dvd_iff_mem_of_numberField k
      (Submission.NeukirchUchida.primeOf A hA) n).mpr hmem)
  have hval : A.valuation (n : Ω) = 1 := le_antisymm hle (not_lt.mp hnotlt)
  exact (ValuationSubring.valuation_eq_one_iff A (n : ↥A)).mpr (by simpa using hval)

end Work.SSGRoute
