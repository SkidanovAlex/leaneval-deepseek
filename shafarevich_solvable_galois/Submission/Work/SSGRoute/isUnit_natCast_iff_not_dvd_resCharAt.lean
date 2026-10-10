import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PTW.Prelude
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An integer is a unit of the valuation ring iff it is prime to the residue characteristic

Let `k` be a number field, `Ω` a field with an algebra structure over `k`, `A ≤ Ω` a valuation
subring whose restriction to `k` is a *finite* place (`A.comap (algebraMap k Ω) ≠ ⊤`, see
`SSGRoute.IsFinPlace`), and `n : ℕ`.  Writing `𝔭 = Submission.NeukirchUchida.primeOf A hA` for the
prime of `𝓞 k` below `A`, and `resCharAt 𝔭` for the residue characteristic of the completion at `𝔭`,
we prove

  `IsUnit (n : ↥A) ↔ ¬ resCharAt 𝔭 ∣ n`.

The two ingredients are the `p`-adic arithmetic of the place:

* `resCharAt_dvd_iff_mem` — `resCharAt 𝔭 ∣ n` iff `n` lies in the prime `𝔭 ⊆ 𝓞 k`;
* `resCharAt_valuation_lt_one_iff_mem` — `A.valuation x < 1` iff `x ∈ 𝔭`, for `x ∈ 𝓞 k`.

Since `n ∈ 𝓞 k ⊆ A` the value `A.valuation n` is `≤ 1`, so both sides of the equivalence are just
the statement `A.valuation (n : Ω) = 1` (equivalently `n mod 𝔪_A ≠ 0`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-! ## The prime of `𝓞 k` below a finite place of `Ω` -/

/-- **The defining property of `Submission.NeukirchUchida.primeOf`.** The restriction of `A` to `k`
is exactly the valuation subring cut out by the prime `primeOf A hA`. -/
theorem resCharAt_primeOf_spec (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (Submission.NeukirchUchida.primeOf A hA) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap k Ω)) hA
    (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hA)).choose_spec

/-! ## The residue characteristic versus membership in `𝔭` -/

/-- **The residue field of `𝓞 k ⧸ 𝔭` has characteristic `resCharAt 𝔭`.** -/
theorem resCharAt_charP (k : Type) [Field k] [NumberField k]
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

/-- **`resCharAt 𝔭` divides `n` exactly when `n` vanishes at `𝔭`.** -/
theorem resCharAt_dvd_iff_mem (k : Type) [Field k] [NumberField k]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (n : ℕ) :
    NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n ↔
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal := by
  haveI := resCharAt_charP k 𝔭
  have h1 : (n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) = 0 ↔
      NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ n := CharP.cast_eq_zero_iff _ _ n
  have h2 : ((n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) = 0) ↔
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal := by
    rw [show (n : NumberField.RingOfIntegers k ⧸ 𝔭.asIdeal) =
        Ideal.Quotient.mk 𝔭.asIdeal (n : NumberField.RingOfIntegers k) from
      (map_natCast (Ideal.Quotient.mk 𝔭.asIdeal) n)]
    exact Ideal.Quotient.eq_zero_iff_mem
  exact h1.symm.trans h2

/-- **Membership in `𝔭` is the inequality `A.valuation · < 1`.** -/
theorem resCharAt_valuation_lt_one_iff_mem (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x : NumberField.RingOfIntegers k) :
    A.valuation (algebraMap (NumberField.RingOfIntegers k) Ω x) < 1 ↔
      x ∈ (Submission.NeukirchUchida.primeOf A hA).asIdeal := by
  set 𝔭 := Submission.NeukirchUchida.primeOf A hA with h𝔭
  have hspec : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
    rw [h𝔭]
    exact resCharAt_primeOf_spec k Ω A hA
  have heq : ((A.comap (algebraMap k Ω)).valuation).IsEquiv
      (IsDedekindDomain.HeightOneSpectrum.valuation k 𝔭) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation,
      hspec, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := k) 𝔭 x).symm]
  rw [← heq.lt_one_iff_lt_one]
  rw [comap_valuation_lt_one_iff A (algebraMap (NumberField.RingOfIntegers k) k x)]
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers k) k Ω x]

/-! ## The equivalence -/

/-- **An integer is a unit of the valuation ring `↥A` iff it is not divisible by the residue
characteristic of the place.** -/
theorem isUnit_natCast_iff_not_dvd_resCharAt (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (n : ℕ) :
    IsUnit (n : ↥A) ↔
      ¬ (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA)) ∣ n := by
  -- `n ∈ 𝓞 k ⊆ A`, so `A.valuation n ≤ 1`.
  have hmemA : (n : Ω) ∈ A := by
    have h1 := Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
      (A.comap (algebraMap k Ω)) hA (n : NumberField.RingOfIntegers k)
    rw [ValuationSubring.mem_comap] at h1
    simpa [IsScalarTower.algebraMap_apply] using h1
  have hle : A.valuation (n : Ω) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff A (n : Ω)).mpr hmemA
  -- `A.valuation n < 1` is equivalent to `resCharAt 𝔭 ∣ n`.
  have hkey : A.valuation (n : Ω) < 1 ↔
      NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA) ∣ n := by
    have h1 : A.valuation (n : Ω) < 1 ↔
        (n : NumberField.RingOfIntegers k) ∈
          (Submission.NeukirchUchida.primeOf A hA).asIdeal :=
      (by simpa using
        resCharAt_valuation_lt_one_iff_mem k Ω A hA (n : NumberField.RingOfIntegers k))
    exact h1.trans (resCharAt_dvd_iff_mem k (Submission.NeukirchUchida.primeOf A hA) n).symm
  constructor
  · -- a unit has valuation `1`, hence not `< 1`
    intro hunit hdvd
    have hval : A.valuation (n : Ω) = 1 := by
      have h1 := (ValuationSubring.valuation_eq_one_iff A (n : ↥A)).mp hunit
      simpa using h1
    have hlt : A.valuation (n : Ω) < 1 := hkey.mpr hdvd
    rw [hval] at hlt
    exact lt_irrefl 1 hlt
  · -- if `resCharAt 𝔭 ∤ n` then `A.valuation n` is `≤ 1` but not `< 1`, so equals `1`
    intro hn
    have hnotlt : ¬ A.valuation (n : Ω) < 1 := fun hlt => hn (hkey.mp hlt)
    have hval : A.valuation (n : Ω) = 1 := le_antisymm hle (not_lt.mp hnotlt)
    exact (ValuationSubring.valuation_eq_one_iff A (n : ↥A)).mpr (by simpa using hval)

end Work.SSGRoute
