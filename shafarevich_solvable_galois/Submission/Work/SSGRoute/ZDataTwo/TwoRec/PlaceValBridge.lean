import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.AdicBridge
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place-valuation bridge (`Ω`-place `A` vs. the prime `𝔭` of `↥K`)

The local inputs of the `p = 2` node lane (`SSGRoute/ZDataTwo/TwoRec/`) are stated at a place `A` of
`Ω` (with `A.valuation` the valuation of the valuation subring `A ≤ Ω`), while the local Kummer
dictionary (`ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass`) works with the `𝔭`-adic
valuation of the completion `𝔭.adicCompletion ↥K` of the number field `↥K` below `A`.

This file provides the translation, in the form of the elementary facts about valuation subrings
which are independent of the number-theoretic setting, and then the two number-theoretic instances:

* `valuation_le_one_iff_of_eq`, `valuation_lt_one_iff_of_eq` — equal valuation subrings cut out the
  same `≤ 1` and `< 1` predicates (through `ValuationSubring.mem_nonunits_iff_or`);
* `comap_valuation_le_one`, `comap_valuation_lt_one` — the valuation of `A.comap f` is
  `A.valuation ∘ f`;
* `valuationSubring_valuation_le_one`, `valuationSubring_valuation_lt_one` — a valuation and the
  valuation of its valuation subring agree on `≤ 1` and `< 1`;
* `place_valuation_le_one_iff`, `place_valuation_lt_one_iff` — **the bridge**: if `A` lies over the
  prime `𝔭` of `↥K` (i.e. `A.comap (algebraMap ↥K Ω) = valuationSubringAtPrime ↥K 𝔭`), then
  `A.valuation (algebraMap ↥K Ω x) < 1 ↔ 𝔭.valuation ↥K x < 1`;
* `adicCompletion_valuation_lt_one_iff` — the same with `Valued.v` on the completion
  (`IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`).
-/

namespace Work.SSGRoute.ZDataTwo.TwoRec

/-! ## Elementary facts about valuation subrings -/

/-- Equal valuation subrings cut out the same `≤ 1` predicate. -/
theorem valuation_le_one_iff_of_eq {K : Type*} [Field K] {V W : ValuationSubring K} (h : V = W)
    (x : K) : V.valuation x ≤ 1 ↔ W.valuation x ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, h]

/-- Equal valuation subrings cut out the same `< 1` predicate. -/
theorem valuation_lt_one_iff_of_eq {K : Type*} [Field K] {V W : ValuationSubring K} (h : V = W)
    (x : K) : V.valuation x < 1 ↔ W.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff (A := V), ValuationSubring.mem_nonunits_iff_or,
    ← ValuationSubring.mem_nonunits_iff (A := W), ValuationSubring.mem_nonunits_iff_or, h]

/-- The valuation of a pullback of a valuation subring is the composite with the pullback map. -/
theorem comap_valuation_le_one {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A : ValuationSubring L) (x : K) : (A.comap f).valuation x ≤ 1 ↔ A.valuation (f x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap,
    ValuationSubring.valuation_le_one_iff]

/-- The valuation of a pullback of a valuation subring is the composite with the pullback map. -/
theorem comap_valuation_lt_one {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (A : ValuationSubring L) (x : K) : (A.comap f).valuation x < 1 ↔ A.valuation (f x) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff (A := A.comap f), ValuationSubring.mem_nonunits_iff_or,
    ← ValuationSubring.mem_nonunits_iff (A := A), ValuationSubring.mem_nonunits_iff_or]
  constructor
  · rintro (h | h)
    · left; rw [h, map_zero]
    · right
      rw [show x⁻¹ ∉ A.comap f ↔ f x⁻¹ ∉ A from not_congr ValuationSubring.mem_comap,
        map_inv₀] at h
      exact h
  · rintro (h | h)
    · left; exact f.injective (by rw [h, map_zero])
    · right
      rw [show x⁻¹ ∉ A.comap f ↔ f x⁻¹ ∉ A from not_congr ValuationSubring.mem_comap, map_inv₀]
      exact h

/-- A valuation and the valuation of its valuation subring agree on `≤ 1`. -/
theorem valuationSubring_valuation_le_one {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (x : K) :
    w.valuationSubring.valuation x ≤ 1 ↔ w x ≤ 1 :=
  ((Valuation.isEquiv_valuation_valuationSubring w).le_one_iff_le_one).symm

/-- A valuation and the valuation of its valuation subring agree on `< 1`. -/
theorem valuationSubring_valuation_lt_one {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (x : K) :
    w.valuationSubring.valuation x < 1 ↔ w x < 1 :=
  ((Valuation.isEquiv_valuation_valuationSubring w).lt_one_iff_lt_one).symm

/-! ## The place bridge -/

/-- **The place-valuation bridge.**  If the place `A` of `Ω` restricts to the prime `𝔭` of `↥K`,
the `≤ 1` (integrality) conditions of the two valuations agree on `↥K`. -/
theorem place_valuation_le_one_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (x : ↥K) :
    A.valuation (algebraMap ↥K Ω x) ≤ 1 ↔ 𝔭.valuation ↥K x ≤ 1 := by
  have hB : A.comap (algebraMap ↥K Ω) = (𝔭.valuation ↥K).valuationSubring := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (comap_valuation_le_one (algebraMap ↥K Ω) A x).symm.trans
    ((valuation_le_one_iff_of_eq hB x).trans
      (valuationSubring_valuation_le_one (𝔭.valuation ↥K) x))

/-- **The place-valuation bridge** (strict form).  If the place `A` of `Ω` restricts to the prime
`𝔭` of `↥K`, the `A`-adic and the `𝔭`-adic valuation of an element of `↥K` are `< 1` together. -/
theorem place_valuation_lt_one_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (x : ↥K) :
    A.valuation (algebraMap ↥K Ω x) < 1 ↔ 𝔭.valuation ↥K x < 1 := by
  have hB : A.comap (algebraMap ↥K Ω) = (𝔭.valuation ↥K).valuationSubring := by
    rw [h𝔭, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (comap_valuation_lt_one (algebraMap ↥K Ω) A x).symm.trans
    ((valuation_lt_one_iff_of_eq hB x).trans
      (valuationSubring_valuation_lt_one (𝔭.valuation ↥K) x))

/-- **The place-valuation bridge in the completion**: the `𝔭`-adic valuation of the completion of
`↥K` and the valuation of the place `A` of `Ω` agree on `< 1`. -/
theorem adicCompletion_valuation_lt_one_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (x : ↥K) :
    Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) x) < 1 ↔
      A.valuation (algebraMap ↥K Ω x) < 1 := by
  rw [show Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) x) = 𝔭.valuation ↥K x from
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' 𝔭 x]
  exact (place_valuation_lt_one_iff A 𝔭 h𝔭 x).symm

/-! ## The local arithmetic at the completion of `↥K`

The two local facts consumed by `killsLocalGroup_of_one_unit`: `2` is a unit of the ring of integers
of the completion when the place does not divide `2`, and a `1`-unit is a square in the completion
(Hensel, `ZConstruction.LocalSquares.exists_unit_sq_one_add`). -/

/-- **`2` is a unit at a place not dividing `2`.** -/
theorem isUnit_two_adicCompletionIntegers_of_not_lt_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : ¬ 𝔭.valuation K (2 : K) < 1) :
    IsUnit (2 : 𝔭.adicCompletionIntegers K) := by
  have hnm : (2 : 𝔭.adicCompletionIntegers K) ∉
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    intro hmem
    rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K)) 2]
      at hmem
    rw [Work.SSGRoute.ZDataTwo.algebraMap_mem_maximalIdeal_iff] at hmem
    refine h2 ?_
    have h2' : (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔭)
        (((2 : NumberField.RingOfIntegers K)) : K) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭
        (2 : NumberField.RingOfIntegers K)).mpr hmem
    rw [show (((2 : NumberField.RingOfIntegers K)) : K) =
        algebraMap (NumberField.RingOfIntegers K) K 2 from rfl] at h2'
    rwa [map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2] at h2'
  by_contra hnu
  exact hnm (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu)

/-- **A `1`-unit at a place where `2` is a unit is a square in the completion.**  If the image of
`y - 1` in the `𝔭`-adic completion of a number field lies in the maximal ideal of the ring of
integers, then `y` is a square in the completion (Hensel's lemma for `X² - (1 + t)`, the residue `1`
being a square and `2` a unit of the residue field). -/
theorem exists_sq_of_valued_sub_one_lt_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers K)) (y : Kˣ)
    (hz : Valued.v (algebraMap K (𝔭.adicCompletion K) ((y : K) - 1)) < 1) :
    ∃ c : (𝔭.adicCompletion K)ˣ,
      (c : 𝔭.adicCompletion K) * (c : 𝔭.adicCompletion K) =
        algebraMap K (𝔭.adicCompletion K) (y : K) := by
  have hzint : algebraMap K (𝔭.adicCompletion K) ((y : K) - 1) ∈
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K 𝔭 := by
    show Valued.v (algebraMap K (𝔭.adicCompletion K) ((y : K) - 1)) ≤ 1
    exact le_of_lt hz
  have ht : (⟨algebraMap K (𝔭.adicCompletion K) ((y : K) - 1), hzint⟩ :
        𝔭.adicCompletionIntegers K) ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) :=
    (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ))))).mpr hz
  obtain ⟨s, hs⟩ := Work.SSGRoute.ZConstruction.exists_unit_sq_one_add (k := K) 𝔭 h2
    ⟨algebraMap K (𝔭.adicCompletion K) ((y : K) - 1), hzint⟩ ht
  refine ⟨s, ?_⟩
  rw [hs]
  have h1 : (1 : 𝔭.adicCompletion K) + algebraMap K (𝔭.adicCompletion K) ((y : K) - 1) =
      algebraMap K (𝔭.adicCompletion K) (y : K) := by
    rw [← map_one (algebraMap K (𝔭.adicCompletion K)), ← map_add]
    congr 1
    ring
  rw [map_add, map_one]
  exact h1

/-- **A `1`-unit at a place where `2` is a unit is a local square, in units form.**  The unit-group
form of `exists_sq_of_valued_sub_one_lt_one`, which is what `localPowClass = 1` consumes. -/
theorem exists_sq_unitsMap_of_valued_sub_one_lt_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : IsUnit (2 : 𝔭.adicCompletionIntegers K)) (y : Kˣ)
    (hz : Valued.v (algebraMap K (𝔭.adicCompletion K) ((y : K) - 1)) < 1) :
    ∃ c : (𝔭.adicCompletion K)ˣ,
      c ^ 2 = Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom y := by
  obtain ⟨c, hc⟩ := exists_sq_of_valued_sub_one_lt_one 𝔭 h2 y hz
  refine ⟨c, Units.ext ?_⟩
  rw [pow_two, Units.coe_map]
  exact hc

end Work.SSGRoute.ZDataTwo.TwoRec
