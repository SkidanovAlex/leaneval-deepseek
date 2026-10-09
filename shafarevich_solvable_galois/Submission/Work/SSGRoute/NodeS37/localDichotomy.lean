import Mathlib
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.ZConstruction.LocalSquares
import Submission.Work.SSGRoute.ges_readoff
import Submission.Work.SSGRoute.ZDataMup.mupOddAux
import Submission.Commons.RingTheory.Valuation.valuation_le_iff_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local dichotomy of the p. 16 computation

The p. 16 computation of Schmidt--Wingberg replaces the class `z` by the anti-invariant element
`X = z - ρz` at the sibling place `A`, and the two local steps that make this legal are

* at a place where `z/X ≡ 1 (mod A)` and `2` is a unit (`A ∤ 2`): `z/X` is a local **square**
  (`ZConstruction.LocalSquares.exists_unit_sq_one_add`), so `χ_{z/X}` kills the local group;
* at a `ρ`-fixed place `P | X` with `P ∤ 2`: the invariant element `a = (z + ρz)/2` is a local
  **square** at `P`, so `χ_a` kills the local group.

Both reduce to the same dictionary statement — a class `β` whose image in the completion `↥K_𝔭` is a
square kills the local group `decomp k A ⊓ K.fixingSubgroup`:

* `NodeS37.killsLocalGroup_of_localSquare` — the dictionary half;
* `NodeS37.killsLocalGroup_of_oneUnit` — the `1`-unit case, obtained by converting the
  `A.valuation`-hypotheses into a square in the `𝔭`-adic completion
  (`exists_unit_sq_one_add`), through the bridge
  `NodeS37.adic_valuation_lt_one_iff` (`A.valuation` at the place `A` versus the canonical
  valuation of the completion's valuation ring).

The chain is the local Kummer dictionary `ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass`
together with `Work.SSGRoute.localPowClass_eq_one_of_unit_component`.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

/-- **A class whose completion image is a square kills the local group.**  If the image of `β` in the
`𝔭`-adic completion of `↥K` is a square, then the level-`↥K` Kummer cochain `χ_β` vanishes on the
local group `decomp k A ⊓ K.fixingSubgroup` of the place `A` below `𝔭`. -/
theorem killsLocalGroup_of_localSquare {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (β : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hsq : ∃ c : (𝔭.adicCompletion ↥K)ˣ,
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom β = c ^ 2) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0 := by
  refine (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass (p := 2)
    K ζ hζK hζ β A hA 𝔭 h𝔭).mpr ?_
  obtain ⟨c, hc⟩ := hsq
  refine Work.SSGRoute.localPowClass_eq_one_of_unit_component (K := ↥K) (p := 2) Nat.prime_two
    (𝔭 := 𝔭) (γ := β) (e := (c⁻¹) ^ 2) ?_ ?_
  · exact ⟨c⁻¹, rfl⟩
  · rw [hc]
    group

/-- **The `𝔭`-adic value of the image of an element of `↥K` in the completion.** -/
theorem valued_adicCompletion_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) (z : ↥K) :
    Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) z) =
      IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 z := by
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (NumberField.RingOfIntegers ↥K)
    ↥K 𝔭]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' 𝔭 z

/-- **The integers of the completion pull back to the valuation ring of `𝔭`.** -/
theorem comap_adicCompletionIntegers {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    (Valued.v (R := 𝔭.adicCompletion ↥K)).valuationSubring.comap
        (algebraMap ↥K (𝔭.adicCompletion ↥K)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  ext x
  change Valued.v (algebraMap ↥K (𝔭.adicCompletion ↥K) x) ≤ 1 ↔
    IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔭 x ≤ 1
  rw [valued_adicCompletion_eq]

/-- **The bridge between the valuation of a place `A` and the canonical valuation of the completion
at the prime `𝔭` below it.**  For `x ≠ 0`,
`A.valuation (algebraMap x) < 1` iff the canonical valuation of `𝔭.adicCompletionIntegers ↥K`
at the image of `x` is `< 1`.

The proof applies `Commons.RingTheory.Valuation.valuation_le_iff_comap_eq` twice (at `1` and at `x`,
which turns the `≤`-equivalence into a `< 1`-equivalence by `Iff.not` and `not_le`): once for the
place `A` (whose comap is the valuation ring of `𝔭`) and once for the completion's valuation ring. -/
theorem adic_valuation_lt_one_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : ↥K) (hx : x ≠ 0) :
    A.valuation (algebraMap ↥K Ω x) < 1 ↔
      (Valued.v (R := 𝔭.adicCompletion ↥K)).valuationSubring.valuation
        (algebraMap ↥K (𝔭.adicCompletion ↥K) x) < 1 := by
  set C : ValuationSubring ↥K :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 with hCdef
  have h1 : A.valuation (algebraMap ↥K Ω x) < 1 ↔ C.valuation x < 1 := by
    have h := Commons.RingTheory.Valuation.valuation_le_iff_comap_eq C A h𝔭
      (x := (1 : ↥K)) (c := x) hx
    have h1a : A.valuation (algebraMap ↥K Ω (1 : ↥K)) = 1 := by
      rw [map_one (algebraMap ↥K Ω)]; exact map_one _
    have h1b : C.valuation (1 : ↥K) = 1 := map_one _
    rw [h1a, h1b] at h
    have := h.not
    rwa [not_le, not_le] at this
  have h2 : (Valued.v (R := 𝔭.adicCompletion ↥K)).valuationSubring.valuation
        (algebraMap ↥K (𝔭.adicCompletion ↥K) x) < 1 ↔ C.valuation x < 1 := by
    have h := Commons.RingTheory.Valuation.valuation_le_iff_comap_eq C
      (Valued.v (R := 𝔭.adicCompletion ↥K)).valuationSubring
      (by rw [hCdef]; exact comap_adicCompletionIntegers 𝔭)
      (x := (1 : ↥K)) (c := x) hx
    have h2a : (Valued.v (R := 𝔭.adicCompletion ↥K)).valuationSubring.valuation
        (algebraMap ↥K (𝔭.adicCompletion ↥K) (1 : ↥K)) = 1 := by
      rw [map_one (algebraMap ↥K (𝔭.adicCompletion ↥K))]; exact map_one _
    have h2b : C.valuation (1 : ↥K) = 1 := map_one _
    rw [h2a, h2b] at h
    have := h.not
    rwa [not_le, not_le] at this
  exact h1.trans h2.symm

/-- **A `1`-unit at a place where `2` is a unit kills the local group.**  If `y` is a unit at the
place `A` whose image in `↥K_𝔭` is `≡ 1` modulo the maximal ideal, and `2` is a unit there, then the
image of `y` is a square in the completion (`exists_unit_sq_one_add`), so `χ_y` kills the local group
of `A`.  (Only `ht` is used; `hunit` is kept because it is the hypothesis shape of
`TwoRec.killsLocalGroup_of_one_unit`.) -/
theorem killsLocalGroup_of_oneUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (y : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (hunit : A.valuation (algebraMap ↥K Ω (y : ↥K)) = 1)
    (ht : A.valuation (algebraMap ↥K Ω ((y : ↥K) - 1)) < 1) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ y u = 0 := by
  refine killsLocalGroup_of_localSquare (K := K) ζ hζ hζK y A hA 𝔭 h𝔭 ?_
  by_cases hy1 : (y : ↥K) = 1
  · exact ⟨1, by rw [show y = 1 from Units.ext hy1, map_one, one_pow]⟩
  set W : ValuationSubring (𝔭.adicCompletion ↥K) := 𝔭.adicCompletionIntegers ↥K with hWdef
  -- the value of the image of `y - 1` is `< 1` for the canonical valuation of the integers
  have hne : (y : ↥K) - 1 ≠ 0 := fun h => hy1 (sub_eq_zero.mp h)
  have hlt : W.valuation (algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1)) < 1 :=
    (adic_valuation_lt_one_iff A 𝔭 h𝔭 ((y : ↥K) - 1) hne).mp ht
  -- `2` is a unit of the integers of the completion
  have h2unit : IsUnit (2 : ↥W) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem2
    have hlt2 : W.valuation ((2 : ↥W) : 𝔭.adicCompletion ↥K) < 1 :=
      (ValuationSubring.valuation_lt_one_iff W (2 : ↥W)).mp hmem2
    have hcoe : ((2 : ↥W) : 𝔭.adicCompletion ↥K) =
        algebraMap ↥K (𝔭.adicCompletion ↥K) (2 : ↥K) := by
      rw [map_ofNat]
      rfl
    rw [hcoe] at hlt2
    exact h2 ((adic_valuation_lt_one_iff A 𝔭 h𝔭 (2 : ↥K) two_ne_zero).mpr hlt2)
  -- the element `t = localImage y - 1` of the integers of the completion
  have hmem : algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1) ∈ W :=
    (ValuationSubring.valuation_le_one_iff W
      (algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1))).mp (le_of_lt hlt)
  have ht_mem : (⟨algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1), hmem⟩ : ↥W) ∈
      IsLocalRing.maximalIdeal ↥W :=
    (ValuationSubring.valuation_lt_one_iff W _).mpr hlt
  obtain ⟨s, hs⟩ := Work.SSGRoute.ZConstruction.exists_unit_sq_one_add (k := ↥K) 𝔭 h2unit
    ⟨algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1), hmem⟩ ht_mem
  have hcomp : algebraMap ↥W (𝔭.adicCompletion ↥K)
        (1 + ⟨algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1), hmem⟩)
      = algebraMap ↥K (𝔭.adicCompletion ↥K) (y : ↥K) := by
    rw [map_add, map_one]
    show (1 : 𝔭.adicCompletion ↥K) +
        algebraMap ↥K (𝔭.adicCompletion ↥K) ((y : ↥K) - 1) =
      algebraMap ↥K (𝔭.adicCompletion ↥K) (y : ↥K)
    rw [map_sub, map_one]
    ring
  have hfinal : (Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)).toMonoidHom y :
      𝔭.adicCompletion ↥K) =
      (s : 𝔭.adicCompletion ↥K) * (s : 𝔭.adicCompletion ↥K) := by
    rw [Units.coe_map]
    change ((algebraMap ↥K (𝔭.adicCompletion ↥K)) (y : ↥K)) =
      (s : 𝔭.adicCompletion ↥K) * (s : 𝔭.adicCompletion ↥K)
    rw [← hcomp, ← hs]
  refine ⟨s, Units.ext ?_⟩
  rw [hfinal, Units.val_pow_eq_pow_val, pow_two]

end Work.SSGRoute.NodeS37
