import Mathlib
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.ZDataTwo.not_exists_sq_val_of_odd_count
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

/-- **Odd count at an escape place from the normalisation condition (1)** (the `p = 2` lane).

If `b ∈ ↥Kˣ` is *normalised at the finite place `A`*, i.e. there is a uniformiser `x` of the prime
`𝔭` of `↥K` below `A` whose Kummer cochain matches that of `b` on the inertia of `A`
(`hnorm`, Schmidt--Wingberg's condition (1) at `p = 2`, where the minus sign is invisible in
`ZMod 2`), then the `𝔭`-adic count of `b` is odd.

The argument is the *tame-free* version of the count-transport of the crossed two-place identity:

* `hnorm` gives `χ_b = -χ_x` on the inertia of `A`, hence `χ_{b·x⁻¹} = χ_b - χ_x = 0` there
  (`chi_mul_inv_kills_inertia`);
* the contrapositive of the tame-free Kummer criterion
  `kummerCochar_ne_zero_of_val_not_sq_noTameness` then produces `d` with
  `v_A(b·x⁻¹) = v_A(d)²`, i.e. `v_A(b·x⁻¹)` is a square — this replaces the tame step
  `kills_inertia_iff_even_valuation` of the sibling node (`evenCountOfKillsInertia`), and is the
  reason no tameness hypothesis (`A ∤ 2`) appears here;
* `not_exists_sq_val_of_odd_count` turns this square witness into the *evenness* of the `𝔭`-count of
  `b·x⁻¹` (`even_count_mul_inv_of_sq_val`);
* the uniformiser `x` has `𝔭`-count `1` (`odd_count_of_maximal_lt_one`, from the maximality clause
  of `hnorm`), and `count_𝔭 b = count_𝔭 (b·x⁻¹) + count_𝔭 x` is even `+` odd `=` odd. -/
theorem oddCountAtEscape {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hnorm : ∃ x : (↥K)ˣ,
      A.valuation (algebraMap ↥K Ω (x : ↥K)) < 1 ∧
      (∀ y : ↥K, A.valuation (algebraMap ↥K Ω y) < 1 →
        A.valuation (algebraMap ↥K Ω y) ≤ A.valuation (algebraMap ↥K Ω (x : ↥K))) ∧
      (∀ τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ
          = - Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ x τ)) :
    Odd (FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K))) := by
  classical
  have hSepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  obtain ⟨x, hxlt, hxmax, hchar⟩ := hnorm
  -- the prime `𝔭` of `↥K` below `A`
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA
  have hspec : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA
  have hAne : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
    Work.SSGRoute.ZDataMup.OddForm.oddFinPlace (K := K) hA
  -- the trace valuation of `A` on `↥K` and the `𝔭`-adic valuation are equivalent
  have heq : (A.valuation.comap (algebraMap ↥K Ω)).IsEquiv (𝔭.valuation ↥K) := by
    rw [Valuation.isEquiv_iff_valuationSubring,
      Work.SSGRoute.H9.CV2.valuationSubring_comap_algebraMap A, hspec,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  -- step 1: `χ_{b·x⁻¹}` kills the inertia of `A`
  have hkillZ : ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (b * x⁻¹) τ = 0 :=
    Work.SSGRoute.H9.CV2.chi_mul_inv_kills_inertia (K := K) ζ hζ hζK b x A hchar
  have hkill : ∀ τ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A τ →
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b * x⁻¹) τ = 0 := by
    intro τ hτK hτI
    rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two
      (K := K) ζ hζ hζK (b * x⁻¹) τ]
    exact hkillZ τ hτK hτI
  -- step 2: the `A`-value of `b·x⁻¹` is a square (tame-free, by contraposition)
  have hsq : ∃ d : (↥K)ˣ, A.valuation (algebraMap ↥K Ω ((b * x⁻¹ : (↥K)ˣ) : ↥K)) =
      (A.valuation (algebraMap ↥K Ω (d : ↥K))) ^ 2 := by
    by_contra hnsq
    obtain ⟨σ, hσK, hσI, hχ⟩ :=
      Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq_noTameness
        k Ω K ζ hζ hζK (b * x⁻¹) A hA hnsq
    exact hχ (hkill σ hσK hσI)
  -- step 3: hence the `𝔭`-count of `b·x⁻¹` is even
  have heven : Even (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        ((b * x⁻¹ : (↥K)ˣ) : ↥K))) :=
    Work.SSGRoute.H9.CV2.even_count_mul_inv_of_sq_val (K := K) b x A hA hAne 𝔭 hspec hsq
  -- step 4: `x` is a uniformiser at `𝔭`, so its `𝔭`-count is odd
  have hxlt' : (𝔭.valuation ↥K) (x : ↥K) < 1 :=
    (Valuation.IsEquiv.lt_one_iff_lt_one heq).mp (by simpa using hxlt)
  have hxmax' : ∀ y : ↥K, (𝔭.valuation ↥K) y < 1 →
      (𝔭.valuation ↥K) y ≤ (𝔭.valuation ↥K) (x : ↥K) := by
    intro y hy
    rw [← Work.SSGRoute.H9.CV2.valuation_isEquiv_le_iff_le heq]
    exact hxmax y ((Valuation.IsEquiv.lt_one_iff_lt_one heq).mpr hy)
  have hoddx : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (x : ↥K))) :=
    Work.SSGRoute.H9.CV2.odd_count_of_maximal_lt_one (K := ↥K) x 𝔭 hxlt' hxmax'
  -- step 5: even + odd = odd
  have hodd : Odd (FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (b : ↥K))) :=
    Work.SSGRoute.H9.CV2.odd_count_of_even_count_mul_inv (K := ↥K) 𝔭 b x heven hoddx
  exact hodd

end Work.SSGRoute.NodeS37
