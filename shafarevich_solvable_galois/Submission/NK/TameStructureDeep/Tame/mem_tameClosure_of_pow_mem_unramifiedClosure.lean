import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure
import Submission.NK.TameStructureDeep.Tame.pow_class_unramifiedClosure_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

/-- **`κ^{ur}`-radicands of prime-to-`p` order are already tame.**

Let `κ = K_𝔭` be the `𝔭`-adic completion of a number field, `p = resCharAt 𝔭` its residue
characteristic, `π` a uniformiser of `κ` and `κ^{tr} = κ^{ur}(π^{1/n} : p ∤ n)` the maximal
tamely ramified extension, realised in the separable closure `K'` of `κ` as `tameClosure p π`.

If `y ^ n ∈ κ^{ur}` with `n > 0` prime to `p`, then already `y ∈ κ^{tr}`.

Indeed, by the Kummer computation over `κ^{ur}` (`pow_class_unramifiedClosure_pow`) the class of
`π` generates `κ^{ur×}/(κ^{ur×})^n`, so `y ^ n = π ^ j * c ^ n` for some `j : ℤ` and
`c ∈ κ^{ur}`.  For an `n`-th root `β ∈ K'` of `π` (`n` is prime to `p = char κ`, so `X ^ n - π`
is separable and splits in the separable closure), the element `ζ = y / (c * β ^ j)` then
satisfies `ζ ^ n = 1`, so `ζ ∈ κ^{ur}` (its order divides `n`, hence is prime to `p`, and
`κ^{ur} = κ(μ_{p'})`).  Thus `y = ζ * c * β ^ j` lies in
`κ^{ur} ⊔ κ⟮β⟯ ≤ κ^{tr}`. -/
theorem mem_tameClosure_of_pow_mem_unramifiedClosure {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {n : ℕ} (hn : 0 < n) (hcop : ¬ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣ n) {y : K'}
    (hy : y ^ n ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)) :
    y ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) := by
  classical
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  haveI hczK : CharZero (𝔭.adicCompletion K) := Algebra.charZero_of_charZero K _
  haveI hcz : CharZero K' := Algebra.charZero_of_charZero (𝔭.adicCompletion K) K'
  haveI hsc : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  -- the uniformiser is nonzero, hence so is its image in `K'`
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 := by
    haveI : IsDiscreteValuationRing (𝔭.adicCompletionIntegers K) := inferInstance
    intro h
    exact IsDiscreteValuationRing.not_a_field _ (by
      rw [hπ]
      exact Ideal.span_singleton_eq_bot.mpr (Subtype.coe_injective h))
  have hP0 : algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ≠ 0 :=
    fun h => hπ0 ((algebraMap (𝔭.adicCompletion K) K').injective (by simpa using h))
  -- Kummer over `κ^{ur}`: `y ^ n = π ^ j * c ^ n` with `c` unramified
  obtain ⟨j, c, hcmem, hceq⟩ :=
    NK.TameStructureDeep.Tame.pow_class_unramifiedClosure_pow 𝔭 hπ hn
      (((hp.coprime_iff_not_dvd).mpr hcop).symm) hy
  -- an `n`-th root of the uniformiser in `K'`
  haveI : NeZero (n : K') := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) n
  have hβ0 : β ≠ 0 := fun h => hP0 (by rw [← hβ, h, zero_pow hn.ne'])
  have hc0 : c ≠ 0 := by
    intro hc
    have h1 : c ^ n = 0 := by rw [hc, zero_pow hn.ne']
    rw [h1] at hceq
    exact (div_ne_zero (pow_ne_zero n hy0) (zpow_ne_zero j hP0)) hceq.symm
  have hβj : (β ^ j) ^ n = (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) ^ j := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hβ]
  -- `ζ = y / (c * β ^ j)` is a root of unity of order dividing `n`
  have hζpow : (y / (c * β ^ j)) ^ n = 1 := by
    rw [div_pow, mul_pow, hβj, hceq, div_mul_cancel₀ _ (zpow_ne_zero j hP0)]
    exact div_self (pow_ne_zero n hy0)
  have hden : c * β ^ j ≠ 0 := mul_ne_zero hc0 (zpow_ne_zero j hβ0)
  have hζmem : y / (c * β ^ j) ∈ NK.LocalAnabelian.unramifiedClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) :=
    NK.TameStructureDeep.Tame.mem_unramifiedClosure_of_pow_eq_one
      (κ := 𝔭.adicCompletion K) (K' := K') (p := NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (m := n) hcop hζpow
  -- reassemble `y`
  rw [show y = (y / (c * β ^ j)) * (c * β ^ j) from (div_mul_cancel₀ y hden).symm]
  refine mul_mem ?_ (mul_mem ?_ ?_)
  · exact NK.TameStructureDeep.Tame.unramifiedClosure_le_tameClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (π : 𝔭.adicCompletion K) hζmem
  · exact NK.TameStructureDeep.Tame.unramifiedClosure_le_tameClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (π : 𝔭.adicCompletion K) hcmem
  · refine Subfield.zpow_mem _ ?_ j
    exact SetLike.le_def.mp
      (NK.TameStructureDeep.Tame.adjoin_root_mem_tameClosure (κ := 𝔭.adicCompletion K)
        (K' := K') (p := NK.TameStructureDeep.Tame.resCharAt 𝔭) (n := n) hcop hβ)
      (IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) β)

end NK.TameStructureDeep.Tame
