import Mathlib.Tactic.Have
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
import Submission.NK.TameStructureDeep.Degree.dvd_pow_orderOf_sub_one
import Submission.NK.TameStructureDeep.Degree.exists_isPrimitiveRoot_adicCompletion_of_dvd
import Submission.NK.TameStructureDeep.Degree.unramifiedExtensionGeneral
import Submission.NK.TameStructureDeep.Tame.Defs

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.TameStructureDeep.Tame

/-! ## Auxiliary lemmas -/

/-- **The valuation of a uniformiser of the completion.**  If `π` generates the maximal ideal of
`𝔭.adicCompletionIntegers K`, then `π` is a uniformiser for the `𝔭`-adic valuation on the
completion, i.e. its valuation is `exp (-1)`. -/
lemma val_eq_exp_neg_one_of_isUniformizerAt {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : 𝔭.adicCompletionIntegers K} (hπ : IsUniformizerAt 𝔭 π) :
    Valued.v (π : 𝔭.adicCompletion K) = WithZero.exp (-1) := by
  have hsurj : Function.Surjective (Valued.v : Valuation (𝔭.adicCompletion K) ℤᵐ⁰) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      (R := NumberField.RingOfIntegers K) K 𝔭
  have hv : (Valued.v : Valuation (𝔭.adicCompletion K) ℤᵐ⁰).IsUniformizer
      ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (Valued.v : Valuation (𝔭.adicCompletion K) ℤᵐ⁰)) hπ
  rw [Valuation.IsUniformizer.val hv]
  have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := (Valued.v : Valuation (𝔭.adicCompletion K) ℤᵐ⁰)) hsurj
  simpa using congrArg (fun u : (ℤᵐ⁰)ˣ => (u : ℤᵐ⁰)) h

/-- **An element of valuation `exp (-1)` has no `n`-th root, for `n ≥ 2`.** -/
lemma pow_ne_of_val_eq_exp_neg_one {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    {x : F} (hx : v x = WithZero.exp (-1)) {n : ℕ} (hn : 2 ≤ n) (y : F) :
    y ^ n ≠ x := by
  intro hy
  have hvy : v y ≠ 0 := by
    intro h0
    have h1 : v x = 0 := by rw [← hy, map_pow, h0, zero_pow (by omega : n ≠ 0)]
    rw [hx] at h1
    exact WithZero.exp_ne_zero h1
  have hlog : WithZero.log (v y ^ n) = WithZero.log (v x) := by rw [← map_pow, ← hy]
  rw [WithZero.log_pow, hx, WithZero.log_exp] at hlog
  have hmul : ((n : ℤ)) * WithZero.log (v y) = -1 := by simpa using hlog
  have hdvd : ((n : ℤ)) ∣ (1 : ℤ) := by
    refine dvd_neg.mp ?_
    exact ⟨WithZero.log (v y), hmul.symm⟩
  have hle : (n : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
  omega

/-! ## The theorem -/

/-- **A uniformiser of the `𝔭`-adic field has no `n`-th root in the cyclotomic extension
`K_𝔭(ζ_m)`, for `n ≥ 2` and `m` prime to the residue characteristic.**

The point is that `K_𝔭(ζ_m)` is *unramified* over `K_𝔭`: a uniformiser keeps valuation `exp (-1)`,
while an `n`-th root would have valuation `exp (-1 / n)`.

The unramified model of `K_𝔭(ζ_m)` used here is the `𝔮`-adic completion of a global number field
`K₂ ⊇ K` attached to `𝔭` by `exists_unramified_extension_of_inertiaDeg'` with inertia degree
`d = ord_m(#𝔽_𝔭)`: it is unramified of degree `d` over `K_𝔭`, so `π` still has valuation
`exp (-1)` there, and — its residue field having `q ^ d` elements — it contains a primitive `m`-th
root of unity, whence the `K_𝔭`-algebra isomorphism with the cyclotomic extension inside `K'`. -/
theorem no_pow_root_adjoin_primitiveRoot {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {m n : ℕ} (hn : 2 ≤ n) (hm : ¬ NK.TameStructureDeep.Tame.resCharAt 𝔭 ∣ m)
    {ζ : K'} (hζ : IsPrimitiveRoot ζ m)
    (α : ↥(IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K'))) :
    (α : K') ^ n ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
  classical
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
  haveI hNeZero : NeZero m := ⟨hm0⟩
  -- the residue cardinality `q` is coprime to `m`
  have hcop : Nat.Coprime (NK.LocalStructure.residueCard K 𝔭) m := by
    have hpprime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
    have hcharP := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
    obtain ⟨f, _hfpos, hqf⟩ :=
      NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hpprime hcharP
    rw [hqf]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hpprime).mpr hm)
  -- `d = ord_m(q)` is positive and `m ∣ q ^ d - 1`
  obtain ⟨hdvd, hdpos⟩ :=
    NK.TameStructureDeep.Degree.dvd_pow_orderOf_sub_one
      (q := NK.LocalStructure.residueCard K 𝔭) hm0 hcop
  -- the global number field `K₂` with a prime `𝔮` over `𝔭` that is unramified of degree `d`
  obtain ⟨K₂, hK₂F, hK₂NF, hK₂A, 𝔮, hLies, he, hf, hfr⟩ :=
    NK.TameStructureDeep.Degree.exists_unramified_extension_of_inertiaDeg' (L := K) 𝔭
      (orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod m)) hdpos
  letI : Algebra K K₂ := hK₂A
  haveI hFDK : FiniteDimensional K K₂ :=
    FiniteDimensional.of_finrank_pos (by rw [hfr]; exact hdpos)
  -- the local field `F = (K₂)_𝔮` over `K_𝔭`
  letI hAlgF : Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hLies)
  have hfin : Module.finrank (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) =
      orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod m) := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := K) (L := K₂) 𝔭 𝔮 hLies, he, hf, one_mul]
  haveI hFDL : FiniteDimensional (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; exact hdpos)
  -- the residue field of `F` has `q ^ d = #𝔽_{q ^ d}` elements, so `μ_m ⊆ F`
  have hN : Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) =
      (NK.LocalStructure.residueCard K 𝔭) ^
        orderOf (NK.LocalStructure.residueCard K 𝔭 : ZMod m) := by
    rw [Commons.NumberTheory.NumberField.Completion.natCard_residueField_adicCompletion_eq_pow_inertiaDeg
      K K₂ 𝔭 𝔮 hLies, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := NK.TameStructureDeep.Degree.exists_isPrimitiveRoot_adicCompletion_of_dvd
    𝔭 𝔮 hLies hm0 (by rw [hN]; exact hdvd)
  -- the image of `π` in `F` has valuation `exp (-1)`
  have hvalπ : Valued.v (algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion K₂)
      (π : 𝔭.adicCompletion K)) = WithZero.exp (-1) := by
    change Valued.v (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hLies
      (π : 𝔭.adicCompletion K)) = WithZero.exp (-1)
    rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow 𝔭 𝔮 hLies,
      he, pow_one]
    exact val_eq_exp_neg_one_of_isUniformizerAt 𝔭 hπ
  -- the two cyclotomic intermediate fields
  let E : IntermediateField (𝔭.adicCompletion K) K' :=
    IntermediateField.adjoin (𝔭.adicCompletion K) ({ζ} : Set K')
  let F₀ : IntermediateField (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    IntermediateField.adjoin (𝔭.adicCompletion K) ({ψ} : Set (𝔮.adicCompletion K₂))
  haveI hintK' : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
  haveI hintF : Algebra.IsIntegral (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) :=
    ⟨fun x => IsIntegral.of_finite (𝔭.adicCompletion K) x⟩
  haveI hcycE : IsCyclotomicExtension ({m} : Set ℕ) (𝔭.adicCompletion K) E :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (𝔭.adicCompletion K) hζ
  haveI hcycF : IsCyclotomicExtension ({m} : Set ℕ) (𝔭.adicCompletion K) F₀ :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (𝔭.adicCompletion K) hψ
  -- transport the relation along the cyclotomic isomorphism
  let e : E ≃ₐ[𝔭.adicCompletion K] F₀ :=
    IsCyclotomicExtension.algEquiv ({m} : Set ℕ) (𝔭.adicCompletion K) E F₀
  intro hα
  have hαE : α ^ n = algebraMap (𝔭.adicCompletion K) E (π : 𝔭.adicCompletion K) := by
    refine Subtype.ext ?_
    simpa using hα
  have hroot : (e α : 𝔮.adicCompletion K₂) ^ n =
      algebraMap (𝔭.adicCompletion K) (𝔮.adicCompletion K₂) (π : 𝔭.adicCompletion K) := by
    have h1 : e (α ^ n) = e (algebraMap (𝔭.adicCompletion K) E (π : 𝔭.adicCompletion K)) := by
      rw [hαE]
    rw [map_pow, AlgEquiv.commutes] at h1
    simpa using congrArg (fun x : F₀ => (x : 𝔮.adicCompletion K₂)) h1
  exact pow_ne_of_val_eq_exp_neg_one (Valued.v : Valuation (𝔮.adicCompletion K₂) ℤᵐ⁰)
    hvalπ hn (e α) hroot

end NK.TameStructureDeep.Tame
