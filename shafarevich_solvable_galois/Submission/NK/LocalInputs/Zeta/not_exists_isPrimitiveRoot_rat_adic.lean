import Mathlib
import Submission.NK.LocalInputs.Hints
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ζ_p ∉ ℚ_p` for odd `p`

For an odd prime `p` the `p`-adic field `ℚ_p = 𝔭.adicCompletion ℚ` contains no primitive
`p`-th root of unity: `NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic`.

The argument is the classical valuation computation of the norm of `1 - ζ`:

* if `ζ` is a primitive `p`-th root of unity in `ℚ_p`, then `ζ` is a unit of the valuation
  ring `𝒪 = 𝔭.adicCompletionIntegers ℚ` (`ζ ^ p = 1` bounds `v ζ`);
* the residue field of `𝒪` has characteristic `p` (`p` lies in the maximal ideal because
  `v p = exp (-1) < 1`), so `(ζ̄ - 1) ^ p = ζ̄ ^ p - 1 = 0` and hence `ζ̄ = 1` in the residue
  field: the reduction is a domain;
* consequently `1 - ζ ^ i ∈ 𝔪` for every `i`, and the classical identity
  `∏_{i < p} (1 - ζ ^ (i+1)) = p` (`IsPrimitiveRoot.prod_one_sub_pow_eq_order`) exhibits `p`
  as a product of `p - 1` elements of the maximal ideal: `v p ≤ exp (-(p - 1))`;
* but `v p = exp (-1)` (`Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat`)
  and `p - 1 ≥ 2`, a contradiction.
-/

namespace NK.LocalInputs.Zeta

open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

set_option linter.style.haveILetI false

/-- A product of elements of an ideal `I`, indexed by a finset `s`, lies in `I ^ s.card`. -/
private lemma prod_mem_pow {R ι : Type*} [CommRing R] (I : Ideal R) (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, f i ∈ I) : ∏ i ∈ s, f i ∈ I ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Ideal.mul_mem_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **There is no primitive `p`-th root of unity in `ℚ_p` for odd `p`.** -/
theorem not_exists_isPrimitiveRoot_rat_adic
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hprim : (Rat.HeightOneSpectrum.primesEquiv 𝔭).1 = p) :
    ¬ ∃ ζ : 𝔭.adicCompletion ℚ, IsPrimitiveRoot ζ p := by
  classical
  rintro ⟨ζ, hζ⟩
  -- `p ≥ 3`
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  -- `p` lies in the prime `𝔭`, so that `v p = exp (-1)` in the completion.
  have hpmem : (p : NumberField.RingOfIntegers ℚ) ∈ 𝔭.asIdeal :=
    Commons.NumberTheory.NumberField.mem_of_primesEquiv_eq 𝔭 p hp (Subtype.ext hprim)
  have hvalp : Valued.v (R := 𝔭.adicCompletion ℚ) (Γ₀ := Zstar0)
      ((p : ℚ) : 𝔭.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) :=
    Commons.NumberTheory.NumberField.Completion.val_prime_adicCompletion_rat hp 𝔭 hpmem
  -- `ζ` is a unit: `v ζ = 1` since `(v ζ) ^ p = v (ζ ^ p) = 1` and `v ζ ≥ 1` is impossible.
  have hζval : Valued.v (R := 𝔭.adicCompletion ℚ) (Γ₀ := Zstar0) ζ ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have h1 : (1 : Zstar0) < (Valued.v (R := 𝔭.adicCompletion ℚ) (Γ₀ := Zstar0) ζ) ^ p :=
      one_lt_pow₀ h hp.ne_zero
    rw [← map_pow, hζ.pow_eq_one, map_one] at h1
    exact lt_irrefl 1 h1
  have hζmem : ζ ∈ 𝔭.adicCompletionIntegers ℚ :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers ℚ) ℚ 𝔭).mpr hζval
  let z : 𝔭.adicCompletionIntegers ℚ := ⟨ζ, hζmem⟩
  have hzprim : IsPrimitiveRoot z p :=
    IsPrimitiveRoot.of_map_of_injective
      (f := ValuationSubring.subtype (𝔭.adicCompletionIntegers ℚ))
      (by simpa only [ValuationSubring.subtype_apply] using hζ)
      (ValuationSubring.subtype_injective (𝔭.adicCompletionIntegers ℚ))
  -- `p` is in the maximal ideal: `v p = exp (-1) < 1`.
  have hpm : (p : 𝔭.adicCompletionIntegers ℚ) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ℚ) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one]
    have hcoe : ((p : 𝔭.adicCompletionIntegers ℚ) : 𝔭.adicCompletion ℚ)
        = ((p : ℚ) : 𝔭.adicCompletion ℚ) := by
      push_cast
      rfl
    rw [hcoe, hvalp, ← WithZero.exp_zero (M := ℤ)]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  -- hence the residue field has characteristic `p`.
  have hpres : (p : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) = 0 := by
    have h1 : IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ)
        (p : 𝔭.adicCompletionIntegers ℚ) = 0 :=
      (IsLocalRing.residue_eq_zero_iff (p : 𝔭.adicCompletionIntegers ℚ)).mpr hpm
    simpa using h1
  haveI : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr hpres
  haveI : Fact p.Prime := ⟨hp⟩
  -- in characteristic `p`, `(ζ̄ - 1) ^ p = ζ̄ ^ p - 1 = 0`, so `ζ̄ = 1`.
  have hresζ : IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ) z = 1 := by
    have hp1 : (IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ) z) ^ p = 1 := by
      rw [← map_pow (IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ)) z p,
        hzprim.pow_eq_one, map_one]
    have h2 : (IsLocalRing.residue (𝔭.adicCompletionIntegers ℚ) z - 1) ^ p = 0 := by
      rw [sub_pow_char, hp1, one_pow, sub_self]
    have h3 := (pow_eq_zero_iff hp.ne_zero).mp h2
    exact sub_eq_zero.mp h3
  -- thus every `1 - ζ ^ i` is a non-unit: it lies in the maximal ideal.
  have hmemfac : ∀ k : ℕ, (1 - z ^ (k + 1)) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ℚ) := by
    intro k
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, map_one, map_pow, hresζ, one_pow, sub_self]
  have hzprim' : IsPrimitiveRoot z (p - 1 + 1) := by
    rw [Nat.sub_add_cancel hp.one_le]; exact hzprim
  have hprod := IsPrimitiveRoot.prod_one_sub_pow_eq_order hzprim'
  -- `p = ∏_{i<p-1} (1 - ζ ^ (i+1)) ∈ 𝔪 ^ (p - 1)`.
  have hmemprod : (p : 𝔭.adicCompletionIntegers ℚ) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ℚ) ^ (p - 1) := by
    have hmem := prod_mem_pow (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers ℚ))
      (Finset.range (p - 1)) (fun k => 1 - z ^ (k + 1)) (fun k _ => hmemfac k)
    rw [Finset.card_range] at hmem
    have hcast : ((p - 1 : ℕ) : 𝔭.adicCompletionIntegers ℚ) + 1
        = (p : 𝔭.adicCompletionIntegers ℚ) := by
      rw [← Nat.cast_one (R := 𝔭.adicCompletionIntegers ℚ), ← Nat.cast_add,
        Nat.sub_add_cancel hp.one_le]
    rw [hprod, hcast] at hmem
    exact hmem
  -- hence `v p ≤ exp (-(p - 1))`, contradicting `v p = exp (-1)`.
  have hvalle := (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
    𝔭 (p : 𝔭.adicCompletionIntegers ℚ) (p - 1)).mpr hmemprod
  have hcoe : ((p : 𝔭.adicCompletionIntegers ℚ) : 𝔭.adicCompletion ℚ)
      = ((p : ℚ) : 𝔭.adicCompletion ℚ) := by
    push_cast
    rfl
  rw [hcoe, hvalp] at hvalle
  have hle := WithZero.exp_le_exp.mp hvalle
  have hp1z : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  omega

end NK.LocalInputs.Zeta
