import Mathlib
import Submission.NK.LocalInputs.All
import Submission.NK.LocalStructure.Main
import Submission.NK.LocalReciprocityLubinTate.All
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The group `U¹ = 1 + 𝔪` of principal units of a `p`-adic completion is a pro-`p` group

For a number field `K` and a finite prime `𝔭`, let `R = 𝔭.adicCompletionIntegers K` be the ring of
integers of the completion `κ = K_𝔭` and let

`U¹ = NK.LocalInputs.principalUnits K 𝔭 = ker (Rˣ → 𝓀ˣ) = 1 + 𝔪`

be the group of *principal units* (`𝔪` the maximal ideal of `R`, `𝓀` the residue field).  If `𝓀`
has characteristic `p`, then `U¹` is a pro-`p` group, i.e. all its finite quotients are finite
`p`-groups: this file proves the finite-quotient formulation
`NK.LocalTame.IsProP p ↥(principalUnits K 𝔭)`.

## The argument

The proof avoids the structure theory of `𝔪`-adic filtrations (`U^i/U^{i+1} ≅ 𝔪^i/𝔪^{i+1}`,
cofinality of `U^n` among the finite-index subgroups, both of which need the finite
`ℤ_p`-rank of the completion).  Instead it uses the *inverse* of the `p`-th power map:

1. **`U¹` is `ℓ`-divisible for every prime `ℓ ≠ p`.**  For `u ∈ U¹` the residue of `u` is `1`, and
   `ℓ` is a unit of `R` (its residue is `ℓ ∈ 𝓀`, and `𝓀` has characteristic `p ≠ ℓ`).  Hensel's
   lemma for the Kummer polynomial `X^ℓ - u` in the Henselian local ring `R`
   (`Commons.RingTheory.Henselian.kummer_root_lift`, using Mathlib's
   `HenselianLocalRing` instance for `𝔭.adicCompletionIntegers K` supplied by the commons) produces
   a root `b` with `residue b = 1`; such a `b` is a unit of `U¹`.
2. **A group that is `ℓ`-divisible for every prime `ℓ ≠ p` is pro-`p`.**  If `N ≤ G` has finite
   index `n`, then `G ⧸ N` is a finite group that is still `ℓ`-divisible for every prime `ℓ ≠ p`;
   a finite group whose order is divisible by `ℓ` is never `ℓ`-divisible (Cauchy's theorem:
   an element of order `ℓ` is not a non-trivial `ℓ`-th power), so no prime `≠ p` divides `n`, and
   `n` is a power of `p` (`Nat.eq_prime_pow_of_unique_prime_dvd`).

The only arithmetic input is `CharP 𝓀 p`; `p` is then prime because the residue field is finite
(`𝓀 = R ⧸ 𝔪` is finite, `Commons.…finite_adicCompletionIntegers_quotient_maximalIdeal_pow`).

## Contents

* `NK.TameStructureDeep.Units.isProP_of_forall_prime_ne_pow_surjective` — step 2, abstract;
* `NK.TameStructureDeep.Units.prime_of_charP_residueField` — `p` is prime;
* `NK.TameStructureDeep.Units.exists_pow_eq_of_mem_principalUnits` — step 1;
* `NK.TameStructureDeep.Units.isProP_principalUnits` — the requested theorem.
-/

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Units

/-! ## The abstract criterion: `ℓ`-divisibility for `ℓ ≠ p` forces pro-`p`-ness -/

/-- **A group all of whose elements are `ℓ`-th powers for every prime `ℓ ≠ p` is pro-`p`** in the
finite-quotient sense `NK.LocalTame.IsProP p G`: every normal subgroup of finite index has
`p`-power index.

Indeed, for a normal `N` of finite index the quotient `G ⧸ N` is finite, non-empty and inherits
`ℓ`-divisibility for every prime `ℓ ≠ p`; but a finite group whose order is divisible by the prime
`ℓ` is not `ℓ`-divisible (Cauchy's theorem produces an element of order `ℓ`, which cannot be a
non-trivial `ℓ`-th power).  Hence no prime `≠ p` divides `N.index`, and
`Nat.eq_prime_pow_of_unique_prime_dvd` concludes. -/
theorem isProP_of_forall_prime_ne_pow_surjective {G : Type*} [Group G] {p : ℕ}
    (hdiv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ z : G, ∃ w : G, w ^ ℓ = z) :
    NK.LocalTame.IsProP p G := by
  intro N hN hfi
  haveI : N.Normal := hN
  haveI : N.FiniteIndex := hfi
  refine ⟨N.index.primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.FiniteIndex.index_ne_zero
    (fun {d} hd hdvd => ?_)
  by_contra hdp
  -- `G ⧸ N` is `d`-divisible as a quotient of the `d`-divisible group `G`
  have hquot : ∀ z : G ⧸ N, ∃ w : G ⧸ N, w ^ d = z := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨y, hy⟩ := hdiv d hd hdp x
    exact ⟨QuotientGroup.mk' N y, by rw [← map_pow, hy]⟩
  exact NK.TameStructureDeep.Support.not_dvd_card_of_forall_pow_eq hd hquot
    (by rw [← Subgroup.index_eq_card]; exact hdvd)

/-! ## The residue characteristic is a prime

The residue field `𝓀` of `𝔭.adicCompletionIntegers K` is finite, and a finite non-trivial ring
never has characteristic `0`; hence `CharP 𝓀 p` forces `p.Prime`. -/

/-- **The residue field of `𝔭.adicCompletionIntegers K` is finite**: it is `R ⧸ 𝔪`, and all the
quotients `R ⧸ 𝔪^n` are finite. -/
theorem finite_residueField_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := by
  have h : Finite ((𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) := by
    have h0 :=
      Commons.NumberTheory.NumberField.Completion.finite_adicCompletionIntegers_quotient_maximalIdeal_pow
        K 𝔭 1
    rwa [pow_one] at h0
  exact h

/-- **`p` is prime when it is the characteristic of the residue field**: the residue field is a
finite field. -/
theorem prime_of_charP_residueField {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) : p.Prime := by
  haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    finite_residueField_adicCompletionIntegers 𝔭
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p
    with hp | hp
  · exact hp
  · exfalso
    -- a finite non-trivial ring has a non-zero cardinality, but characteristic `0` forces it to be `0`
    have hchar0 : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) 0 := hp ▸ hchar
    haveI : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) 0 := hchar0
    haveI : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := Fintype.ofFinite _
    have hcard : (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :
        IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    rw [CharP.cast_eq_zero_iff _ 0, zero_dvd_iff] at hcard
    exact Nat.card_ne_zero.mpr ⟨⟨0⟩, hfin⟩ hcard

/-! ## `U¹` is `ℓ`-divisible for every prime `ℓ ≠ p` -/

/-- **The principal units are `ℓ`-divisible for every prime `ℓ ≠ p`** (`p` the residue
characteristic): every `u ∈ U¹` is an `ℓ`-th power in `U¹`.

The `ℓ`-th power map is surjective on `U¹` because it is *invertible* on `U¹`: `ℓ` is a unit of
`R = 𝔭.adicCompletionIntegers K` (its residue `ℓ ∈ 𝓀` is non-zero as `𝓀` has characteristic
`p ≠ ℓ`), so Hensel's lemma for `X^ℓ - u` at the approximate root `1` yields an `ℓ`-th root `b` of
`u` with `residue b = 1`, i.e. an `ℓ`-th root inside `U¹` itself. -/
theorem exists_pow_eq_of_mem_principalUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p ℓ : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    ∀ z : ↥(NK.LocalInputs.principalUnits K 𝔭),
      ∃ w : ↥(NK.LocalInputs.principalUnits K 𝔭), w ^ ℓ = z := by
  intro z
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the ring of integers of the completion is a Henselian local ring
  haveI : HenselianLocalRing (𝔭.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) 𝔭
  -- the residue of a principal unit is `1`
  have hresz : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
      ((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) = 1 := by
    have h1 : Units.map (IsLocalRing.residue (𝔭.adicCompletionIntegers K)).toMonoidHom
        (z : (𝔭.adicCompletionIntegers K)ˣ) = 1 :=
      MonoidHom.mem_ker.mp z.2
    have h2 := congrArg (fun v : (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ =>
      (v : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) h1
    simpa [Units.coe_map] using h2
  -- `ℓ` is a unit of `R`, because its residue in `𝓀` is nonzero
  have hℓunit : IsUnit (ℓ : 𝔭.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hne : (ℓ : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ≠ 0 := by
      intro hzero
      have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff _ p ℓ).mp hzero
      exact hℓp (Nat.prime_dvd_prime_iff_eq hp hℓ |>.mp hdvd).symm
    simpa using hne
  -- Hensel's lemma: `X^ℓ - u` has a root `b` with `residue b = 1`
  obtain ⟨b, hbpow, hbres⟩ := Commons.RingTheory.Henselian.kummer_root_lift
    (R := 𝔭.adicCompletionIntegers K) ℓ ((z : (𝔭.adicCompletionIntegers K)ˣ)).isUnit hℓunit
    (1 : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) (by simp [hresz])
  -- a root of the unit `u` is a unit
  have hbunit : IsUnit b := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hbres]
    exact one_ne_zero
  let w : (𝔭.adicCompletionIntegers K)ˣ := hbunit.unit
  have hwpow : w ^ ℓ = (z : (𝔭.adicCompletionIntegers K)ˣ) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hbpow]
  -- `b` is a principal unit, because its residue is `1`
  have hwmem : w ∈ NK.LocalInputs.principalUnits K 𝔭 := by
    rw [NK.LocalInputs.principalUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
      Units.val_one]
    show IsLocalRing.residue (𝔭.adicCompletionIntegers K) (w : 𝔭.adicCompletionIntegers K) = 1
    rw [show (w : 𝔭.adicCompletionIntegers K) = b from IsUnit.unit_spec hbunit, hbres]
  exact ⟨⟨w, hwmem⟩, Subtype.ext hwpow⟩

/-! ## The theorem -/

/-- **The group of principal units `U¹ = 1 + 𝔪` of a `p`-adic completion is pro-`p`.**

`p` is the residue characteristic of `𝔭` (given by `CharP` of the residue field of
`𝔭.adicCompletionIntegers K`), and the conclusion is the finite-quotient formulation: every
normal subgroup of finite index in `U¹` has `p`-power index.

The proof is the two-step argument described in the module docstring: `U¹` is `ℓ`-divisible for
every prime `ℓ ≠ p` (Hensel for `X^ℓ - u`, `ℓ` a unit of the ring of integers), and an
`ℓ`-divisible-for-all-`ℓ ≠ p` group is pro-`p`. -/
theorem isProP_principalUnits {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    NK.LocalTame.IsProP p ↥(NK.LocalInputs.principalUnits K 𝔭) :=
  isProP_of_forall_prime_ne_pow_surjective fun _ℓ hℓ hℓp =>
    exists_pow_eq_of_mem_principalUnits 𝔭 hchar (prime_of_charP_residueField 𝔭 hchar) hℓ hℓp

end NK.TameStructureDeep.Units
