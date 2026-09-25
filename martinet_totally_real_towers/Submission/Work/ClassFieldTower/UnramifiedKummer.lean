import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.TwoDescentDefs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.kummer_expTwo_iso
import Submission.Work.ClassFieldTower.exists_ideal_sq_of_unramified

/-!
# `Work.ClassFieldTower.UnramifiedKummer` -- the elementary two-descent for unramified levels

This module assembles the two proved ingredients of the Kummer two-descent into the statement a
user of this chapter needs: **an unramified exponent-`2` level of a number field is described by
Kummer classes whose integral representatives have square principal ideals**.

* exponent-`2` Kummer theory (`kummer_expTwo_iso`): for a finite Galois `L/K` with `∀ σ, σ² = 1` and
  `char K ≠ 2`, the subgroup `U ≤ Kˣ/(Kˣ)²` of classes with a square root in `L` satisfies
  `Gal(L/K) ≃* Hom(U, 𝔽₂)` and `|Gal(L/K)| = |U|`;
* unramifiedness forces even valuations (`exists_ideal_sq_of_unramified`): for `L/K` unramified,
  every `a ∈ 𝓞 K` that becomes a square in `L` has `(a)` a square of an integral ideal.

Combined: for `L/K` unramified with `Gal(L/K)` of exponent `2`, the Kummer classes of `L` are
precisely the classes of elements whose principal ideal is a square — i.e. `U` is a subgroup of
`V/K^{×2}`, `V = {x : (x) = I²}`.  That is the input on which the (elementary) two-descent count
`dim_{𝔽₂}(V/K^{×2}) = rank₂ Cl(K) + d₂(O_K^×)` runs; see the `README` §11.3.

## Main results

* `exists_kummerSubgroup_of_unramified` -- the general assembly;
* `exists_kummerSubgroup_witness` -- its specialisation to `Kc = ℚ(√-30030)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The elementary two-descent for an unramified exponent-`2` level.**

For a finite Galois extension `L/K` of number fields with `char K ≠ 0`-independent hypothesis
`(2 : K) ≠ 0`, unramified over `K` (`differentIdeal (𝓞 K) (𝓞 L) = ⊤`) and with `Gal(L/K)` of
exponent `2`, there is a subgroup `U ≤ Kˣ/(Kˣ)²` such that

* `U` is exactly the set of Kummer classes with a square root in `L`,
* `Gal(L/K) ≃* Hom(U, 𝔽₂)` and `Nat.card (L ≃ₐ[K] L) = Nat.card U`,
* every nonzero `a ∈ 𝓞 K` with a square root in `L` has `(a)` a square of an integral ideal. -/
theorem exists_kummerSubgroup_of_unramified {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hchar : (2 : K) ≠ 0)
    (hunr : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤)
    (h2 : ∀ σ : L ≃ₐ[K] L, σ ^ 2 = 1) :
    ∃ (U : Subgroup (Kˣ ⧸ Sq K)),
      (∀ a : Kˣ, (QuotientGroup.mk' (Sq K) a) ∈ U ↔
        ∃ b : L, b * b = algebraMap K L (a : K)) ∧
      Nonempty ((L ≃ₐ[K] L) ≃* (U →* Multiplicative (ZMod 2))) ∧
      Nat.card (L ≃ₐ[K] L) = Nat.card U ∧
      (∀ a : NumberField.RingOfIntegers K, a ≠ 0 →
        (∃ b : L, b * b = algebraMap K L (a : K)) →
        ∃ I : Ideal (NumberField.RingOfIntegers K), I * I = Ideal.span {a}) := by
  obtain ⟨U, hU, hiso, hcard⟩ := kummer_expTwo_iso h2 hchar
  exact ⟨U, hU, hiso, hcard,
    fun a ha hsq => exists_ideal_sq_of_unramified a ha hunr hsq⟩

/-- **The same for the explicit witness field `Kc = ℚ(√-30030)`.** -/
theorem exists_kummerSubgroup_witness (L : Type) [Field L] [NumberField L] [Algebra Kc L]
    [FiniteDimensional Kc L] [IsGalois Kc L]
    (hunr : differentIdeal (NumberField.RingOfIntegers Kc) (NumberField.RingOfIntegers L) = ⊤)
    (h2 : ∀ σ : L ≃ₐ[Kc] L, σ ^ 2 = 1) :
    ∃ (U : Subgroup (Kcˣ ⧸ Sq Kc)),
      (∀ a : Kcˣ, (QuotientGroup.mk' (Sq Kc) a) ∈ U ↔
        ∃ b : L, b * b = algebraMap Kc L (a : Kc)) ∧
      Nonempty ((L ≃ₐ[Kc] L) ≃* (U →* Multiplicative (ZMod 2))) ∧
      Nat.card (L ≃ₐ[Kc] L) = Nat.card U := by
  obtain ⟨U, hU, hiso, hcard, -⟩ :=
    exists_kummerSubgroup_of_unramified (K := Kc) (L := L)
      (by norm_num) hunr h2
  exact ⟨U, hU, hiso, hcard⟩

end Work.ClassFieldTower
