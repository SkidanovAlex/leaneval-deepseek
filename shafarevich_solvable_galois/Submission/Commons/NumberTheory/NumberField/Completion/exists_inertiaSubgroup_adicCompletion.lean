import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia subgroup of the local Galois group of an adic completion

Let `L / K` be a finite extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  The `Q`-adic completion `K_Q = Q.adicCompletion K`
acts on the `q`-adic completion `L_q = q.adicCompletion L` through the continuous algebra map
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq`.

The main result of this file,

`exists_inertiaSubgroup_adicCompletion`,

is the existence of the **inertia subgroup** of the group
`Gal(L_q / K_Q) = (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)`:

> there is a subgroup `I ≤ Gal(L_q / K_Q)` consisting exactly of those `σ` acting trivially on
> the residue field, i.e. such that `v (σ x - x) < 1` for every `x` in the ring of integers
> `q.adicCompletionIntegers L` of `L_q`.

This is the local input to the description of the decomposition group of a place; the subgroup `I`
is the local inertia group `Gal(L_q/K_Q)^nr` of the local field extension.

## Proof outline

Write `v` for the `q`-adic valuation on `L_q` and `O ⊆ L_q` for `q.adicCompletionIntegers L`.
Call `σ ∈ Gal(L_q/K_Q)` *residue-trivial* if `v (σ x - x) < 1` for all `x ∈ O`.

* Residue-triviality is stable under multiplication: if `σ` and `τ` are residue-trivial and
  `x ∈ O`, then `σ x ∈ O` (because `σ x = x + (σ x - x)` and `v (x + y) ≤ max (v x) (v y)`), so
  `τ x - x ∈ O` is an element of `O` with `v (τ x - x) < 1`; applying `σ` to it and adding gives
  `(σ τ) x - x = σ (τ x - x) + (σ x - x)` with both summands of valuation `< 1`, hence
  `v ((σ τ) x - x) < 1` (`Valuation.map_add_lt`).
* The identity is residue-trivial, so the residue-trivial automorphisms form a submonoid `P`.
* `Gal(L_q/K_Q)` is finite: `L_q` is a finite-dimensional `K_Q`-vector space and a `K_Q`-algebra
  automorphism is determined by the images of a finite generating set
  (`Finite.algHom`/`Finite.algEquiv`).  A submonoid of a finite group is a subgroup:
  `σ ^ orderOf σ = 1` shows `σ⁻¹ = σ ^ (orderOf σ - 1) ∈ P`.

These ingredients are proved abstractly for an arbitrary finite `R`-algebra `K` with a valuation
(`algEquiv_mul_mem_residueTrivial`, `algEquiv_one_mem_residueTrivial`,
`exists_inertiaSubgroup_of_finite`) and then specialised to the local field `L_q / K_Q`.
-/

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- Residue-triviality is stable under composition.

Let `K` be a field with a valuation `v`, `O = v.valuationSubring` its valuation ring.  If the
`R`-algebra automorphisms `σ` and `τ` of `K` both move every element of `O` by an element of
valuation `< 1` (i.e. both act trivially on the residue field of `O`), then so does `σ * τ`. -/
theorem algEquiv_mul_mem_residueTrivial {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {σ τ : K ≃ₐ[R] K}
    (hσ : ∀ x : v.valuationSubring, v (σ (x : K) - (x : K)) < 1)
    (hτ : ∀ x : v.valuationSubring, v (τ (x : K) - (x : K)) < 1) :
    ∀ x : v.valuationSubring, v ((σ * τ) (x : K) - (x : K)) < 1 := by
  intro x
  -- `y = τ x - x` lies in `O` and has valuation `< 1`
  set y : K := τ (x : K) - (x : K) with hydef
  have hyval : v y < 1 := hτ x
  have hymem : y ∈ v.valuationSubring := le_of_lt hyval
  -- hence so does `σ y`
  have hσy : v (σ y) < 1 := by
    have h := hσ ⟨y, hymem⟩
    rw [show σ y = y + (σ y - y) by ring]
    exact v.map_add_lt hyval h
  -- and `(σ * τ) x - x = σ y + (σ x - x)` is a sum of two small elements
  have hstep : (σ * τ) (x : K) - (x : K) = σ y + (σ (x : K) - (x : K)) := by
    rw [hydef, AlgEquiv.mul_apply, map_sub]
    ring
  rw [hstep]
  exact v.map_add_lt hσy (hσ x)

/-- The identity is residue-trivial. -/
theorem algEquiv_one_mem_residueTrivial {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    ∀ x : v.valuationSubring, v ((1 : K ≃ₐ[R] K) (x : K) - (x : K)) < 1 := by
  intro x
  simp only [AlgEquiv.one_apply, sub_self, map_zero]
  exact zero_lt_one

/-- **The inertia subgroup of the automorphism group of a valued field with finite automorphism
group.**

If the group of `R`-algebra automorphisms of a valued field `K` is finite, the residue-trivial
automorphisms (those `σ` with `v (σ x - x) < 1` for all `x` in the valuation ring) form a
subgroup of it. -/
theorem exists_inertiaSubgroup_of_finite {R K : Type*} [CommSemiring R] [Field K] [Algebra R K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    [Finite (K ≃ₐ[R] K)] :
    ∃ I : Subgroup (K ≃ₐ[R] K),
      ∀ σ : K ≃ₐ[R] K, σ ∈ I ↔
        ∀ x : v.valuationSubring, v (σ (x : K) - (x : K)) < 1 := by
  let P : (K ≃ₐ[R] K) → Prop :=
    fun σ => ∀ x : v.valuationSubring, v (σ (x : K) - (x : K)) < 1
  have hP1 : P 1 := algEquiv_one_mem_residueTrivial v
  have hmul : ∀ σ τ, P σ → P τ → P (σ * τ) := fun σ τ hσ hτ =>
    algEquiv_mul_mem_residueTrivial v hσ hτ
  have hpow : ∀ (σ : K ≃ₐ[R] K) (n : ℕ), P σ → P (σ ^ n) := by
    intro σ n hσ
    induction n with
    | zero => simpa using hP1
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hσ
  refine ⟨?_, ?_⟩
  · refine { carrier := {σ | P σ}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }
    · intro a b ha hb
      exact hmul a b ha hb
    · exact hP1
    · -- a submonoid of a finite group is a subgroup
      intro σ hσ
      have hn : 1 ≤ orderOf σ := orderOf_pos σ
      have hm : σ * σ ^ (orderOf σ - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      have hinv : σ⁻¹ = σ ^ (orderOf σ - 1) := inv_eq_of_mul_eq_one_right hm
      rw [hinv]
      exact hpow σ _ hσ
  · intro σ
    exact Iff.rfl

/-- **The inertia subgroup of the local Galois group of an adic completion.**

Let `L / K` be a finite extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  Then the group of `K_Q`-algebra automorphisms of the
local field `L_q = q.adicCompletion L` contains a subgroup `I` consisting exactly of the
automorphisms acting trivially on the residue field of `L_q`, i.e. those `σ` with
`v (σ x - x) < 1` for every `x` in the ring of integers `q.adicCompletionIntegers L`.

`I` is the inertia subgroup `I(L_q/K_Q) ≤ Gal(L_q/K_Q)`. -/
theorem exists_inertiaSubgroup_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ I : Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
        σ ∈ I ↔ ∀ x : q.adicCompletionIntegers L,
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (σ (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- `L_q` is a finite-dimensional `K_Q`-vector space, so its `K_Q`-algebra automorphisms are
  -- finite in number
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Finite (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := Finite.algEquiv
  exact exists_inertiaSubgroup_of_finite
    (Valued.v : Valuation (q.adicCompletion L) (WithZero (Multiplicative ℤ)))

end Commons.NumberTheory.NumberField.Completion
