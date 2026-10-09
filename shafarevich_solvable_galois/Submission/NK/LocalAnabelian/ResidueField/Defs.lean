/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inertia subgroup, the Frobenius, and the residue field cardinality

This file sets up part (C) of the `NK.LocalAnabelian` chapter: the recovery of
the residue field cardinality `q` of a `p`-adic field `κ` from `Gal(κ̄/κ)`.

The one classical identification used is

  `κ^ur = κ(μ_{p'})`,  the maximal unramified extension of `κ` is obtained by
  adjoining all roots of unity of order prime to `p` (an unramified extension is
  determined by its residue field, and `[κ(ζ_n) : κ] = ord_n(q)` for `(n,p) = 1`).

Consequently

* the **inertia subgroup** `I = Gal(κ̄/κ^ur)` is the kernel of the action of
  `Gal(κ̄/κ)` on the roots of unity of order prime to `p`, and
* the **Frobenius** is the action `ζ ↦ ζ^q`, which makes `q` visible from the
  group alone.

`unramifiedClosure` is `κ(μ_{p'})` realised inside the separable closure `K'`,
`inertiaSubgroup` is its fixing subgroup (equivalently, the cyclotomic kernel), and
`ActsAsFrobenius p q σ` says that `σ` acts on prime-to-`p` roots of unity by the
`q`-power map.  The main unconditional result is `eq_of_actsAsFrobenius`: a single
such element determines `q`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## The maximal unramified extension as `κ(μ_{p'})` -/

/-- The maximal unramified extension of `κ` inside `K'`, realised as the compositum
of all `κ(ζ_n)` for `n` prime to `p` (this is `κ(μ_{p'})`). -/
noncomputable def unramifiedClosure (p : ℕ) : IntermediateField κ K' :=
  ⨆ (n : {n : ℕ // ¬ p ∣ n}) (ζ : K') (_ : IsPrimitiveRoot ζ (n : ℕ)), κ⟮ζ⟯

/-! ## The inertia subgroup -/

/-- **The inertia subgroup** of `Gal(K'/κ)`: the `κ`-automorphisms of `K'` acting
trivially on every root of unity of order prime to `p`.

For `κ` a `p`-adic field this is the inertia subgroup `Gal(K'/κ^ur)`, since
`κ^ur = κ(μ_{p'})`; see `inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure`. -/
def inertiaSubgroup (p : ℕ) : Subgroup (Gal(K'/κ)) where
  carrier := {σ | ∀ n : ℕ, ¬ p ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → σ ζ = ζ}
  one_mem' := by intro n _ ζ _; rfl
  mul_mem' := by
    intro σ τ hσ hτ n hn ζ hζ
    show (σ * τ) ζ = ζ
    rw [AlgEquiv.mul_apply, hσ n hn (τ ζ) (hζ.map_of_injective τ.injective), hτ n hn ζ hζ]
  inv_mem' := by
    intro σ hσ n hn ζ hζ
    have h := hσ n hn (σ.symm ζ) (hζ.map_of_injective σ.symm.injective)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm

/-- Characterisation of membership in the inertia subgroup. -/
theorem mem_inertiaSubgroup_iff (p : ℕ) (σ : Gal(K'/κ)) :
    σ ∈ inertiaSubgroup (κ := κ) (K' := K') p ↔
      ∀ n : ℕ, ¬ p ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → σ ζ = ζ :=
  Iff.rfl

/-- The inertia subgroup is normal in `Gal(K'/κ)`. -/
instance inertiaSubgroup_normal (p : ℕ) :
    (inertiaSubgroup (κ := κ) (K' := K') p).Normal where
  conj_mem := by
    intro σ hσ τ
    change ∀ n : ℕ, ¬ p ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → (τ * σ * τ⁻¹) ζ = ζ
    intro n hn ζ hζ
    have hτ : IsPrimitiveRoot (τ.symm ζ) n := hζ.map_of_injective τ.symm.injective
    have h := hσ n hn (τ.symm ζ) hτ
    calc (τ * σ * τ⁻¹) ζ = τ (σ (τ.symm ζ)) := rfl
      _ = τ (τ.symm ζ) := by rw [h]
      _ = ζ := AlgEquiv.apply_symm_apply τ ζ

/-! ## The Frobenius action -/

/-- `σ` acts on the roots of unity of order prime to `p` as the `q`-power map: `σ` is a
Frobenius element attached to a residue field of cardinality `q`. -/
def ActsAsFrobenius (p q : ℕ) (σ : Gal(K'/κ)) : Prop :=
  ∀ n : ℕ, ¬ p ∣ n → ∀ ζ : K', IsPrimitiveRoot ζ n → σ ζ = ζ ^ q

/-- **The residue field cardinality is determined by the Frobenius action.**  A single
element `σ` of `Gal(K'/κ)` cannot act on all prime-to-`p` roots of unity by two different
power maps: taking a prime `ℓ ≠ p` exceeding both `q` and `q'`, a primitive `ℓ`-th root of
unity forces `ℓ ∣ (q - q')`. -/
theorem eq_of_actsAsFrobenius {p q q' : ℕ} {σ : Gal(K'/κ)} (hp : p.Prime)
    (hroot : ∀ n : ℕ, ¬ p ∣ n → ∃ ζ : K', IsPrimitiveRoot ζ n)
    (h : ActsAsFrobenius (κ := κ) (K' := K') p q σ)
    (h' : ActsAsFrobenius (κ := κ) (K' := K') p q' σ) : q = q' := by
  obtain ⟨ℓ, hℓge, hℓprime⟩ := Nat.exists_infinite_primes (p + q + q' + 1)
  have hℓne : ¬ p ∣ ℓ := by
    intro hd
    have hpe : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓprime).mp hd
    omega
  obtain ⟨ζ, hζ⟩ := hroot ℓ hℓne
  have hζne : ζ ≠ 0 := hζ.ne_zero hℓprime.ne_zero
  have hpq : ζ ^ q = ζ ^ q' := by rw [← h ℓ hℓne ζ hζ, h' ℓ hℓne ζ hζ]
  have hltq : q < ℓ := by omega
  have hltq' : q' < ℓ := by omega
  have key : ∀ {a b : ℕ}, a ≤ b → b < ℓ → ζ ^ a = ζ ^ b → b - a = 0 := by
    intro a b hle hbℓ hab
    have h1 : ζ ^ b = ζ ^ a * ζ ^ (b - a) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [← hab] at h1
    have h2 : ζ ^ a * 1 = ζ ^ a * ζ ^ (b - a) := by rw [mul_one]; exact h1
    have hpow : ζ ^ (b - a) = 1 :=
      (mul_left_cancel₀ (pow_ne_zero a hζne) h2).symm
    have hdvd : ℓ ∣ b - a := hζ.dvd_of_pow_eq_one _ hpow
    have hlt : b - a < ℓ := by omega
    rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
    · exact h0
    · exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)
  rcases le_total q q' with hle | hle
  · have := key hle hltq' hpq
    omega
  · have := key hle hltq hpq.symm
    omega

/-- In a separably closed field of characteristic not dividing `n`, primitive `n`-th roots
of unity exist.  In particular a separable closure of a `p`-adic field contains primitive
`n`-th roots of unity for every `n` prime to `p`. -/
theorem exists_isPrimitiveRoot_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {n : ℕ} [NeZero (n : K)] : ∃ ζ : K, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.exists_primitiveRoot K n

end

end NK.LocalAnabelian
