/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level of a non-inertia element

Let `κ` be a field, `K'` a separably closed field extension of characteristic `0`
(in the application `κ = K_𝔭` is a `p`-adic field and `K' = κ̄`), `p` a prime and
`σ ∈ Gal(K'/κ)`.  Write `I = inertiaSubgroup p` for the subgroup of `Gal(K'/κ)`
consisting of the automorphisms acting trivially on every root of unity of order
prime to `p`.

The main result `exists_level_of_notMem_inertia` says that an element `σ ∉ I` is
already detected at the level `n` of a *root of unity* `ζ` of order `n`: there is
`n > 1` with `p ∤ n`, a primitive `n`-th root of unity `ζ` moved by `σ`, and an
integer `a` with `σ ζ = ζ ^ a`, such that moreover

  `n ∤ (a - 1)`   and   `n ∤ (a - 1) ^ 2`.

The first non-divisibility just says `σ ζ ≠ ζ`; the second says that the level `n`
is *large compared with* the `ℓ`-adic valuation of `a - 1` for some prime `ℓ ∣ n`,
which is what makes the level a genuine (non-trivial) Kummer level in the tamely
ramified structure theory.  The proof takes `n = m ^ 2`, where `m` is any level at
which `σ` is already nontrivial: the exponent of `σ` at the level `m ^ 2` reduces
modulo `m` to the exponent at the level `m`, and squaring the level dominates the
valuation of `a - 1` at a prime `ℓ ∣ m` for which `ℓ ^ (v_ℓ m) ∤ (a - 1)`.
-/
import Mathlib
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.TameStructureDeep.Tame.prime_pow_dvd_of_pow_dvd_sq
import Submission.NK.TameStructureDeep.Tame.exists_prime_pow_not_dvd_of_not_dvd
import Submission.NK.TameStructureDeep.Tame.dvd_sub_of_sq_action
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Classical

namespace NK.TameStructureDeep.Tame

/-! ## The main result -/

theorem exists_level_of_notMem_inertia {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosed K'] [CharZero K'] {p : ℕ} (hp : p.Prime) {σ : Gal(K'/κ)}
    (hσ : σ ∉ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) :
    ∃ n : ℕ, ¬ p ∣ n ∧ 1 < n ∧ ∃ ζ : K', IsPrimitiveRoot ζ n ∧ σ ζ ≠ ζ ∧
      ∃ a : ℤ, σ ζ = ζ ^ a ∧ ¬ ((n : ℤ) ∣ (a - 1)) ∧ ¬ ((n : ℤ) ∣ (a - 1) ^ 2) := by
  -- a level `m` at which `σ` is already nontrivial
  rw [NK.LocalAnabelian.mem_inertiaSubgroup_iff] at hσ
  push Not at hσ
  obtain ⟨m, hpm, ζ₀, hζ₀, hne⟩ := hσ
  have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  haveI : NeZero m := ⟨hm0⟩
  have hm1 : 1 < m := by
    rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hm0) with h | h
    · exact h
    · exfalso
      have hz : ζ₀ = 1 := IsPrimitiveRoot.one_right_iff.mp (h.symm ▸ hζ₀)
      exact hne (by rw [hz, map_one])
  -- the exponent `a` of `σ` at the level `m`
  have hζσ : IsPrimitiveRoot (σ ζ₀) m := hζ₀.map_of_injective σ.injective
  obtain ⟨a, ha_lt, ha⟩ := hζ₀.eq_pow_of_pow_eq_one hζσ.pow_eq_one
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (by rw [← ha, h, pow_zero] : σ ζ₀ = 1) (hζσ.ne_one hm1)
    · exact h
  have hnotdvd : ¬ m ∣ a - 1 := by
    intro hd
    have h1 : ζ₀ ^ (a - 1) = 1 := (hζ₀.pow_eq_one_iff_dvd _).mpr hd
    have h2 : ζ₀ ^ a = ζ₀ := by
      rw [← Nat.sub_add_cancel ha1, pow_add, h1, one_mul, pow_one]
    exact hne (by rw [← ha]; exact h2)
  have hAne : a - 1 ≠ 0 := fun h => hnotdvd (h ▸ dvd_zero m)
  -- a prime `ℓ` such that the `ℓ`-part of `m` does not divide `a - 1`
  obtain ⟨ℓ, hℓprime, hℓnotdvd⟩ := exists_prime_pow_not_dvd_of_not_dvd hm0 hAne hnotdvd
  -- the exponent `b` of `σ` at the level `m ^ 2`
  have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  haveI : NeZero ((m ^ 2 : ℕ) : K') := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr hm0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K' (m ^ 2)
  have hζσ' : IsPrimitiveRoot (σ ζ) (m ^ 2) := hζ.map_of_injective σ.injective
  obtain ⟨b, hb_lt, hb⟩ := hζ.eq_pow_of_pow_eq_one hζσ'.pow_eq_one
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exact absurd (by rw [← hb, h, pow_zero] : σ ζ = 1) (hζσ'.ne_one (by nlinarith [hm1]))
    · exact h
  -- the exponents agree modulo `m`
  have hcomp : (m : ℤ) ∣ (b : ℤ) - (a : ℤ) := dvd_sub_of_sq_action hm0 hζ₀ hζ ha.symm hb.symm
  have hℓdvdm : ℓ ^ (m.factorization ℓ) ∣ m :=
    (hℓprime.pow_dvd_iff_le_factorization hm0).mpr le_rfl
  have hℓk_dvd_m2 : ℓ ^ (m.factorization ℓ) ∣ m ^ 2 := by
    rw [pow_two]; exact dvd_mul_of_dvd_right hℓdvdm m
  -- the `ℓ`-part of `m` does not divide `b - 1`
  have hcore : ¬ (ℓ ^ (m.factorization ℓ)) ∣ (b - 1) := by
    intro hd
    have hdZ : ((ℓ : ℤ) ^ (m.factorization ℓ)) ∣ ((b : ℤ) - 1) := by
      have h1 : ((ℓ ^ (m.factorization ℓ) : ℕ) : ℤ) ∣ ((b - 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hd
      rwa [Nat.cast_pow, Nat.cast_sub hb1] at h1
    have hmZ : ((ℓ : ℤ) ^ (m.factorization ℓ)) ∣ (m : ℤ) := by
      have h1 : ((ℓ ^ (m.factorization ℓ) : ℕ) : ℤ) ∣ ((m : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hℓdvdm
      rwa [Nat.cast_pow] at h1
    have h2 : ((ℓ : ℤ) ^ (m.factorization ℓ)) ∣ ((b : ℤ) - (a : ℤ)) := dvd_trans hmZ hcomp
    have h3 : ((ℓ : ℤ) ^ (m.factorization ℓ)) ∣ ((a : ℤ) - 1) := by
      have h4 := dvd_sub hdZ h2
      have heq : (b : ℤ) - 1 - ((b : ℤ) - (a : ℤ)) = (a : ℤ) - 1 := by ring
      rwa [heq] at h4
    have h5 : ((ℓ ^ (m.factorization ℓ) : ℕ) : ℤ) ∣ ((a - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Nat.cast_sub ha1]
      exact h3
    exact hℓnotdvd (Int.natCast_dvd_natCast.mp h5)
  have hBnotdvd : ¬ (m ^ 2) ∣ (b - 1) := fun hd => hcore (dvd_trans hℓk_dvd_m2 hd)
  have hBsqnotdvd : ¬ (m ^ 2) ∣ (b - 1) ^ 2 := by
    intro hd
    have h2k : ℓ ^ (2 * (m.factorization ℓ)) ∣ m ^ 2 := by
      have h := pow_dvd_pow_of_dvd hℓdvdm 2
      rwa [← pow_mul, mul_comm (m.factorization ℓ) 2] at h
    exact hcore (prime_pow_dvd_of_pow_dvd_sq hℓprime (dvd_trans h2k hd))
  refine ⟨m ^ 2, fun h => hpm (hp.dvd_of_dvd_pow h), by nlinarith [hm1], ζ, hζ, ?_,
    (b : ℤ), ?_, ?_, ?_⟩
  · -- `σ` moves `ζ`
    intro heq
    apply hBnotdvd
    have hbeq : ζ ^ b = ζ := by rw [hb, heq]
    have h1 : ζ ^ (b - 1) = 1 := by
      have h2 : ζ ^ (b - 1) * ζ = ζ := by rw [← pow_succ, Nat.sub_add_cancel hb1, hbeq]
      exact mul_right_cancel₀ (hζ.ne_zero hm2ne) (by rw [one_mul]; exact h2)
    exact (hζ.pow_eq_one_iff_dvd _).mp h1
  · -- `σ ζ = ζ ^ b`
    rw [← hb, zpow_natCast]
  · -- `m ^ 2 ∤ (b - 1)`
    intro hd
    apply hBnotdvd
    have h1 : ((m ^ 2 : ℕ) : ℤ) ∣ ((b - 1 : ℕ) : ℤ) := by
      have h0 : (b : ℤ) - 1 = ((b - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hb1]; ring
      rwa [h0] at hd
    exact Int.natCast_dvd_natCast.mp h1
  · -- `m ^ 2 ∤ (b - 1) ^ 2`
    intro hd
    apply hBsqnotdvd
    have h1 : ((m ^ 2 : ℕ) : ℤ) ∣ (((b - 1 : ℕ) : ℤ) ^ 2) := by
      rw [Nat.cast_sub hb1]
      exact hd
    have h2 : ((m ^ 2 : ℕ) : ℤ) ∣ (((b - 1) ^ 2 : ℕ) : ℤ) := by
      rwa [← Nat.cast_pow] at h1
    exact Int.natCast_dvd_natCast.mp h2

end NK.TameStructureDeep.Tame
