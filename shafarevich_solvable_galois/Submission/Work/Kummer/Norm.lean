/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The norm subgroup of a finite extension

For a finite extension `L/K` we write `N_{L/K}(Lˣ) ≤ Kˣ` for the group of norms of units of `L`.
It contains `(Kˣ)^n` by `Algebra.norm_algebraMap`, and it is the group in which the obstruction to
the cyclic embedding problem lives: the Kummer-theoretic criterion says that the embedding problem
with cyclic kernel `ℤ/n` is solvable if and only if the primitive `n`-th root of unity `ζ` lies in
`normSubgroup K L`.
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.Norm.Basic
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The group `N_{L/K}(Lˣ)` of norms of units, as a subgroup of `Kˣ`. -/
def normSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ where
  carrier := {x | ∃ y : Lˣ, Algebra.norm K (y : L) = (x : K)}
  mul_mem' := by
    rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [Units.val_mul, map_mul, hx, hy, Units.val_mul]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro _ ⟨x, hx⟩
    exact ⟨x⁻¹, by rw [Units.val_inv_eq_inv_val, Algebra.norm_inv, hx, Units.val_inv_eq_inv_val]⟩

@[simp]
lemma mem_normSubgroup [FiniteDimensional K L] {x : Kˣ} :
    x ∈ normSubgroup K L ↔ ∃ y : Lˣ, Algebra.norm K (y : L) = (x : K) := Iff.rfl

variable [FiniteDimensional K L]

/-- If the degree `[L : K]` divides `n`, then every `n`-th power in `K` is a norm from `L`:
`a^n = N_{L/K}(a^(n/[L:K]))`. -/
lemma nthPowerSubgroup_le_normSubgroup {n : ℕ} (h : Module.finrank K L ∣ n) :
    nthPowerSubgroup n Kˣ ≤ normSubgroup K L := by
  obtain ⟨m, rfl⟩ := h
  rintro x ⟨y, rfl⟩
  refine ⟨Units.map (algebraMap K L) (y ^ m), ?_⟩
  show Algebra.norm K ((Units.map (algebraMap K L) (y ^ m) : Lˣ) : L) =
    ((y ^ (Module.finrank K L * m) : Kˣ) : K)
  rw [show ((Units.map (algebraMap K L) (y ^ m) : Lˣ) : L) = algebraMap K L ((y : K) ^ m) from rfl,
    Algebra.norm_algebraMap, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]

variable {n : ℕ} [NeZero n] {ζ : K}

/-- The primitive `n`-th root of unity, as an element of `Kˣ`, is `n`-torsion modulo the norm
group: its class in `Kˣ/N_{L/K}(Lˣ)` has order dividing `n`. -/
lemma primRootUnit_pow_mem_normSubgroup (hζ : IsPrimitiveRoot ζ n) :
    primRootUnit hζ ^ n ∈ normSubgroup K L := by
  have h1 : primRootUnit hζ ^ n = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, primRootUnit_coe, hζ.pow_eq_one, Units.val_one]
  rw [h1]
  exact one_mem _

end Work.Kummer
