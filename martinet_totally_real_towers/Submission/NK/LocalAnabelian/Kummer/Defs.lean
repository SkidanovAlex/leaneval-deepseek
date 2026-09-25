/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Kummer theory: the vocabulary

This file fixes the definitions used by the `NK.LocalAnabelian` Kummer bridge:
the class group `kˣ/(kˣ)^p`, and the Kummer field `k(a^{1/p})` of a class `a`,
realised inside a fixed separable closure `K'` of `k` as the subfield generated
by *all* the `p`-th roots of `a`.

Everything downstream (degree-`p` Galois extensions of `k` versus index-`p`
subgroups of `kˣ/(kˣ)^p`, and the count of the former) is stated in terms of
these.
-/
import Mathlib

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

universe u

noncomputable section

/-- The subgroup `(kˣ)^p` of `p`-th powers in the unit group of a field. -/
def powSubgroup (p : ℕ) (k : Type*) [Field k] : Subgroup kˣ :=
  (powMonoidHom p : kˣ →* kˣ).range

/-- The Kummer class group `kˣ / (kˣ)^p`. -/
abbrev KummerGroup (p : ℕ) (k : Type*) [Field k] : Type _ := kˣ ⧸ powSubgroup p k

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- **The Kummer field of `a`**: the subfield of `K'` generated over `k` by all the
`p`-th roots of `a`.

It is defined without any choice: it is the join of all the subfields `k⟮α⟯` with
`α ^ p = a`.  When `K'` is a separable closure of `k` and `a` is not a `p`-th
power, it is a Galois extension of `k` of degree `p`. -/
noncomputable def kummerField (p : ℕ) (a : kˣ) : IntermediateField k K' :=
  IntermediateField.adjoin k {α : K' | α ^ p = algebraMap k K' (a : k)}

/-- Every `p`-th root of `a` lies in the Kummer field of `a`. -/
theorem mem_kummerField_of_pow_eq {p : ℕ} {a : kˣ} {α : K'}
    (hα : α ^ p = algebraMap k K' (a : k)) : α ∈ kummerField (K' := K') p a :=
  IntermediateField.subset_adjoin _ _ (Set.mem_setOf.mpr hα)

/-- The Kummer field of `a` is the smallest subfield containing `k` and one (equivalently
all) `p`-th root of `a`. -/
theorem kummerField_le_iff {p : ℕ} {a : kˣ} {L : IntermediateField k K'} :
    kummerField (K' := K') p a ≤ L ↔
      ∀ α : K', α ^ p = algebraMap k K' (a : k) → α ∈ L := by
  rw [kummerField, IntermediateField.adjoin_le_iff]
  exact ⟨fun h α hα => h (Set.mem_setOf.mpr hα), fun h α hα => h α (Set.mem_setOf.mp hα)⟩

end

end NK.LocalAnabelian
