/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The subfield of `p`-th powers of an intermediate field

For a perfect base field `k` and a field extension `F / k`, and an intermediate field
`L ⊆ F`, the *`p`-th powers of `L`* form a subfield `L^p ⊆ L`, namely the image of the
`p`-th power map (Frobenius) on `L`.  This module defines `pthPowers p L` as an
intermediate field of `F / k` together with its basic API.

The definition needs `k` to be perfect: then the `p`-th power map fixes `k`, so that `L^p`
is again a `k`-subfield of `F`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial

universe u

namespace Work.CurveBasics.Order

variable {k F : Type u}

/-- The subfield of `p`-th powers of an intermediate field `L ⊆ F` (where `k` is perfect, so
that `L^p` contains `algebraMap k F '' k`). -/
noncomputable def pthPowers [Field k] [PerfectField k] [Field F] [Algebra k F]
    (p : ℕ) [ExpChar k p] [ExpChar F p] (L : IntermediateField k F) : IntermediateField k F :=
  Subfield.toIntermediateField ((frobenius F p).comp L.val.toRingHom).fieldRange
    (fun c => by
      obtain ⟨d, hd⟩ := surjective_frobenius k p c
      refine ⟨⟨algebraMap k F d, L.algebraMap_mem d⟩, ?_⟩
      show (frobenius F p) (algebraMap k F d) = algebraMap k F c
      rw [frobenius_def, ← map_pow, show d ^ p = c by rw [← frobenius_def]; exact hd])

lemma frobenius_comp_val [Field k] [Field F] [Algebra k F]
    (p : ℕ) [ExpChar F p] (L : IntermediateField k F) (y : ↥L) :
    ((frobenius F p).comp L.val.toRingHom) y = (y : F) ^ p := by
  rw [RingHom.comp_apply, frobenius_def]
  rfl

/-- Characterisation of the elements of `L^p`. -/
theorem mem_pthPowers [Field k] [PerfectField k] [Field F] [Algebra k F]
    {p : ℕ} [ExpChar k p] [ExpChar F p] {L : IntermediateField k F} {x : F} :
    x ∈ pthPowers p L ↔ ∃ y ∈ L, y ^ p = x := by
  change x ∈ ((frobenius F p).comp L.val.toRingHom).fieldRange ↔ ∃ y ∈ L, y ^ p = x
  rw [RingHom.mem_fieldRange]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y : F), y.2, by rw [← frobenius_comp_val p L y]; exact hy⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, by rw [frobenius_comp_val, hyx]⟩

/-- The `p`-th powers of `L` are contained in `L`. -/
theorem pthPowers_le [Field k] [PerfectField k] [Field F] [Algebra k F]
    (p : ℕ) [ExpChar k p] [ExpChar F p] (L : IntermediateField k F) : pthPowers p L ≤ L :=
  fun _ hx => by
    obtain ⟨y, hy, hyx⟩ := mem_pthPowers.mp hx
    rw [← hyx]
    exact pow_mem hy p

/-- Monotonicity of `L ↦ L^p`. -/
theorem pthPowers_mono [Field k] [PerfectField k] [Field F] [Algebra k F]
    {p : ℕ} [ExpChar k p] [ExpChar F p] {L M : IntermediateField k F} (h : L ≤ M) :
    pthPowers p L ≤ pthPowers p M :=
  fun _ hx => by
    obtain ⟨y, hy, hyx⟩ := mem_pthPowers.mp hx
    exact mem_pthPowers.mpr ⟨y, h hy, hyx⟩

/-- `h ^ p ∈ L ^ p` for `h ∈ L`. -/
theorem pow_mem_pthPowers [Field k] [PerfectField k] [Field F] [Algebra k F]
    {p : ℕ} [ExpChar k p] [ExpChar F p] {L : IntermediateField k F} {h : F} (hh : h ∈ L) :
    h ^ p ∈ pthPowers p L :=
  mem_pthPowers.mpr ⟨h, hh, rfl⟩

/-- The `p`-th power map is injective, hence `x ^ p = y ^ p` implies `x = y`. -/
theorem pow_p_eq_pow_p_iff [Field F] {p : ℕ} [ExpChar F p] {x y : F} :
    x ^ p = y ^ p ↔ x = y :=
  ⟨fun h => frobenius_inj F p h, fun h => by rw [h]⟩

end Work.CurveBasics.Order
