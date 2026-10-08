/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# The inversion set `I_K(s) = invSet K s` only depends on the coset of `s` modulo `C_G(K)`

Bender's `I_K(s) = {x ∈ K | x^s = x⁻¹}` (`Work.GW2.invSet`) is the basic object of the whole
`I_U(s)` calculus of Gorenstein–Walter.  This file records the first invariance property it has:

> if `y` centralizes `K`, then `invSet K (y * s) = invSet K s`.

It is the step that lets one replace `s` by any other element of `s · C_G(K)`, and it is used in
`Submission/Work/CORE4/Case2NotInvNormal.lean` to identify `I_U(s')` for an arbitrary
`s' ∈ S ∖ S₀` with `I_U(s)`, using `S₀ ≤ C_G(U)` (Bender p. 227: `S₀ = C_S(U)`).

The proof is the computation `(y*s) x (y*s)⁻¹ = y (s x s⁻¹) y⁻¹`, together with the fact that
`y ∈ C_G(K)` commutes with `x ∈ K`, hence with `x⁻¹`.
-/
import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.InvSet

open Subgroup

/-- **Inversion sets only depend on the coset modulo the centralizer.**  If `y` centralizes `K`,
then `invSet K (y * s) = invSet K s`.

For `x ∈ K`, `(y*s) * x * (y*s)⁻¹ = y * (s*x*s⁻¹) * y⁻¹`; since `y` commutes with `x` (and hence
with `x⁻¹`), stripping `y` is exactly the operation `s*x*s⁻¹ ↦ x⁻¹`. -/
theorem invSet_mul_centralizer {X : Type*} [Group X] {K : Subgroup X} {y s : X}
    (hy : y ∈ Subgroup.centralizer (K : Set X)) :
    Work.GW2.invSet K (y * s) = Work.GW2.invSet K s := by
  ext x
  simp only [Work.GW2.invSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxK, hx⟩
    obtain hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy) x hxK
    refine ⟨hxK, ?_⟩
    have key : (y * s) * x * (y * s)⁻¹ = y * (s * x * s⁻¹) * y⁻¹ := by group
    have h1 : y * (s * x * s⁻¹) * y⁻¹ = x⁻¹ := by rw [← key]; exact hx
    have h2 : s * x * s⁻¹ = y⁻¹ * x⁻¹ * y := by rw [← h1]; group
    have hyinv : y⁻¹ * x * y = x := by
      rw [mul_assoc, hxy, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    rw [h2, h3, hyinv]
  · rintro ⟨hxK, hx⟩
    obtain hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy) x hxK
    refine ⟨hxK, ?_⟩
    have hyx : y * x * y⁻¹ = x := by rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
    have key : (y * s) * x * (y * s)⁻¹ = y * (s * x * s⁻¹) * y⁻¹ := by group
    rw [key, hx]
    have hconj : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
    rw [hconj, hyx]

end Work.CORE4.InvSet
