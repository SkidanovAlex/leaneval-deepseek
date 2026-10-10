import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Sums over a complete set of left-coset representatives (no normality)

For an arbitrary subgroup `U ≤ G` (no normality!), `G ⧸ U` is the type of left cosets
`Quotient (QuotientGroup.leftRel U)`; it carries no group structure, but it does carry the canonical
section `Quotient.out` with `Quotient.out_eq'`.

This file builds the small piece of "missing Mathlib" that the degree-`2` and degree-`3` transfer
arguments need, and that the tree currently avoids by *assuming* `[U.Normal]` (see
`Work.SSGRoute.finite_coind`, `PT/h2loc_coboundaries_of_coboundaries_subgroup`):

* `IsCosetReps U T` — `T : Finset G` meets every left coset `xU` in exactly one point;
* `sum_eq_of_isCosetReps` — **the sum over such a `T` is independent of the choice of `T`**, for a
  summand `f` invariant under right multiplication by `U` (`f (x * u) = f x` for `u ∈ U`);
* `isCosetReps_image_mul` — left translation sends coset representatives to coset representatives;
* `exists_isCosetReps` / `exists_isCosetReps_of_finiteIndex` — such a `T` exists as soon as
  `G ⧸ U` is finite (in particular for `[U.FiniteIndex]`).

Nothing here uses normality of `U`, and nothing here uses finiteness of `G`.
-/

namespace Work.SSGRoute.EulerSymm

open Classical

variable {G M : Type*} [Group G] [AddCommGroup M]

/-- **`T` is a complete set of left-coset representatives for `U ≤ G`**: every `x : G` has a
unique `t ∈ T` with `x⁻¹ * t ∈ U`, i.e. `t ∈ xU`. -/
def IsCosetReps (U : Subgroup G) (T : Finset G) : Prop :=
  ∀ x : G, ∃! t : G, t ∈ T ∧ x⁻¹ * t ∈ U

/-- **The sum over a complete set of left-coset representatives is independent of the choice of
representatives**, for a summand invariant under right multiplication by `U`.

Both sides sum the same coset-invariant function over the same finite set of cosets; the proof is
the canonical bijection `t ↦` (the unique representative in `T'` of the coset `tU`), which
preserves `f` because that representative is `t * u` for some `u ∈ U`. -/
theorem sum_eq_of_isCosetReps {U : Subgroup G} {T T' : Finset G}
    (hT : IsCosetReps U T) (hT' : IsCosetReps U T') (f : G → M)
    (hf : ∀ (x : G) (u : U), f (x * (u : G)) = f x) :
    ∑ t ∈ T, f t = ∑ t ∈ T', f t := by
  classical
  have hex : ∀ t : G, ∃ t' : G, t' ∈ T' ∧ t⁻¹ * t' ∈ U := fun t => (hT' t).exists
  let i : G → G := fun t => Classical.choose (hex t)
  have hi_mem : ∀ t : G, i t ∈ T' := fun t => (Classical.choose_spec (hex t)).1
  have hi_rel : ∀ t : G, t⁻¹ * i t ∈ U := fun t => (Classical.choose_spec (hex t)).2
  have hi_eq : ∀ t : G, f (i t) = f t := by
    intro t
    have h : t * ((⟨t⁻¹ * i t, hi_rel t⟩ : U) : G) = i t := by
      rw [Subtype.coe_mk, mul_inv_cancel_left]
    rw [← h, hf t ⟨t⁻¹ * i t, hi_rel t⟩]
  refine Finset.sum_bij (fun t _ => i t) (fun t _ => hi_mem t) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ heq
    have e₁ : (i t₁)⁻¹ * t₁ ∈ U := by
      simpa only [mul_inv_rev, inv_inv] using U.inv_mem_iff.mpr (hi_rel t₁)
    have e₂ : (i t₁)⁻¹ * t₂ ∈ U := by
      rw [heq]
      simpa only [mul_inv_rev, inv_inv] using U.inv_mem_iff.mpr (hi_rel t₂)
    exact (hT (i t₁)).unique ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
  · intro t' ht'
    obtain ⟨t, htT, htrel⟩ := (hT t').exists
    refine ⟨t, htT, ?_⟩
    have hrel' : t⁻¹ * t' ∈ U := by
      simpa only [mul_inv_rev, inv_inv] using U.inv_mem_iff.mpr htrel
    exact (hT' t).unique ⟨hi_mem t, hi_rel t⟩ ⟨ht', hrel'⟩
  · intro t _
    exact (hi_eq t).symm

/-- **Left translation preserves coset representatives.**  If `T` meets every left coset in exactly
one point, so does `g • T = {g * t : t ∈ T}`. -/
theorem isCosetReps_image_mul {U : Subgroup G} {T : Finset G} (hT : IsCosetReps U T) (g : G) :
    IsCosetReps U (T.image (fun t => g * t)) := by
  classical
  intro x
  obtain ⟨t, ht, huniq⟩ := hT (g⁻¹ * x)
  refine ⟨g * t, ⟨Finset.mem_image.mpr ⟨t, ht.1, rfl⟩, ?_⟩, ?_⟩
  · have h : x⁻¹ * (g * t) = (g⁻¹ * x)⁻¹ * t := by group
    rw [h]
    exact ht.2
  · intro y hy
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy.1
    have hrel : (g⁻¹ * x)⁻¹ * t' ∈ U := by
      have h : x⁻¹ * (g * t') = (g⁻¹ * x)⁻¹ * t' := by group
      rw [← h]
      exact hy.2
    rw [huniq t' ⟨ht', hrel⟩]

/-- A complete set of left-coset representatives exists as soon as the quotient `G ⧸ U` is
finite. -/
theorem exists_isCosetReps (U : Subgroup G) [Finite (G ⧸ U)] :
    ∃ T : Finset G, IsCosetReps U T := by
  classical
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (Quotient.out (s := QuotientGroup.leftRel U)), fun x => ?_⟩
  refine ⟨Quotient.out (Quotient.mk'' (s₁ := QuotientGroup.leftRel U) x), ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · rw [← QuotientGroup.leftRel_apply]
    exact Quotient.exact' (Quotient.out_eq' (Quotient.mk'' (s₁ := QuotientGroup.leftRel U) x)).symm
  · intro y hy
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy.1
    have hrel : QuotientGroup.leftRel U x q.out := by
      rw [QuotientGroup.leftRel_apply]
      exact hy.2
    have hq : q = Quotient.mk'' (s₁ := QuotientGroup.leftRel U) x := by
      rw [← Quotient.out_eq' q]
      exact (Quotient.sound' hrel).symm
    rw [hq]

/-- A complete set of left-coset representatives exists for any finite-index subgroup. -/
theorem exists_isCosetReps_of_finiteIndex (U : Subgroup G) [U.FiniteIndex] :
    ∃ T : Finset G, IsCosetReps U T := by
  haveI := Subgroup.finiteIndex_iff_finite_quotient.mp ‹U.FiniteIndex›
  exact exists_isCosetReps U

end Work.SSGRoute.EulerSymm

namespace Work.SSGRoute.EulerSymm

open Classical

variable {G : Type*} [Group G]

/-- **A complete set of left-coset representatives has `U.index` elements.** -/
theorem card_eq_index_of_isCosetReps (U : Subgroup G) [Finite (G ⧸ U)] {T : Finset G}
    (hT : IsCosetReps U T) : T.card = U.index := by
  classical
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  have hinj : ∀ t₁ ∈ T, ∀ t₂ ∈ T,
      Quotient.mk'' (s₁ := QuotientGroup.leftRel U) t₁
        = Quotient.mk'' (s₁ := QuotientGroup.leftRel U) t₂ → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ heq
    have hrel : t₁⁻¹ * t₂ ∈ U := by
      rw [← QuotientGroup.leftRel_apply]
      exact Quotient.exact' heq
    exact (hT t₁).unique ⟨h₁, by rw [inv_mul_cancel]; exact U.one_mem⟩ ⟨h₂, hrel⟩
  have hsurj : ∀ q : G ⧸ U, ∃ t ∈ T, Quotient.mk'' (s₁ := QuotientGroup.leftRel U) t = q := by
    intro q
    obtain ⟨t, ht, hrel⟩ := (hT (Quotient.out q)).exists
    refine ⟨t, ht, ?_⟩
    rw [← Quotient.out_eq' q]
    exact (Quotient.sound' (by rw [QuotientGroup.leftRel_apply]; exact hrel)).symm
  have himg : T.image (fun t => Quotient.mk'' (s₁ := QuotientGroup.leftRel U) t)
      = (Finset.univ : Finset (G ⧸ U)) := by
    refine Finset.eq_univ_iff_forall.mpr (fun q => ?_)
    obtain ⟨t, ht, hq⟩ := hsurj q
    exact Finset.mem_image.mpr ⟨t, ht, hq⟩
  have hcard : (T.image (fun t => Quotient.mk'' (s₁ := QuotientGroup.leftRel U) t)).card = T.card :=
    Finset.card_image_of_injOn (fun a ha b hb h => hinj a ha b hb h)
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← hcard, himg, Finset.card_univ]
  rfl

end Work.SSGRoute.EulerSymm
