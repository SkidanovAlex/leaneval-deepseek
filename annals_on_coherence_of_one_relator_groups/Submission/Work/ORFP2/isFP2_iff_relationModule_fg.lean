/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `FP₂` over `k` iff the relation module is finitely generated (node N11 of ORFP2)

Let `φ : F(Fin n) →* G` be a surjection from a finitely generated free group onto `G`.
Over the group ring `k[G]` there is a right exact sequence

  `k[G]ⁿ --relMap--> k[G] --augmentation--> k`,

whose image is the augmentation ideal `augIdeal k G` and whose kernel is by definition the
relation module `relationModule k G φ`.  Hence

  `0 → relationModule k G φ → k[G]ⁿ → augIdeal k G → 0`

is short exact, with `k[G]ⁿ` finitely generated free.  As a quotient of a finitely presented
module by a finitely generated submodule is finitely presented, and dually the kernel of a
surjection from a finitely generated module onto a finitely presented module is finitely
generated, we obtain

`IsFP2 k G ↔ (relationModule k G φ).FG`.

The mathematical content is that the images `φ xᵢ - 1` generate the augmentation ideal, which
is where the surjectivity of `φ` enters; that fact is
`Work.ORFP2.augIdeal_eq_span_of_surjective` (node N11's `augIdeal` bookkeeping) and is used
here.
-/
import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.augIdeal_eq_span_of_surjective

set_option autoImplicit false

namespace Work.ORFP2

open MonoidAlgebra

section RelationMap

variable (k : Type*) [CommRing k] (G : Type*) [Group G]

/-- `relMap k G φ x ∈ augIdeal k G`; no surjectivity is needed for this. -/
private lemma relMap_mem_augIdeal {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (x : Fin n →₀ MonoidAlgebra k G) : relMap k G φ x ∈ augIdeal k G := by
  have hle : LinearMap.range (relMap k G φ) ≤ augIdeal k G := by
    rw [range_relMap]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact single_sub_one_mem_augIdeal k G _
  exact hle ⟨x, rfl⟩

/-- The relation map of the presentation, with values restricted to the augmentation ideal. -/
private noncomputable def relMapAug {n : ℕ} (φ : FreeGroup (Fin n) →* G) :
    (Fin n →₀ MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] augIdeal k G :=
  (relMap k G φ).codRestrict (augIdeal k G) (relMap_mem_augIdeal k G φ)

/-- For a surjective `φ`, the restricted relation map is surjective: its range is the augmentation
ideal, since the elements `φ xᵢ - 1` generate it. -/
private lemma relMapAug_surjective {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hφ : Function.Surjective φ) : Function.Surjective (relMapAug k G φ) := by
  intro y
  have hy : (y : MonoidAlgebra k G) ∈ LinearMap.range (relMap k G φ) := by
    rw [range_relMap, ← augIdeal_eq_span_of_surjective k G (Fin n) φ hφ]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  show (relMap k G φ) x = (y : MonoidAlgebra k G)
  exact hx

/-- The kernel of the restricted relation map is the relation module. -/
private lemma ker_relMapAug {n : ℕ} (φ : FreeGroup (Fin n) →* G) :
    LinearMap.ker (relMapAug k G φ) = relationModule k G φ := by
  ext x
  simp only [LinearMap.mem_ker, relationModule, relMapAug]
  rw [Subtype.ext_iff, LinearMap.codRestrict_apply, Submodule.coe_zero]

end RelationMap

/-- **Bieri–Strebel criterion, `FP₂` form.**  For a surjection `φ` from a finitely generated free
group onto `G`, the group `G` is `FP₂` over `k` (i.e. the augmentation ideal of `k[G]` is a
finitely presented `k[G]`-module) if and only if the relation module of the presentation `φ` is a
finitely generated `k[G]`-module. -/
theorem isFP2_iff_relationModule_fg (k : Type*) [CommRing k] {n : ℕ} (G : Type*) [Group G]
    (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) :
    IsFP2 k G ↔ (relationModule k G φ).FG := by
  have hiff := Module.FinitePresentation.fg_ker_iff (R := MonoidAlgebra k G)
      (M := Fin n →₀ MonoidAlgebra k G) (N := augIdeal k G)
      (relMapAug k G φ) (relMapAug_surjective k G φ hφ)
  rw [ker_relMapAug] at hiff
  simpa [IsFP2] using hiff.symm

end Work.ORFP2
