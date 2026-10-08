/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Galois decomposition of `PΓL(2,F) = PGL(2,F) · PΣL(2,F)`

For a field `F` (with `DecidableEq F`), with `P1 F = ℙ¹(F)`:

* `galHom F` is injective: a field automorphism is determined by its action on `ℙ¹(F)`;
* `pglImage F ⊓ galSub F = ⊥`;
* `galSub F` normalizes `pglImage F`;
* every element of `pglImage F ⊔ galSub F = PΓL(2,F)` is a product `x * τ` with
  `x ∈ pglImage F` and `τ ∈ galSub F`;
* `PΓL(2,F)` normalizes `pslImage F`.

The two computational ingredients are the compatibility lemma
`OnePoint.map_smul` (a field automorphism conjugates the Möbius action of a matrix into the
Möbius action of the image matrix) and the fact that `toPGL` has range the `SL`-part of `PGL`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.AUTL2.Galois.decomposition

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint
open Pointwise

namespace Work.AUTL2.Galois

open Work.AUTL2

/-- If `K` normalizes `H`, then every element of `H ⊔ K` is of the form `x * τ` with `x ∈ H`
and `τ ∈ K`. -/
private lemma exists_mul_of_mem_sup {G : Type*} [Group G] (H K : Subgroup G)
    (h : K ≤ Subgroup.normalizer H) {π : G} (hπ : π ∈ H ⊔ K) :
    ∃ x ∈ H, ∃ τ ∈ K, π = x * τ := by
  classical
  have hconj : ∀ k ∈ K, ∀ y ∈ H, k * y * k⁻¹ ∈ H := Subgroup.le_normalizer_iff.mp h
  set S : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      mul_mem' := by
        rintro a b ⟨h1, h1H, k1, k1K, rfl⟩ ⟨h2, h2H, k2, k2K, rfl⟩
        refine ⟨h1 * (k1 * h2 * k1⁻¹), mul_mem h1H (hconj k1 k1K h2 h2H), k1 * k2,
          mul_mem k1K k2K, ?_⟩
        group
      one_mem' := ⟨1, one_mem H, 1, one_mem K, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨h1, h1H, k1, k1K, rfl⟩
        have hmem' : k1⁻¹ * h1⁻¹ * k1 ∈ H := by
          simpa using hconj k1⁻¹ (inv_mem k1K) h1⁻¹ (inv_mem h1H)
        refine ⟨k1⁻¹ * h1⁻¹ * k1, hmem', k1⁻¹, inv_mem k1K, ?_⟩
        group } with hSdef
  have hHS : H ≤ S := fun x hx => ⟨x, hx, 1, one_mem K, mul_one x⟩
  have hKS : K ≤ S := fun x hx => ⟨1, one_mem H, x, hx, one_mul x⟩
  have hsub : H ⊔ K ≤ S := sup_le hHS hKS
  obtain ⟨x, hxH, τ, hτK, hxτ⟩ := hsub hπ
  exact ⟨x, hxH, τ, hτK, hxτ.symm⟩

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## Matrix-level computations -/


/-! ## The five assertions -/


end Work.AUTL2.Galois
