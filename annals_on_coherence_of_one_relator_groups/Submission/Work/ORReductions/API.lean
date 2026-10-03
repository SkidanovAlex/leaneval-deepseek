/-
Copyright (c) 2026 The contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N0: the public interface

The wrappers below give the design names of `ROUTE_LEAD.md`, §3 (N0) to the lemmas proved in
this directory.  A caller should import this file.
-/
import Submission.Work.ORReductions.Basic
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.FreeGroupGens.freeGens_one
import Submission.Work.ORReductions.FreeGroupGens.freeGens_of
import Submission.Work.ORReductions.FreeGroupGens.freeGens_inv
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mul_subset
import Submission.Work.ORReductions.FreeGroupGens.freeGens_finite
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_closure
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_closure_iff
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_range_map_iff
import Submission.Work.ORReductions.FreeGroupGens.freeGens_exists_injective_lift
import Submission.Work.ORReductions.PresentedGroup.presentedGroup_empty_equiv_freeGroup
import Submission.Work.ORReductions.PresentedGroup.presentedGroup_coprod_single
import Submission.Work.ORReductions.PresentedGroup.presentedGroup_single_equiv
import Submission.Work.ORReductions.PresentedGroup.presentedGroup_map_mk
import Submission.Work.ORReductions.Coherent.coherent_of_ringEquiv
import Submission.Work.ORReductions.Coherent.groupCoherent_of_mulEquiv
import Submission.Work.ORReductions.Coherent.groupCoherent_subgroup
import Submission.Work.ORReductions.Coherent.submodule_finitePresentation_of_fg
import Submission.Work.ORReductions.Coherent.submodule_fg_ker_of_coherent
import Submission.Work.ORReductions.Coherent.coherent_of_finite_subgroups
import Submission.Work.ORReductions.Coherent.coherent_of_finiteIndex
import Submission.Work.ORReductions.Coherent.coherent_of_subfield
import Submission.Work.ORReductions.Field.fg_charZero_field_embeds_complex
import Submission.Work.ORReductions.Coherent.ideal_map_finitePresentation_of_subgroup
import Submission.Work.ORReductions.Coherent.SubgroupRestriction
import Submission.Work.ORReductions.Coherent.restrictToSubgroup_subgroupAlgMap
import Submission.Work.ORReductions.Coherent.restrictToSubgroup_mul_subgroupAlgMap
import Submission.Work.ORReductions.OneRelator.oneRelator_freeFactor
import Submission.Work.ORReductions.OneRelator.groupCoherent_of_oneRelator_of_fg
import Submission.Work.ORReductions.OneRelator.coherent_of_oneRelator_of_fg

set_option autoImplicit false

/-! ### `FreeGroup.gens` API under the Mathlib names -/

namespace FreeGroup

theorem gens_one {α : Type*} : gens (1 : FreeGroup α) = ∅ :=
  Work.ORReductions.FreeGroupGens.freeGens_one

theorem gens_of {α : Type*} (a : α) : gens (of a) = {a} :=
  Work.ORReductions.FreeGroupGens.freeGens_of a

theorem gens_inv {α : Type*} (x : FreeGroup α) : gens x⁻¹ = gens x :=
  Work.ORReductions.FreeGroupGens.freeGens_inv x

theorem gens_mul_subset {α : Type*} (x y : FreeGroup α) : gens (x * y) ⊆ gens x ∪ gens y :=
  Work.ORReductions.FreeGroupGens.freeGens_mul_subset x y

theorem gens_finite {α : Type*} (x : FreeGroup α) : (gens x).Finite :=
  Work.ORReductions.FreeGroupGens.freeGens_finite x

theorem mem_closure_of_gens {α : Type*} (x : FreeGroup α) :
    x ∈ Subgroup.closure (of '' gens x) :=
  Work.ORReductions.FreeGroupGens.freeGens_mem_closure x

theorem mem_closure_iff {α : Type*} {S : Set α} (x : FreeGroup α) :
    x ∈ Subgroup.closure (of '' S) ↔ gens x ⊆ S :=
  Work.ORReductions.FreeGroupGens.freeGens_mem_closure_iff x

theorem mem_range_map_iff {α : Type*} {S : Set α} (x : FreeGroup α) :
    x ∈ Set.range (map (Subtype.val : S → α)) ↔ gens x ⊆ S :=
  Work.ORReductions.FreeGroupGens.freeGens_mem_range_map_iff x

theorem exists_injective_lift {α : Type*} (F : Finset (FreeGroup α)) :
    ∃ (n : ℕ) (φ : Fin n → α), Function.Injective φ ∧ ∀ x ∈ F, x ∈ Set.range (map φ) :=
  Work.ORReductions.FreeGroupGens.freeGens_exists_injective_lift F

end FreeGroup

/-! ### Coherence: invariance and the main transfers -/

namespace Ring.Coherent

theorem of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Ring.Coherent R → Ring.Coherent S :=
  Work.ORReductions.Coherent.coherent_of_ringEquiv e

theorem of_finite_subgroups (G : Type*) [Group G] (K : Type*) [Field K]
    (h : ∀ (s : Finset G), ∃ (H : Subgroup G), (s : Set G) ⊆ (H : Set G) ∧
      Ring.Coherent (MonoidAlgebra K H)) :
    Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORReductions.Coherent.coherent_of_finite_subgroups G K h

theorem of_finiteIndex (G : Type*) [Group G] (K : Type*) [Field K]
    (H : Subgroup G) (hH : H.FiniteIndex) (h : Ring.Coherent (MonoidAlgebra K H)) :
    Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORReductions.Coherent.coherent_of_finiteIndex G K H hH h

theorem of_subfield (G : Type*) [Group G] (K : Type*) [Field K]
    (h : ∀ (S : Finset K), Ring.Coherent (MonoidAlgebra (Subfield.closure (S : Set K)) G)) :
    Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORReductions.Coherent.coherent_of_subfield G K h

end Ring.Coherent

namespace Group.Coherent

theorem of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Group.Coherent G → Group.Coherent H :=
  Work.ORReductions.Coherent.groupCoherent_of_mulEquiv e

theorem subgroup {G : Type*} [Group G] (H : Subgroup G) :
    Group.Coherent G → Group.Coherent H :=
  Work.ORReductions.Coherent.groupCoherent_subgroup H

end Group.Coherent

/-! ### The field reduction -/

/-- Every subfield of a field of characteristic zero generated by a finite set embeds into `ℂ`. -/
theorem fg_charZero_field_embeds_complex (K : Type*) [Field K] [CharZero K] (S : Finset K) :
    Nonempty ((Subfield.closure (S : Set K)) →+* ℂ) :=
  Work.ORReductions.Field.fg_charZero_field_embeds_complex K S

/-! ### The retraction of `K[G]` onto `K[H]` -/

/-- `restrictToSubgroup H K` is the additive retraction of `K[G]` onto `K[H]`. -/
theorem restrictToSubgroup_subgroupAlgMap {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (t : MonoidAlgebra K H) :
    Work.ORReductions.Coherent.restrictToSubgroup H K
      (Work.ORReductions.subgroupAlgMap H K t) = t :=
  Work.ORReductions.Coherent.restrictToSubgroup_subgroupAlgMap H K t

/-- `restrictToSubgroup H K` is right `K[H]`-linear. -/
theorem restrictToSubgroup_mul_subgroupAlgMap {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (b : MonoidAlgebra K G) (t : MonoidAlgebra K H) :
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (b * Work.ORReductions.subgroupAlgMap H K t) =
      Work.ORReductions.Coherent.restrictToSubgroup H K b * t :=
  Work.ORReductions.Coherent.restrictToSubgroup_mul_subgroupAlgMap H K b t

/-! ### The one-relator reduction -/

theorem oneRelator_fg_reduction (G : Type*) [Group G] (hG : Group.OneRelator G) (s : Finset G) :
    ∃ (n : ℕ) (r : FreeGroup (Fin n)) (H : Subgroup G), (s : Set G) ⊆ (H : Set G) ∧
      Nonempty (PresentedGroup {r} ≃* H) := by
  obtain ⟨n, r, H, T, hs, h1, h2⟩ :=
    Work.ORReductions.OneRelator.oneRelator_freeFactor G hG s
  exact ⟨n, r, H, hs, h1⟩

theorem oneRelator_freeFactor (G : Type*) [Group G] (hG : Group.OneRelator G) (s : Finset G) :
    ∃ (n : ℕ) (r : FreeGroup (Fin n)) (H T : Subgroup G), (s : Set G) ⊆ (H : Set G) ∧
      Nonempty (PresentedGroup {r} ≃* H) ∧ Nonempty (G ≃* Monoid.Coprod H T) :=
  Work.ORReductions.OneRelator.oneRelator_freeFactor G hG s

/-- The group half of Theorem 1.1 reduces to finitely generated one-relator groups. -/
theorem Group.Coherent.of_oneRelator_of_fg (G : Type*) [Group G] (hG : Group.OneRelator G)
    (h : ∀ (n : ℕ) (r : FreeGroup (Fin n)), Group.Coherent (PresentedGroup {r})) :
    Group.Coherent G :=
  Work.ORReductions.OneRelator.groupCoherent_of_oneRelator_of_fg G hG h

/-- The ring half of Theorem 1.1 reduces to finitely generated one-relator groups. -/
theorem Ring.Coherent.of_oneRelator_of_fg (G : Type*) [Group G] (K : Type*) [Field K]
    (hG : Group.OneRelator G)
    (h : ∀ (n : ℕ) (r : FreeGroup (Fin n)), Ring.Coherent (MonoidAlgebra K (PresentedGroup {r}))) :
    Ring.Coherent (MonoidAlgebra K G) :=
  Work.ORReductions.OneRelator.coherent_of_oneRelator_of_fg G K hG h

/-- `K[G]` free over `K[H]` on a coset transversal: the extension of a finitely presented ideal of
`K[H]` to `K[G]` is finitely presented. -/
theorem ideal_map_finitePresentation_of_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (K : Type*) [Field K] (I : Ideal (MonoidAlgebra K H))
    (hI : Module.FinitePresentation (MonoidAlgebra K H) I) :
    Module.FinitePresentation (MonoidAlgebra K G)
      (Ideal.map (Work.ORReductions.subgroupAlgMap H K) I) :=
  Work.ORReductions.Coherent.ideal_map_finitePresentation_of_subgroup H K I hI
