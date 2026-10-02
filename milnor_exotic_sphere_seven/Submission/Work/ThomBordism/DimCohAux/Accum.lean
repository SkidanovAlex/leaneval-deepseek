/-
# The accumulation of the cohomological dimension bound over a finite cover

This file contains the two Mayer–Vietoris-shaped steps that turn the *local* vanishing of the
singular cohomology of a charted space (`singCoh_vanishing_open_subset_chart`, in `Basic.lean`)
into the *global* statement used by `Work.ThomBordism.dimCohVanishingCharted`:

* `subsingleton_singCoh_union` — if `U`, `V` are open, the cohomology of `U` and `V` vanishes in
  degree `m + 1` and that of `U ∩ V` vanishes in degree `m`, then the cohomology of `U ∪ V`
  vanishes in degree `m + 1`.  This is the vanishing form of the Mayer–Vietoris sequence, in the
  "union of two open sets" shape.
* `subsingleton_singCoh_biUnion` — the accumulation over a finite family of open sets: if each
  family member has vanishing cohomology above `N` and every "member against a union of the
  others" intersection has vanishing cohomology in degrees `≥ N`, then every finite union of
  members has vanishing cohomology above `N`.

The induction in `subsingleton_singCoh_biUnion` is on the finite family; each step is
`subsingleton_singCoh_union` applied to the new member and the union of the old ones, the
intersection hypothesis being supplied by `hinter`.
-/

import Mathlib
import Mathlib
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.euclidean_open_cohomology_vanishing
import Submission.Work.ThomBordism.DimVanishingCommon
import Submission.Work.ThomBordism.DimCohAux.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism
noncomputable section

/-- **The Mayer–Vietoris step, union form.** -/
theorem subsingleton_singCoh_union {α : Type} [TopologicalSpace α] (U V : Set α)
    (hU : IsOpen U) (hV : IsOpen V) (m : ℕ)
    (hUm : Subsingleton (singCoh (TopCat.of ↥U) (m + 1)))
    (hVm : Subsingleton (singCoh (TopCat.of ↥V) (m + 1)))
    (hI : Subsingleton (singCoh (TopCat.of ↥(U ∩ V)) m)) :
    Subsingleton (singCoh (TopCat.of ↥(U ∪ V)) (m + 1)) := by
  have hcov : (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) ∪ (Subtype.val ⁻¹' V : Set ↥(U ∪ V))
      = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rcases x.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hUm' : Subsingleton (singCoh (TopCat.of ↥(Subtype.val ⁻¹' U : Set ↥(U ∪ V))) (m + 1)) :=
    subsingleton_singCoh_preimage_subtype_val (S := U) (T := U ∪ V) Set.subset_union_left (m + 1)
      hUm
  have hVm' : Subsingleton (singCoh (TopCat.of ↥(Subtype.val ⁻¹' V : Set ↥(U ∪ V))) (m + 1)) :=
    subsingleton_singCoh_preimage_subtype_val (S := V) (T := U ∪ V) Set.subset_union_right (m + 1)
      hVm
  have hI' : Subsingleton
      (singCoh (TopCat.of ↥((Subtype.val ⁻¹' U : Set ↥(U ∪ V)) ∩ Subtype.val ⁻¹' V)) m) := by
    have h1 : (Subtype.val ⁻¹' (U ∩ V) : Set ↥(U ∪ V))
        = (Subtype.val ⁻¹' U : Set ↥(U ∪ V)) ∩ Subtype.val ⁻¹' V := rfl
    rw [← h1]
    exact subsingleton_singCoh_preimage_subtype_val (S := U ∩ V) (T := U ∪ V)
      (fun x hx => Or.inl hx.1) m hI
  exact subsingleton_singCoh_of_cover_two _ _ (hU.preimage continuous_subtype_val)
    (hV.preimage continuous_subtype_val) hcov m hUm' hVm' hI'

/-- **The accumulation over a finite family.** -/
theorem subsingleton_singCoh_biUnion {M : TopCat} {ι : Type} (A : ι → Set M) (N : ℕ)
    (hAopen : ∀ i, IsOpen (A i))
    (hpiece : ∀ i, ∀ k, N < k → Subsingleton (singCoh (TopCat.of ↥(A i)) k))
    (hinter : ∀ (u : Finset ι) (i : ι), i ∉ u → ∀ k, N ≤ k →
      Subsingleton (singCoh (TopCat.of ↥(A i ∩ ⋃ j ∈ (u : Set ι), A j)) k)) :
    ∀ (u : Finset ι) (k : ℕ), N < k →
      Subsingleton (singCoh (TopCat.of ↥(⋃ i ∈ (u : Set ι), A i)) k) := by
  classical
  intro u
  induction u using Finset.induction with
  | empty =>
      intro k hk
      rw [show (⋃ j ∈ ((∅ : Finset ι) : Set ι), A j) = (∅ : Set M) by simp]
      exact ModuleCat.subsingleton_of_isZero (Work.Cohomology.isZero_homology_of_isZero_X_cochain k
        (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of (∅ : Set M)) k))
  | insert z u hzu ih =>
      intro k hk
      have hins : (⋃ j ∈ (((insert z u) : Finset ι) : Set ι), A j)
          = A z ∪ ⋃ j ∈ (u : Set ι), A j := by
        rw [Finset.coe_insert, Set.biUnion_insert]
      have hmain := subsingleton_singCoh_union (A z) (⋃ j ∈ (u : Set ι), A j) (hAopen z)
        (isOpen_biUnion (fun j _ => hAopen j)) (k - 1)
        (hpiece z (k - 1 + 1) (by omega)) (ih (k - 1 + 1) (by omega))
        (hinter u z hzu (k - 1) (by omega))
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hmain
      rw [← hins] at hmain
      exact hmain

end
end Work.ThomBordism
