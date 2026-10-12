import Mathlib.Data.Finset.Card
import Submission.Work.BoseKinLoc.Sector.fibre_defs_v3

/-!
# `Work.BoseKinLoc.Sector.slotPermDefs` — the slot permutation of a slot set

For a slot set `S : Finset (Fin N)` and a permutation `σ : Equiv.Perm (Fin S.card)` of the
`|S|` slots, this file defines the permutation of `Fin N` that acts on the slots of `S` by
`σ` (transported along the canonical order isomorphism `slotIso S`) and fixes every particle
outside `S`:

* `slotPermIn S σ : Equiv.Perm (SlotIn N S)` — the transported permutation of the slots of `S`,
  characterised by `slotIso S (slotPermIn S σ i) = σ (slotIso S i)`;
* `slotPerm S σ : Equiv.Perm (Fin N)` — its extension by the identity off `S`, built from the
  splitting `Fin N ≃ SlotIn N S ⊕ SlotOut N S` (`Equiv.Set.sumCompl`), with the two evaluation
  rules `slotPerm_apply_of_mem` (on `S` it is `slotPermIn S σ`) and `slotPerm_apply_of_notMem`
  (off `S` it is the identity).

This is the permutation appearing in the symmetry statement for the fibre states
(`fibState_permInvariant`).
-/

noncomputable section

namespace Work.BoseKinLoc.Sector

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The permutation of the slots of `S` induced by a permutation of `Fin |S|`** along the
canonical order isomorphism `slotIso S`. -/
noncomputable def slotPermIn {N : ℕ} (S : Finset (Fin N)) (σ : Equiv.Perm (Fin S.card)) :
    Equiv.Perm (Work.PerSector.SlotIn N S) :=
  ((slotIso S).trans σ).trans (slotIso S).symm

/-- The defining property of `slotPermIn`: transported along `slotIso S` it is `σ`. -/
theorem slotIso_slotPermIn {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    (i : Work.PerSector.SlotIn N S) :
    slotIso S (slotPermIn S σ i) = σ (slotIso S i) := by
  simp [slotPermIn]

/-- The inverse of `slotPermIn`, transported along `slotIso S`, is `σ.symm`. -/
theorem slotIso_slotPermIn_symm {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    (i : Work.PerSector.SlotIn N S) :
    slotIso S ((slotPermIn S σ).symm i) = σ.symm (slotIso S i) := by
  have h := slotIso_slotPermIn σ ((slotPermIn S σ).symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

/-- **The permutation of `Fin N` induced by a permutation of the slots of `S`**: it acts on the
slots of `S` as `slotPermIn S σ` and fixes every particle outside `S`. -/
noncomputable def slotPerm {N : ℕ} (S : Finset (Fin N)) (σ : Equiv.Perm (Fin S.card)) :
    Equiv.Perm (Fin N) :=
  (Equiv.Set.sumCompl (S : Set (Fin N))).symm.trans
    ((Equiv.sumCongr (slotPermIn S σ) (Equiv.refl (Work.PerSector.SlotOut N S))).trans
      (Equiv.Set.sumCompl (S : Set (Fin N))))

/-- **`slotPerm` on the slots of `S`**: there it agrees with `slotPermIn S σ`. -/
theorem slotPerm_apply_of_mem {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    {i : Fin N} (hi : i ∈ S) :
    slotPerm S σ i = (slotPermIn S σ ⟨i, hi⟩).1 := by
  have h1 : (Equiv.Set.sumCompl (S : Set (Fin N))).symm i
      = Sum.inl (⟨i, hi⟩ : Work.PerSector.SlotIn N S) :=
    Equiv.Set.sumCompl_symm_apply (s := (S : Set (Fin N))) ⟨i, hi⟩
  rw [slotPerm, Equiv.trans_apply, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl]
  exact Equiv.Set.sumCompl_apply_inl (S : Set (Fin N)) (slotPermIn S σ ⟨i, hi⟩)

/-- **`slotPerm` off the slot set `S`**: there it is the identity. -/
theorem slotPerm_apply_of_notMem {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    {i : Fin N} (hi : i ∉ S) :
    slotPerm S σ i = i := by
  have h1 : (Equiv.Set.sumCompl (S : Set (Fin N))).symm i
      = Sum.inr (⟨i, hi⟩ : Work.PerSector.SlotOut N S) :=
    Equiv.Set.sumCompl_symm_apply_compl (s := (S : Set (Fin N))) ⟨i, hi⟩
  rw [slotPerm, Equiv.trans_apply, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inr]
  exact Equiv.Set.sumCompl_apply_inr (S : Set (Fin N)) ⟨i, hi⟩

/-- The slot permutation maps `S` onto itself. -/
theorem slotPerm_mem_iff {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    (i : Fin N) : slotPerm S σ i ∈ S ↔ i ∈ S := by
  by_cases hi : i ∈ S
  · rw [slotPerm_apply_of_mem σ hi]
    exact iff_of_true (slotPermIn S σ ⟨i, hi⟩).2 hi
  · rw [slotPerm_apply_of_notMem σ hi]

/-- `slotPerm` applied to a slot of `S`. -/
theorem slotPerm_apply_slotIn {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    (i : Work.PerSector.SlotIn N S) :
    slotPerm S σ i.1 = (slotPermIn S σ i).1 :=
  slotPerm_apply_of_mem σ i.2

/-- The inverse form of the defining property of `slotPerm` on `S`. -/
theorem slotPerm_symm_apply_of_mem {N : ℕ} {S : Finset (Fin N)} (σ : Equiv.Perm (Fin S.card))
    {i : Fin N} (hi : i ∈ S) :
    slotPerm S σ.symm i = ((slotPermIn S σ).symm ⟨i, hi⟩).1 :=
  slotPerm_apply_of_mem σ.symm hi

end Work.BoseKinLoc.Sector
