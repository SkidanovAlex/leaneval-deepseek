import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseFixB2.Sector.aQ_sym_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.slotProd` — slot projections over an arbitrary slot list

`slotProd ℓ L S Φ` applies, for each entry `j` of the slot list `L` (in order, the
*last* entry first), the slot operator `aQ ℓ j` if `j ∈ S` and `aP ℓ j` if `j ∉ S`.
It is `blockOpL ℓ (L.map (fun j => (j, decide (j ∈ S)))) Φ`, i.e. the corpus's
iterated list operator with the flags read off from `S`.

The point of this file is that the *free* slots of the band analysis in
`potBand_secProj_v3` are an arbitrary finite set (the complement of the interaction
slots), which `blockOp` (slots `0,…,n−1`) cannot address directly.  The lemmas proved
here (and in the sibling files of this directory) are the projection algebra of
`slotProd`: it is self-adjoint, idempotent, its patterns resolve the identity, distinct
patterns are orthogonal, and the paired sum collapses — the collapse being the
analytic content of the band identities.

## The interface

* `slotProd` — the definition.
* `slotProd_nil`, `slotProd_cons`, `slotProd_append` — the recursion.
* `slotProd_congr` — the flags only matter on the slots of the list.
* `slotProd_reorder` — the value depends only on the *set* of slots (operators of
  distinct slots commute).
* `slotProd_continuous` — continuity is preserved.

The remaining statements (self-adjointness, idempotence, resolution, orthogonality,
the paired sum, and the splitting of `jointProj` into a list part and its complement)
are proved in the sibling files.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-- **The slot product of a list of slots.**  For a list `L` of slot indices and a set
`S` of slots, `slotProd ℓ L S Φ` is the composition, over the entries of `L` (the last
entry applied first), of the slot operators `aQ ℓ j` (if `j ∈ S`) and `aP ℓ j` (if
`j ∉ S`).  Entries `j ≥ n` are ignored (`blockOpL`'s convention). -/
noncomputable def slotProd (ℓ : ℝ) {n : ℕ} (L : List ℕ) (S : Finset ℕ)
    (Φ : X n → ℝ) : X n → ℝ :=
  Work.BoseFixB2.Sector.blockOpL ℓ (L.map (fun j => (j, decide (j ∈ S)))) Φ

@[simp] lemma slotProd_nil (ℓ : ℝ) {n : ℕ} (S : Finset ℕ) (Φ : X n → ℝ) :
    slotProd ℓ ([] : List ℕ) S Φ = Φ := rfl

/-- The recursion: the *head* of the list is applied last. -/
lemma slotProd_cons {ℓ : ℝ} {n j : ℕ} (hj : j < n) (L : List ℕ) (S : Finset ℕ)
    (Φ : X n → ℝ) :
    slotProd ℓ (j :: L) S Φ
      = (if j ∈ S then aQ ℓ ⟨j, hj⟩ else aP ℓ ⟨j, hj⟩) (slotProd ℓ L S Φ) := by
  unfold slotProd
  rw [List.map_cons, Work.BoseFixB2.Sector.blockOpL_cons_of_lt hj]
  by_cases h : j ∈ S <;> simp [Work.BoseFixB2.Sector.slotOp, h]

/-- Concatenation of the slot lists composes the operators. -/
lemma slotProd_append (ℓ : ℝ) {n : ℕ} (L₁ L₂ : List ℕ) (S : Finset ℕ) (Φ : X n → ℝ) :
    slotProd ℓ (L₁ ++ L₂) S Φ = slotProd ℓ L₁ S (slotProd ℓ L₂ S Φ) := by
  unfold slotProd
  rw [List.map_append, Work.BoseFixB2.Sector.blockOpL_append]

/-- The value of `slotProd` depends on `S` only through `S ∩ L`. -/
lemma slotProd_congr {ℓ : ℝ} {n : ℕ} (L : List ℕ) {S T : Finset ℕ}
    (hLt : ∀ j ∈ L, j < n) (h : ∀ j ∈ L, (j ∈ S ↔ j ∈ T)) (Φ : X n → ℝ) :
    slotProd ℓ L S Φ = slotProd ℓ L T Φ := by
  induction L with
  | nil => rfl
  | cons j L ih =>
      rw [slotProd_cons (hLt j (by simp)) L S Φ, slotProd_cons (hLt j (by simp)) L T Φ,
        ih (fun k hk => hLt k (List.mem_cons_of_mem _ hk))
          (fun k hk => h k (List.mem_cons_of_mem _ hk))]
      have hj := h j (by simp)
      by_cases hmem : j ∈ S
      · rw [if_pos hmem, if_pos (hj.mp hmem)]
      · rw [if_neg hmem, if_neg (fun hc => hmem (hj.mpr hc))]

/-- **Reordering.**  The slot product depends only on the *set* of slots: slot operators
of distinct slots commute (`blockOpL_congr_set`). -/
lemma slotProd_reorder {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {L L' : List ℕ} (hnd : L.Nodup) (hnd' : L'.Nodup)
    (hLt : ∀ j ∈ L, j < n) (hLt' : ∀ j ∈ L', j < n) (h : ∀ j, j ∈ L ↔ j ∈ L')
    (S : Finset ℕ) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    slotProd ℓ L S Φ = slotProd ℓ L' S Φ := by
  have hnd1 : ((L.map (fun j => (j, decide (j ∈ S)))).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnd
  have hnd2 : ((L'.map (fun j => (j, decide (j ∈ S)))).map Prod.fst).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnd'
  have hlt1 : ∀ p ∈ L.map (fun j => (j, decide (j ∈ S))), p.1 < n := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact hLt j hj
  have hset : ∀ p : ℕ × Bool,
      p ∈ L.map (fun j => (j, decide (j ∈ S))) ↔
        p ∈ L'.map (fun j => (j, decide (j ∈ S))) := by
    intro p
    constructor
    · intro hp
      rw [List.mem_map] at hp ⊢
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨j, (h j).mp hj, rfl⟩
    · intro hp
      rw [List.mem_map] at hp ⊢
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨j, (h j).mpr hj, rfl⟩
  exact Work.BoseFixB2.Sector.blockOpL_congr_set (ℓ := ℓ) (N := n) hℓ _ _ hnd1 hnd2 hlt1 hset hΦ

/-- `slotProd` preserves continuity. -/
lemma slotProd_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (L : List ℕ) (S : Finset ℕ)
    {Φ : X n → ℝ} (hΦ : Continuous Φ) : Continuous (slotProd ℓ L S Φ) :=
  Work.BoseFixB2.Sector.continuous_blockOpL hℓ _ hΦ

end

end Work.BoseFixB2.DvApriori
