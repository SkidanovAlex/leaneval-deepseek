import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.DvApriori.Band.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.Band.projOn_comp_jointProj`

The slot projections of `projOn` compose: if the slot set splits as `A ∪ J = {0,…,n−1}`
with `A`, `J` disjoint, and the flags are `U ⊆ A`, `R ⊆ J`, then projecting onto `J`
(with flags `R`) after projecting onto `A` (with flags `U`) is the joint sector
projection of the whole slot set with flags `R ∪ U`.

The proof is the slot algebra of `slotProd`: unfold both `projOn`s, concatenate the two
slot lists (`slotProd_append`), change the flags (`slotProd_congr` — on `J` the flag
`R ∪ U` is `R` since `U ⊆ A` and `A ∩ J = ∅`, and on `A` it is `U` since `R ⊆ J`),
permute the concatenation into `List.range n` (`slotProd_reorder`, legitimate because the
slot operators of distinct slots commute) and identify the result with `jointProj`
(`projOn_full` at the full slot set).
-/

namespace Work.BoseFixB2.DvApriori.Band

open Submission.BoseGases

theorem projOn_comp_jointProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A J U R : Finset ℕ}
    (hAJ : A ∪ J = Finset.range n) (hdisj : Disjoint A J)
    (hU : U ⊆ A) (hR : R ⊆ J) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Work.BoseFixB2.DvApriori.projOn ℓ J R (Work.BoseFixB2.DvApriori.projOn ℓ A U Φ)
      = Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ := by
  -- `A` and `J` are disjoint, in both directions.
  have hdAJ : ∀ a ∈ A, a ∉ J := fun a ha => Finset.disjoint_left.mp hdisj ha
  have hdJA : ∀ a ∈ J, a ∉ A := fun a ha => Finset.disjoint_right.mp hdisj ha
  -- On the slots of `A` the flag `R ∪ U` is `U`, and on the slots of `J` it is `R`.
  have hInA : ∀ j ∈ slotList n A, (j ∈ U ↔ j ∈ R ∪ U) := by
    intro j hj
    have hjA : j ∈ A := (mem_slotList.mp hj).2
    constructor
    · intro h; exact Finset.mem_union.mpr (Or.inr h)
    · intro h
      rcases Finset.mem_union.mp h with hR' | hU'
      · exact absurd (hR hR') (hdAJ j hjA)
      · exact hU'
  have hInJ : ∀ j ∈ slotList n J, (j ∈ R ↔ j ∈ R ∪ U) := by
    intro j hj
    have hjJ : j ∈ J := (mem_slotList.mp hj).2
    constructor
    · intro h; exact Finset.mem_union.mpr (Or.inl h)
    · intro h
      rcases Finset.mem_union.mp h with hR' | hU'
      · exact hR'
      · exact absurd (hU hU') (hdJA j hjJ)
  -- The two flag changes.
  have hinner : slotProd ℓ (slotList n A) U Φ
      = slotProd ℓ (slotList n A) (R ∪ U) Φ :=
    slotProd_congr (slotList n A) (fun j hj => slotList_lt hj) hInA Φ
  have houter : slotProd ℓ (slotList n J) R (slotProd ℓ (slotList n A) (R ∪ U) Φ)
      = slotProd ℓ (slotList n J) (R ∪ U) (slotProd ℓ (slotList n A) (R ∪ U) Φ) :=
    slotProd_congr (slotList n J) (fun j hj => slotList_lt hj) hInJ _
  -- Step 1: concatenate the two slot lists.
  have hstep1 : projOn ℓ J R (projOn ℓ A U Φ)
      = slotProd ℓ (slotList n J ++ slotList n A) (R ∪ U) Φ := by
    rw [projOn, projOn, hinner, houter]
    exact (slotProd_append ℓ (slotList n J) (slotList n A) (R ∪ U) Φ).symm
  -- The concatenation is exactly the full slot set `{0,…,n−1}`.
  have hset : ∀ j, j ∈ slotList n J ++ slotList n A ↔ j ∈ List.range n := by
    intro j
    constructor
    · intro h
      rcases List.mem_append.mp h with hJ | hA
      · exact List.mem_range.mpr (slotList_lt hJ)
      · exact List.mem_range.mpr (slotList_lt hA)
    · intro h
      have hjn : j < n := List.mem_range.mp h
      have hmem : j ∈ A ∨ j ∈ J := Finset.mem_union.mp (by rw [hAJ]; exact h)
      rcases hmem with hA | hJ
      · exact List.mem_append.mpr (Or.inr (mem_slotList.mpr ⟨hjn, hA⟩))
      · exact List.mem_append.mpr (Or.inl (mem_slotList.mpr ⟨hjn, hJ⟩))
  have hnd : (slotList n J ++ slotList n A).Nodup :=
    List.nodup_append.mpr ⟨slotList_nodup n J, slotList_nodup n A,
      fun _a ha _b hb hab => hdJA _ (mem_slotList.mp ha).2 (hab ▸ (mem_slotList.mp hb).2)⟩
  have hLt : ∀ j ∈ slotList n J ++ slotList n A, j < n := by
    intro j hj
    rcases List.mem_append.mp hj with h | h
    · exact slotList_lt h
    · exact slotList_lt h
  -- Step 2: the slot operators of distinct slots commute, so only the slot *set* matters.
  have hreorder : slotProd ℓ (slotList n J ++ slotList n A) (R ∪ U) Φ
      = slotProd ℓ (List.range n) (R ∪ U) Φ :=
    slotProd_reorder (L := slotList n J ++ slotList n A) (L' := List.range n) hℓ hnd
      List.nodup_range hLt (fun j hj => List.mem_range.mp hj) hset (R ∪ U) hΦ
  -- Step 3: on the full slot set the restricted projection is `jointProj`.
  have hfull : slotProd ℓ (List.range n) (R ∪ U) Φ = jointProj ℓ (R ∪ U) Φ := by
    have h := projOn_full (ℓ := ℓ) hℓ (R ∪ U) hΦ
    rwa [projOn, slotList_range] at h
  exact hstep1.trans (hreorder.trans hfull)

end Work.BoseFixB2.DvApriori.Band
