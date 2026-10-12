import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for FS's box-faithful excited count `cnPlusBoxInd`

`Work.UBBInputs8.cnPlusBoxInd a A volA Ψ = Σᵢ ∫_{abox N a}(Q_{A,i}Ψ)²` is FS's
excited-particle count with **FS's own box projection** `Q_{A,i} = 1_{A,i} − P_{A,i}`
(`boxQInd`, `eq:HBU`), i.e. the projection that — unlike the corpus's `aQ`/`boxQ` —
carries the box indicator.

The point of this module is the structural fact the FS grouping trick needs
(`Work.KinPSuperadd.SlotSplit`): `cnPlusBoxInd` is a **sum of one-particle forms over the
slots**, hence

    cnPlusBoxInd s A volA Φ
      = ∫_{w ∈ abox N₂ s} cnPlusBoxInd s A volA (fun u ↦ Φ (merge(u,w)))
      + ∫_{u ∈ abox N₁ s} cnPlusBoxInd s A volA (fun w ↦ Φ (merge(u,w))) ,

with the two slice integrals integrable.  This is the FS-faithful analogue of
`Work.KinPSuperadd.slotSplit_cnPlus`, and the missing input of the word-level grouping step
`Work.BoseFixB1S.sbKinSliceSplitW` (the `n₊(B)` half of the sliding small-box kinetic word).

## Proof

Slots of the first block: for `j : Fin N₁`, the slot `Fin.castAdd N₂ j` of a *merged*
configuration is the slot `j` of the frozen `w`-slice (`boxQInd_slice_fst`, from
`Function.update` commuting with `mergeBlock`, `mergeBlock_update_fst`).  So, with
`G x = (Q_{A,castAdd N₂ j}Ψ x)²`:

* `G` is `IntegrableOn (abox (N₁+N₂) s)` for continuous `Ψ` (`integrableOn_sq_boxQInd`,
  from `Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn` and the sup bound of `Ψ` on
  the compact box);
* the measure-preserving block split `aboxSplit_measurePreserving_restrict` carries `G` to
  the product of the block boxes, where Fubini (`aboxFubini_swapped`) turns `∫ G` into the
  iterated integral (`fubini_boxQInd_fst`) and integrates the `u`-variable out
  (`integrableOn_slice_boxQInd_fst`);
* summing over the slots of the two blocks with `Fin.sum_univ_add` and pulling the finite
  sum out of the `w`-integral (`integral_finsetSum`) gives the identity; the second block is
  symmetric (`boxQInd_slice_snd`, `fubini_boxQInd_snd`, `integrableOn_slice_boxQInd_snd`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB1S

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1  The one-slot slice identities

For a merged configuration `mergeBlock N₁ N₂ (u,w)`, the slot functional of a slot in the
first block is the corresponding slot functional of the `w`-slice, applied at `u`; and
symmetrically for the second block.  The proofs reduce to
`Function.update (merge(u,w)) (castAdd N₂ j) z = merge (update u j z, w)`
(`Work.KinPSuperadd.mergeBlock_update_fst`) inside the defining integral. -/

/-- **First-block slice of `boxPInd`.** -/
lemma boxPInd_slice_fst {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxPInd volA A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxPInd volA A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  have hInt : (∫ z in A, Φ (Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) z))
      = (∫ z in A, Φ (mergeBlock N1 N2 (Function.update u j z, w))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [← Work.KinPSuperadd.mergeBlock_update_fst]
  have hpt : (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) = u j := by simp [mergeBlock]
  simp only [Work.UBBInputs8.boxPInd, hInt, hpt]

/-- **Second-block slice of `boxPInd`.** -/
lemma boxPInd_slice_snd {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxPInd volA A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxPInd volA A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  have hInt : (∫ z in A, Φ (Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z))
      = (∫ z in A, Φ (mergeBlock N1 N2 (u, Function.update w j z))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [← Work.KinPSuperadd.mergeBlock_update_snd]
  have hpt : (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) = w j := by simp [mergeBlock]
  simp only [Work.UBBInputs8.boxPInd, hInt, hpt]

/-- **First-block slice of `boxQInd`**: FS's mean-free box projection of a slot of the
first block of a merged configuration is the projection of the frozen `w`-slice. -/
lemma boxQInd_slice_fst {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N1) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxQInd volA A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  have hP := boxPInd_slice_fst volA A Φ j u w
  have hpt : (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) = u j := by simp [mergeBlock]
  simp only [Work.UBBInputs8.boxQInd, hP, hpt]

/-- **Second-block slice of `boxQInd`.** -/
lemma boxQInd_slice_snd {N1 N2 : ℕ} (volA : ℝ) (A : Set ℝ³)
    (Φ : X (N1 + N2) → ℝ) (j : Fin N2) (u : X N1) (w : X N2) :
    Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))
      = Work.UBBInputs8.boxQInd volA A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  have hP := boxPInd_slice_snd volA A Φ j u w
  have hpt : (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) = w j := by simp [mergeBlock]
  simp only [Work.UBBInputs8.boxQInd, hP, hpt]

/-! ## 2  Integrability of one squared slot field on the ambient box -/

/-- The squared slot field `(Q_{A,i}Ψ)²` of a *continuous* state is integrable on
`abox N s`: continuity gives a bound `C` on the compact box, and
`Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn` converts it (with `A ⊆ acube s`)
into integrability. -/
lemma integrableOn_sq_boxQInd {N : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    {Φ : X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    IntegrableOn (fun x : X N => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2) (abox N s) volume := by
  obtain ⟨C, hC⟩ := (abox_compact N hs).exists_bound_of_continuousOn hΦ.continuousOn
  refine Work.SlotWord.integrableOn_boxQInd_sq_of_boundedOn hA hAsub hvolA hΦ.measurable
    (abs_nonneg C) (fun x hx => ?_) i
  exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_abs_self C)

/-! ## 3  Fubini over the block split for one slot field -/

/-- Restricted Fubini (`w`-outer) for the squared slot field of a *first-block* slot. -/
lemma fubini_boxQInd_fst {N1 N2 : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    (j : Fin N1) {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in abox (N1 + N2) s, (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
      = ∫ w in abox N2 s, ∫ u in abox N1 s,
          (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w))) ^ 2 :=
  (aboxFubini_swapped (N1 := N1) (N2 := N2) s
    (fun x => (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
    (integrableOn_sq_boxQInd hs hA hAsub hvolA hΦ _)).symm

/-- Restricted Fubini (`u`-outer) for the squared slot field of a *second-block* slot. -/
lemma fubini_boxQInd_snd {N1 N2 : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    (j : Fin N2) {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in abox (N1 + N2) s, (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2)
      = ∫ u in abox N1 s, ∫ w in abox N2 s,
          (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w))) ^ 2 :=
  (aboxFubini (N1 := N1) (N2 := N2) s
    (fun x => (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2)
    (integrableOn_sq_boxQInd hs hA hAsub hvolA hΦ _)).symm

/-! ## 4  Slice integrability of one slot field -/

/-- First-block slice integrability: as a function of the frozen second block, the
`u`-integral of a first-block slot field of the slice is integrable. -/
lemma integrableOn_slice_boxQInd_fst {N1 N2 : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    (j : Fin N1) {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun w : X N2 => ∫ u in abox N1 s,
      (Work.UBBInputs8.boxQInd volA A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2)
      (abox N2 s) volume := by
  have hGint : IntegrableOn
      (fun x : X (N1 + N2) => (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
      (abox (N1 + N2) s) volume :=
    integrableOn_sq_boxQInd hs hA hAsub hvolA hΦ (Fin.castAdd N2 j)
  have hmp := aboxSplit_measurePreserving_restrict N1 N2 s
  have hGe : Integrable
      (fun p : X N1 × X N2 =>
        (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 p)) ^ 2)
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    apply (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding).mp
    refine hGint.congr ?_
    filter_upwards with x
    simp [Function.comp_apply, blockSplitEquiv_apply, mergeBlock_eq]
  refine (hGe.integral_prod_right).congr ?_
  filter_upwards with w
  apply integral_congr_ae
  filter_upwards with u
  rw [boxQInd_slice_fst]

/-- Second-block slice integrability. -/
lemma integrableOn_slice_boxQInd_snd {N1 N2 : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    (j : Fin N2) {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun u : X N1 => ∫ w in abox N2 s,
      (Work.UBBInputs8.boxQInd volA A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) ^ 2)
      (abox N1 s) volume := by
  have hGint : IntegrableOn
      (fun x : X (N1 + N2) => (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2)
      (abox (N1 + N2) s) volume :=
    integrableOn_sq_boxQInd hs hA hAsub hvolA hΦ (Fin.natAdd N1 j)
  have hmp := aboxSplit_measurePreserving_restrict N1 N2 s
  have hGe : Integrable
      (fun p : X N1 × X N2 =>
        (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 p)) ^ 2)
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    apply (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding).mp
    refine hGint.congr ?_
    filter_upwards with x
    simp [Function.comp_apply, blockSplitEquiv_apply, mergeBlock_eq]
  refine (hGe.integral_prod_left).congr ?_
  filter_upwards with u
  apply integral_congr_ae
  filter_upwards with w
  rw [boxQInd_slice_snd]

/-! ## 5  The block decomposition of `cnPlusBoxInd` -/

/-- The block decomposition of the FS-faithful excited count. -/
lemma cnPlusBoxInd_split {N1 N2 : ℕ} {s volA : ℝ} (hs : 0 < s) {A : Set ℝ³}
    (hA : MeasurableSet A) (hAsub : A ⊆ acube s) (hvolA : volA = (volume : Measure ℝ³).real A)
    {Φ : X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    Work.UBBInputs8.cnPlusBoxInd s A volA Φ
      = (∫ w in abox N2 s, Work.UBBInputs8.cnPlusBoxInd s A volA
            (fun u => Φ (mergeBlock N1 N2 (u, w))))
        + (∫ u in abox N1 s, Work.UBBInputs8.cnPlusBoxInd s A volA
            (fun w => Φ (mergeBlock N1 N2 (u, w)))) := by
  -- the first block's slots
  have hFst : (∑ j : Fin N1, ∫ x in abox (N1 + N2) s,
        (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
      = ∫ w in abox N2 s, Work.UBBInputs8.cnPlusBoxInd s A volA
          (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
    calc
      (∑ j : Fin N1, ∫ x in abox (N1 + N2) s,
          (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
          = ∑ j : Fin N1, ∫ w in abox N2 s, ∫ u in abox N1 s,
              (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ
                (mergeBlock N1 N2 (u, w))) ^ 2 :=
            Finset.sum_congr rfl (fun j _ => fubini_boxQInd_fst hs hA hAsub hvolA j hΦ)
      _ = ∑ j : Fin N1, ∫ w in abox N2 s, ∫ u in abox N1 s,
              (Work.UBBInputs8.boxQInd volA A j
                (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            apply integral_congr_ae
            filter_upwards with w
            apply integral_congr_ae
            filter_upwards with u
            rw [boxQInd_slice_fst]
      _ = ∫ w in abox N2 s, ∑ j : Fin N1, ∫ u in abox N1 s,
              (Work.UBBInputs8.boxQInd volA A j
                (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2 :=
            (integral_finsetSum Finset.univ
              (fun j _ => integrableOn_slice_boxQInd_fst hs hA hAsub hvolA j hΦ)).symm
      _ = ∫ w in abox N2 s, Work.UBBInputs8.cnPlusBoxInd s A volA
              (fun u => Φ (mergeBlock N1 N2 (u, w))) := rfl
  -- the second block's slots
  have hSnd : (∑ j : Fin N2, ∫ x in abox (N1 + N2) s,
        (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2)
      = ∫ u in abox N1 s, Work.UBBInputs8.cnPlusBoxInd s A volA
          (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
    calc
      (∑ j : Fin N2, ∫ x in abox (N1 + N2) s,
          (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2)
          = ∑ j : Fin N2, ∫ u in abox N1 s, ∫ w in abox N2 s,
              (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ
                (mergeBlock N1 N2 (u, w))) ^ 2 :=
            Finset.sum_congr rfl (fun j _ => fubini_boxQInd_snd hs hA hAsub hvolA j hΦ)
      _ = ∑ j : Fin N2, ∫ u in abox N1 s, ∫ w in abox N2 s,
              (Work.UBBInputs8.boxQInd volA A j
                (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            apply integral_congr_ae
            filter_upwards with u
            apply integral_congr_ae
            filter_upwards with w
            rw [boxQInd_slice_snd]
      _ = ∫ u in abox N1 s, ∑ j : Fin N2, ∫ w in abox N2 s,
              (Work.UBBInputs8.boxQInd volA A j
                (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) ^ 2 :=
            (integral_finsetSum Finset.univ
              (fun j _ => integrableOn_slice_boxQInd_snd hs hA hAsub hvolA j hΦ)).symm
      _ = ∫ u in abox N1 s, Work.UBBInputs8.cnPlusBoxInd s A volA
              (fun w => Φ (mergeBlock N1 N2 (u, w))) := rfl
  calc Work.UBBInputs8.cnPlusBoxInd s A volA Φ
      = ∑ i : Fin (N1 + N2), ∫ x in abox (N1 + N2) s,
          (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 := rfl
    _ = (∑ j : Fin N1, ∫ x in abox (N1 + N2) s,
          (Work.UBBInputs8.boxQInd volA A (Fin.castAdd N2 j) Φ x) ^ 2)
        + (∑ j : Fin N2, ∫ x in abox (N1 + N2) s,
          (Work.UBBInputs8.boxQInd volA A (Fin.natAdd N1 j) Φ x) ^ 2) :=
          Fin.sum_univ_add _
    _ = _ := by rw [hFst, hSnd]

/-! ## 6  The target -/

theorem slotSplitCnPlusBoxInd {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAsub : A ⊆ Submission.BoseGases.acube s) {volA : ℝ}
    (hvolA : volA = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A) :
    Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ) =>
        Work.UBBInputs8.cnPlusBoxInd s A volA Φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N1 N2 Φ hΦ
    exact cnPlusBoxInd_split hs hA hAsub hvolA hΦ.continuous
  · intro N1 N2 Φ hΦ
    have h1 : (fun w : X N2 => Work.UBBInputs8.cnPlusBoxInd s A volA
        (fun u => Φ (mergeBlock N1 N2 (u, w))))
        = (fun w : X N2 => ∑ j : Fin N1, (∫ u in abox N1 s,
            (Work.UBBInputs8.boxQInd volA A j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u) ^ 2)) :=
      rfl
    rw [h1]
    exact integrable_finsetSum Finset.univ
      (fun j _ => integrableOn_slice_boxQInd_fst (N1 := N1) (N2 := N2) hs hA hAsub hvolA j
        hΦ.continuous)
  · intro N1 N2 Φ hΦ
    have h1 : (fun u : X N1 => Work.UBBInputs8.cnPlusBoxInd s A volA
        (fun w => Φ (mergeBlock N1 N2 (u, w))))
        = (fun u : X N1 => ∑ j : Fin N2, (∫ w in abox N2 s,
            (Work.UBBInputs8.boxQInd volA A j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w) ^ 2)) :=
      rfl
    rw [h1]
    exact integrable_finsetSum Finset.univ
      (fun j _ => integrableOn_slice_boxQInd_snd (N1 := N1) (N2 := N2) hs hA hAsub hvolA j
        hΦ.continuous)

end Work.BoseFixB1S
