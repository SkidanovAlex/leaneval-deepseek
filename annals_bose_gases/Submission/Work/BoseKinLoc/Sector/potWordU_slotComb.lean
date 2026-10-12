import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.fibre_defs_v3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option linter.unusedVariables false

/-! ## Auxiliary lemmas

The vanishing of the anchored window `χ_0` off the box, the order-theoretic
properties of `slotIso`, and the two finite-sum re-indexing lemmas (over a single
index and over the strictly ordered pairs) that carry out the collapse.
-/

/-- The anchored window `χ_0 = χ((ℓ⁻¹)•·)` vanishes off the centred box `acube ℓ`. -/
lemma chiU_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℝ³}
    (ht : t ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiU ℓ 0 t = 0 := by
  rw [show Submission.BoseGases.chiU ℓ 0 t = Submission.BoseGases.chiScale ℓ t from by
        simp [Submission.BoseGases.chiU, Submission.BoseGases.chiScale]]
  by_contra h
  exact ht (Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ)
    (Submission.BoseGases.chiScale_support_le hℓ h))

/-- `slotIso S` is an order isomorphism for the subspace order on the slots of `S`. -/
lemma slotIso_lt_iff {N : ℕ} {S : Finset (Fin N)} (a b : Work.PerSector.SlotIn N S) :
    (slotIso S) a < (slotIso S) b ↔ a.1 < b.1 := by
  rw [show (slotIso S) = ⇑(Finset.orderIsoOfFin S rfl).symm from rfl]
  exact (Finset.orderIsoOfFin S rfl).symm.lt_iff_lt

/-- The order-reflecting form of `slotIso_symm_lt`: the `m`-th smallest slot of `S` is smaller
than the `n`-th one exactly when `m < n`. -/
lemma slotIso_symm_lt_iff {N : ℕ} {S : Finset (Fin N)} {i j : Fin S.card} :
    ((slotIso S).symm i).1 < ((slotIso S).symm j).1 ↔ i < j := by
  have h := slotIso_lt_iff ((slotIso S).symm i) ((slotIso S).symm j)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- A sum over `Fin N` of a function vanishing off `S` is the sum over `S`, re-indexed by the
order isomorphism `slotIso S`. -/
lemma sum_univ_eq_sum_slots {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℝ)
    (hF : ∀ i, i ∉ S → F i = 0) :
    (∑ i : Fin N, F i) = ∑ m : Fin S.card, F ((slotIso S).symm m) := by
  calc (∑ i : Fin N, F i) = ∑ i ∈ S, F i :=
        (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hF i hi)).symm
    _ = ∑ i : Work.PerSector.SlotIn N S, F i :=
        Finset.sum_subtype S (fun x => Iff.rfl) F
    _ = ∑ m : Fin S.card, F ((slotIso S).symm m) :=
        Fintype.sum_equiv (slotIso S)
          (fun i : Work.PerSector.SlotIn N S => F i)
          (fun m : Fin S.card => F ((slotIso S).symm m)) (fun i => by simp)

/-- The sum over the strictly ordered pairs `ij : Fin N × Fin N` written as an iterated sum with
the ordering indicator. -/
lemma sum_pair_subtype_eq {N : ℕ} (W : Fin N → Fin N → ℝ) :
    (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, W ij.1.1 ij.1.2)
      = ∑ i : Fin N, ∑ j : Fin N, (if i < j then W i j else 0) := by
  rw [← Finset.sum_subtype (s := (Finset.univ : Finset (Fin N × Fin N)).filter
        (fun ij => ij.1 < ij.2)) (by intro x; simp) (fun ij => W ij.1 ij.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

/-- A sum over the strictly ordered pairs of `Fin N` of a kernel vanishing whenever one slot is
outside `S` is the sum over the strictly ordered pairs of the slots of `S`, re-indexed by the
order isomorphism `slotIso S` (the order preservation is what keeps the orientation of the pair
sum). -/
lemma sum_orderedPairs_eq_sum_slots {N : ℕ} (S : Finset (Fin N)) (W : Fin N → Fin N → ℝ)
    (hW₁ : ∀ i j, i ∉ S → W i j = 0) (hW₂ : ∀ i j, j ∉ S → W i j = 0) :
    (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, W ij.1.1 ij.1.2)
      = ∑ mn : {mn : Fin S.card × Fin S.card | mn.1 < mn.2},
          W ((slotIso S).symm mn.1.1) ((slotIso S).symm mn.1.2) := by
  calc (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, W ij.1.1 ij.1.2)
      = ∑ i : Fin N, ∑ j : Fin N, (if i < j then W i j else 0) := sum_pair_subtype_eq W
    _ = ∑ i : Fin N, ∑ n : Fin S.card,
          (if i < ((slotIso S).symm n).1 then W i ((slotIso S).symm n) else 0) :=
          Finset.sum_congr rfl (fun i _ =>
            sum_univ_eq_sum_slots S _ (fun j hj => by simp [hW₂ i j hj]))
    _ = ∑ m : Fin S.card, ∑ n : Fin S.card,
          (if ((slotIso S).symm m).1 < ((slotIso S).symm n).1
            then W ((slotIso S).symm m) ((slotIso S).symm n) else 0) :=
          sum_univ_eq_sum_slots S _ (fun i hi => by
            apply Finset.sum_eq_zero
            intro n _
            simp [hW₁ i ((slotIso S).symm n) hi])
    _ = ∑ mn : {mn : Fin S.card × Fin S.card | mn.1 < mn.2},
          W ((slotIso S).symm mn.1.1) ((slotIso S).symm mn.1.2) := by
          rw [sum_pair_subtype_eq
            (fun m n : Fin S.card => W ((slotIso S).symm m) ((slotIso S).symm n))]
          refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
          by_cases h : m < n
          · rw [if_pos h, if_pos ((slotIso_symm_lt_iff).mpr h)]
          · rw [if_neg h, if_neg (fun hc => h ((slotIso_symm_lt_iff).mp hc))]

/-- **The potential word collapses on a slot set.**  Let `B = acube ℓ` (`ℓ > 0`) be the
localisation box, `z` an in-box configuration (slots of `S`) and `y` an outside configuration
(all slots outside `acube ℓ`).  In the reassembled configuration `x = slotComb S z y` the
`N`-body potential word `potWordU N v g ℓ μ 0 x` — whose one-body kernels carry the factor
`chiU ℓ 0` (supported in `acube ℓ`) and whose pair kernels carry a factor `chiU` in *both*
variables — sees only the particles of `S`: every slot outside `S` has a vanishing `chiU`-factor
(because `SlotIn`/`SlotOut` give `x i = z ⟨i,·⟩` for `i ∈ S` and `x j = y ⟨j,·⟩ ∉ acube ℓ` for
`j ∉ S`), so the one-body sum over `Fin N` and the pair sum over `{i < j : Fin N}` reduce to the
sums over the slots of `S`, re-indexed by the order isomorphism `slotIso S`.  The orientation of
the pair sum is respected because `slotIso S` is order preserving.  Namespace
`Work.BoseKinLoc.Sector`; imports: Mathlib, `Submission.Work.BoseKinLoc.Defs`,
`Submission.Work.BoseKinLoc.Sector.fibre_defs_v3`, `Submission.Work.PerSector.Defs`. -/
theorem potWordU_slotComb {N : ℕ} (S : Finset (Fin N)) {v g : ℝ³ → ℝ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    (z : Work.PerSector.SlotIn N S → ℝ³) (y : Work.PerSector.SlotOut N S → ℝ³)
    (hy : ∀ j : Work.PerSector.SlotOut N S, y j ∉ Submission.BoseGases.acube ℓ) :
    Work.BoseKinLoc.potWordU N v g ℓ μ 0 (Work.PerSector.slotComb S z y)
      = Work.BoseKinLoc.potWordU S.card v g ℓ μ 0
          (fun m : Fin S.card => z ((slotIso S).symm m)) := by
  -- the value of the reassembled configuration on and off `S`
  have hv_in : ∀ (i : Fin N) (hi : i ∈ S), (Work.PerSector.slotComb S z y) i = z ⟨i, hi⟩ :=
    fun i hi => by rw [Work.PerSector.slotComb_apply, dif_pos hi]
  have hv_out : ∀ (i : Fin N) (hi : i ∉ S), (Work.PerSector.slotComb S z y) i = y ⟨i, hi⟩ :=
    fun i hi => by rw [Work.PerSector.slotComb_apply, dif_neg hi]
  have hv_slot : ∀ (a : Work.PerSector.SlotIn N S),
      (Work.PerSector.slotComb S z y) a.1 = z a :=
    fun a => hv_in a.1 a.2
  -- off the box the anchored window vanishes
  have hzero : ∀ t : ℝ³, t ∉ Submission.BoseGases.acube ℓ → chiU ℓ 0 t = 0 :=
    fun t ht => chiU_zero_of_notMem_acube hℓ ht
  -- the one-body sum
  have h1 : (∑ i : Fin N, ∫ y' : ℝ³, wLoc ℓ g 0 ((Work.PerSector.slotComb S z y) i) y')
      = ∑ m : Fin S.card, ∫ y' : ℝ³, wLoc ℓ g 0 (z ((slotIso S).symm m)) y' := by
    rw [sum_univ_eq_sum_slots S
      (fun i => ∫ y' : ℝ³, wLoc ℓ g 0 ((Work.PerSector.slotComb S z y) i) y') ?_]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hv_slot ((slotIso S).symm m)]
    · intro i hi
      have hxi : (Work.PerSector.slotComb S z y) i ∉ Submission.BoseGases.acube ℓ := by
        rw [hv_out i hi]; exact hy ⟨i, hi⟩
      simp [wLoc, hzero _ hxi]
  -- the pair sum
  have h2 : (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
        wLoc ℓ v 0 ((Work.PerSector.slotComb S z y) ij.1.1)
          ((Work.PerSector.slotComb S z y) ij.1.2))
      = ∑ mn : {mn : Fin S.card × Fin S.card | mn.1 < mn.2},
          wLoc ℓ v 0 (z ((slotIso S).symm mn.1.1)) (z ((slotIso S).symm mn.1.2)) := by
    rw [sum_orderedPairs_eq_sum_slots S
      (fun i j => wLoc ℓ v 0 ((Work.PerSector.slotComb S z y) i)
        ((Work.PerSector.slotComb S z y) j)) ?_ ?_]
    · refine Finset.sum_congr rfl (fun mn _ => ?_)
      rw [hv_slot ((slotIso S).symm mn.1.1), hv_slot ((slotIso S).symm mn.1.2)]
    · intro i j hi
      have hxi : (Work.PerSector.slotComb S z y) i ∉ Submission.BoseGases.acube ℓ := by
        rw [hv_out i hi]; exact hy ⟨i, hi⟩
      simp [wLoc, hzero _ hxi]
    · intro i j hj
      have hxj : (Work.PerSector.slotComb S z y) j ∉ Submission.BoseGases.acube ℓ := by
        rw [hv_out j hj]; exact hy ⟨j, hj⟩
      simp [wLoc, hzero _ hxj]
  show -μ * (∑ i : Fin N, ∫ y' : ℝ³, wLoc ℓ g 0 ((Work.PerSector.slotComb S z y) i) y')
      + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
          wLoc ℓ v 0 ((Work.PerSector.slotComb S z y) ij.1.1)
            ((Work.PerSector.slotComb S z y) ij.1.2)
    = -μ * (∑ m : Fin S.card, ∫ y' : ℝ³,
          wLoc ℓ g 0 (z ((slotIso S).symm m)) y')
      + ∑ mn : {mn : Fin S.card × Fin S.card | mn.1 < mn.2},
          wLoc ℓ v 0 (z ((slotIso S).symm mn.1.1)) (z ((slotIso S).symm mn.1.2))
  rw [h1, h2]

end Work.BoseKinLoc.Sector
