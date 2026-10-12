import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ae_eval_mem_interior_acube`

The centred box `Λ(ℓ) = acube ℓ = [−ℓ/2, ℓ/2]³` is closed, and the `n`-particle box
`abox n ℓ = (Λ(ℓ))ⁿ` carries the restricted product volume
`volume.restrict (abox n ℓ) = πᵢ (volume.restrict (acube ℓ))`
(`Submission.BoseGases.restrict_abox_eq_pi`).

The boundary `acube ℓ \ interior (acube ℓ)` consists of the six coordinate faces
`{y | y m = ±ℓ/2}` (`acube_sdiff_interior_subset`), each contained in a coordinate
hyperplane of `ℝ³`, and those are Lebesgue-null (`volume_coord_eq_zero`).  Hence the
boundary is null (`volume_acube_sdiff_interior`), so for a.e. `y` w.r.t. the measure
restricted to the cube one has `y ∈ interior (acube ℓ)`
(`ae_restrict_acube_compl_interior`).  Taking the `j`-th coordinate of the product
measure gives the claim.

The only volume-theoretic input is that a coordinate hyperplane of `ℝ³` is null; this
is transported from `Fin 3 → ℝ` along the volume-preserving identification
`PiLp.volume_preserving_toLp` and uses `MeasureTheory.pi_hyperplane`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS

set_option linter.unusedVariables false

-- `ℝ³` is the global corpus notation `EuclideanSpace ℝ (Fin 3)`
-- (`Submission/Work/BoseKinLoc/Defs.lean`), imported through `Work.BoseFixB3.Defs`.

/-! ## 1. Coordinate hyperplanes of `ℝ³` are Lebesgue-null -/

/-- The hyperplane `{y : ℝ³ | y m = c}` is Lebesgue-null. -/
lemma volume_coord_eq_zero (m : Fin 3) (c : ℝ) :
    (volume : Measure ℝ³) {y : ℝ³ | y m = c} = 0 := by
  have hcont : Continuous fun y : ℝ³ => y m := by fun_prop
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hmeas : MeasurableSet {y : ℝ³ | y m = c} := by
    have hset : {y : ℝ³ | y m = c} = (fun y : ℝ³ => y m) ⁻¹' ({c} : Set ℝ) := by
      ext y
      exact Iff.rfl
    rw [hset]
    exact hcont.measurable (measurableSet_singleton c)
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hmeas]
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³) ⁻¹' {y : ℝ³ | y m = c}
      = {x : Fin 3 → ℝ | x m = c} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, WithLp.ofLp_toLp, PiLp.toLp_apply]
  rw [hpre]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) {x : Fin 3 → ℝ | x m = c} = 0
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) m c

/-! ## 2. The open inner box -/

/-- The open box `{z | ∀ m, z m ∈ Ioo (−ℓ/2) (ℓ/2)}` is open. -/
lemma isOpen_interiorBox (ℓ : ℝ) :
    IsOpen {z : ℝ³ | ∀ m : Fin 3, z m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} := by
  have hset : {z : ℝ³ | ∀ m : Fin 3, z m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)}
      = ⋂ m : Fin 3, (fun z : ℝ³ => z m) ⁻¹' Set.Ioo (-ℓ / 2) (ℓ / 2) := by
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hset]
  exact isOpen_iInter_of_finite fun m =>
    IsOpen.preimage (by fun_prop : Continuous fun z : ℝ³ => z m) isOpen_Ioo

/-- The open inner box is contained in the closed cube. -/
lemma interiorBox_subset_acube (ℓ : ℝ) :
    {z : ℝ³ | ∀ m : Fin 3, z m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)}
      ⊆ Submission.BoseGases.acube ℓ := by
  intro z hz
  rw [Submission.BoseGases.mem_acube_iff]
  intro m
  exact ⟨(hz m).1.le, (hz m).2.le⟩

/-! ## 3. The boundary of the cube is contained in the six faces -/

/-- A point of the cube which is not in the interior has a coordinate on the boundary
of the cube. -/
lemma acube_sdiff_interior_subset (ℓ : ℝ) :
    Submission.BoseGases.acube ℓ \ interior (Submission.BoseGases.acube ℓ) ⊆
      ⋃ m : Fin 3, {y : ℝ³ | y m = ℓ / 2 ∨ y m = -ℓ / 2} := by
  intro y hy
  by_contra hcon
  have hbox : ∀ m : Fin 3, y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := fun m =>
    (Submission.BoseGases.mem_acube_iff ℓ y).mp hy.1 m
  have hne : ∀ m : Fin 3, y m ≠ ℓ / 2 ∧ y m ≠ -ℓ / 2 := by
    intro m
    constructor
    · intro h
      exact hcon (Set.mem_iUnion_of_mem m (Or.inl h))
    · intro h
      exact hcon (Set.mem_iUnion_of_mem m (Or.inr h))
  have hmem : y ∈ {z : ℝ³ | ∀ m : Fin 3, z m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} := by
    intro m
    exact ⟨lt_of_le_of_ne (hbox m).1 (Ne.symm (hne m).2),
      lt_of_le_of_ne (hbox m).2 (hne m).1⟩
  have hsub : y ∈ interior {z : ℝ³ | ∀ m : Fin 3, z m ∈ Set.Ioo (-ℓ / 2) (ℓ / 2)} := by
    rw [(isOpen_interiorBox ℓ).interior_eq]
    exact hmem
  exact hy.2 (interior_mono (interiorBox_subset_acube ℓ) hsub)

/-! ## 4. The boundary of the cube is null -/

/-- The boundary of the centred cube is Lebesgue-null. -/
lemma volume_acube_sdiff_interior (ℓ : ℝ) :
    (volume : Measure ℝ³)
      (Submission.BoseGases.acube ℓ \ interior (Submission.BoseGases.acube ℓ)) = 0 := by
  refine measure_mono_null (acube_sdiff_interior_subset ℓ) ?_
  rw [measure_iUnion_null_iff]
  intro m
  rw [show {y : ℝ³ | y m = ℓ / 2 ∨ y m = -ℓ / 2}
      = {y : ℝ³ | y m = ℓ / 2} ∪ {y : ℝ³ | y m = -ℓ / 2} from by
        ext y
        simp only [Set.mem_union, Set.mem_ofPred_eq]]
  rw [measure_union_null_iff]
  exact ⟨volume_coord_eq_zero m (ℓ / 2), volume_coord_eq_zero m (-ℓ / 2)⟩

/-! ## 5. The complement of the interior is null in the cube -/

/-- With respect to the volume restricted to the cube, almost every point lies in the
interior of the cube. -/
lemma ae_restrict_acube_compl_interior (ℓ : ℝ) :
    ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
      {y : ℝ³ | ¬ y ∈ interior (Submission.BoseGases.acube ℓ)} = 0 := by
  change ((volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ))
      ((interior (Submission.BoseGases.acube ℓ))ᶜ) = 0
  rw [Measure.restrict_apply' (Submission.BoseGases.acube_measurable ℓ)]
  rw [Set.inter_comm]
  exact volume_acube_sdiff_interior ℓ

/-! ## 6. The claim -/

theorem ae_eval_mem_interior_acube {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      x j ∈ interior (Submission.BoseGases.acube ℓ) := by
  rw [MeasureTheory.ae_iff]
  change (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))
      ((Function.eval j) ⁻¹'
        {y : ℝ³ | ¬ y ∈ interior (Submission.BoseGases.acube ℓ)}) = 0
  rw [Submission.BoseGases.restrict_abox_eq_pi]
  refine MeasureTheory.Measure.pi_eval_preimage_null
    (fun _ : Fin n => (volume : Measure ℝ³).restrict (Submission.BoseGases.acube ℓ)) ?_
  exact ae_restrict_acube_compl_interior ℓ

end Work.BoseFixB3.CS
