import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.ne_top_left_of_trace

/-!
# The level region at `mu < ℓ centre` lies in the closure of the dent's region plus the strip

`Work.Drive.Final.dentOutRegion D` is (the carrier part of) the interior of the preimage under the
dent deformation of the level's removed set at the level `ℓ D.centre`.  The present module combines
two facts:

* the purely order-theoretic statement `Work.Drive.Mono.levelRegion_subset_closure_union_levelStrip`
  — for `mu ≤ lamstar` the open sweep region at the level `mu` lies in the closure of the open sweep
  region at the level `lamstar` together with the closed strip between the two levels;
* the "wall push" computation (proved here, self-contained, as `openRegion_subset_dentOutRegion`)
  that the dent's region contains the *whole* open sweep region at the dent's own level: the dent
  direction is orthogonal to the slab normal (`d_orth_v`), so membership in the closed tilted slab is
  preserved pointwise, while the level functional only ever *increases* along the dent (`χ_nonneg`,
  `a'_pos`, `push_pos`), so no point is pushed behind its own level; `box_pres` keeps the deformation
  inside the open box.

For every level `mu < ℓ D.centre` the open sweep region at `mu` is therefore contained in the
closure of the dent's region together with the strip `mu ≤ ℓ ≤ ℓ D.centre` inside the closed box and
the closed tilted slab.  This is the "one-step drop" statement consumed by the no-jump argument.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

variable {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}

/-! ## The dent preserves the slab and never lowers the level -/

/-- The dent deformation does not change the slab height functional `⟪v, ·⟫` (`⟪v, d⟫ = 0`). -/
private theorem anyDent_inner_v_deform (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    inner ℝ v (D.deform z) = inner ℝ v z := by
  simp only [AnyDentDatum.deform, dentDeform, inner_add_right, inner_smul_right, D.d_orth_v,
    mul_zero, add_zero]

/-- The dent deformation preserves the closed tilted slab. -/
private theorem anyDent_deform_mem_slab_iff (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    D.deform z ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ↔
      z ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
  simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, anyDent_inner_v_deform D z]

/-- The displacement of the level functional under the dent. -/
private theorem anyDent_deform_wall (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    ℓ (D.deform z) = ℓ z + (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d := by
  simp only [AnyDentDatum.deform, dentDeform, map_add, map_smul, smul_eq_mul]

/-- The deformation does not leave the open box: inside the support ball this is the datum's
`box_pres`, outside it the deformation is the identity. -/
private theorem anyDent_deform_mem_PBox (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {z : R3}
    (hz : z ∈ Submission.PBox s c σ) : D.deform z ∈ Submission.PBox s c σ := by
  by_cases hb : ‖z - D.centre‖ ≤ D.r
  · exact (D.box_pres z hb).mp hz
  · rw [not_le] at hb
    have hχ : D.χ (‖z - D.centre‖ / D.r) = 0 := by
      apply D.χ_eq_zero
      rw [one_le_div D.r_pos]
      exact le_of_lt hb
    have hself : D.deform z = z := by
      simp only [AnyDentDatum.deform, dentDeform, hχ, mul_zero, zero_smul, add_zero]
    rw [hself]
    exact hz

/-- The level functional never decreases along the dent (`χ ≥ 0`, `a' > 0`, `ℓ d > 0`). -/
private theorem anyDent_wall_le (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (z : R3) :
    ℓ z ≤ ℓ (D.deform z) := by
  have hnn : 0 ≤ (D.a' * D.χ (‖z - D.centre‖ / D.r)) * ℓ D.d :=
    mul_nonneg (mul_nonneg (le_of_lt D.a'_pos) (D.χ_nonneg _)) (le_of_lt D.push_pos)
  rw [anyDent_deform_wall D z]
  linarith

/-! ## The open region at the dent's own level sits inside the dent's region -/

/-- **The open sweep region at the dent's level is contained in the dent's region.**  This is the
"wall push" fact: past the wall `ℓ = ℓ D.centre` the deformation moves points *further* past it
(when on the slab), while off the closed slab the deformation keeps them off it. -/
private theorem openRegion_subset_dentOutRegion (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre) ⊆ dentOutRegion ψ s c σ u v h R ℓ D := by
  intro x hx
  rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_inter_iff] at hx
  obtain ⟨hxcarr, hxbox, hxnot⟩ := hx
  refine ⟨hxcarr, ?_⟩
  by_cases hxslab : x ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h
  · -- `x` lies on the closed slab, so it lies strictly past the wall `ℓ = ℓ D.centre`
    have hxlt : ℓ D.centre < ℓ x := by
      by_contra hle
      exact hxnot ⟨hxslab, not_lt.mp hle⟩
    have hsub : Submission.PBox s c σ ∩ {y : R3 | ℓ D.centre < ℓ y} ⊆
        D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) := by
      rintro y ⟨hybox, hylt⟩
      rw [Set.mem_preimage, Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      simp only [Set.mem_ofPred_eq] at hylt
      refine ⟨anyDent_deform_mem_PBox D hybox, ?_⟩
      rintro ⟨-, hlt⟩
      have := anyDent_wall_le D y
      linarith
    have hopen : IsOpen (Submission.PBox s c σ ∩ {y : R3 | ℓ D.centre < ℓ y}) :=
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
        (isOpen_lt continuous_const ℓ.continuous)
    exact interior_maximal hsub hopen ⟨hxbox, hxlt⟩
  · -- `x` lies off the closed slab, and the deformation keeps it off it
    have hsub : Submission.PBox s c σ ∩
        {y : R3 | y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h} ⊆
        D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) := by
      rintro y ⟨hybox, hyslab⟩
      rw [Set.mem_preimage, Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      simp only [Set.mem_ofPred_eq] at hyslab
      refine ⟨anyDent_deform_mem_PBox D hybox, ?_⟩
      rintro ⟨hslab', -⟩
      exact hyslab ((anyDent_deform_mem_slab_iff D y).mp hslab')
    have hopen : IsOpen (Submission.PBox s c σ ∩
        {y : R3 | y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h}) :=
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
        (Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).isOpen_compl
    exact interior_maximal hsub hopen ⟨hxbox, hxslab⟩

/-! ## The target -/

/-- **The level region below the dent's level is contained in the closure of the dent's region, plus
the strip up to the dent's level.** -/
theorem levelRegion_subset_dentOut_union_strip {ψ : Submission.Diffeo}
    {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) {mu : ℝ}
    (hmu : mu < ℓ D.centre) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        mu ⊆
      closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) ∪
        Work.Drive.Mono.levelStrip (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu
          (ℓ D.centre) := by
  refine Set.Subset.trans
    (Work.Drive.Mono.levelRegion_subset_closure_union_levelStrip
      (P := Work.Drive.EpsSphere.torusOf ψ) (s := s) (c := c) (σ := σ) (u := u) (v := v)
      (h := h) (ℓ := ℓ) (mu := mu) (lamstar := ℓ D.centre)) ?_
  rintro z (hz | hz)
  · exact Or.inl (closure_mono (openRegion_subset_dentOutRegion D) hz)
  · exact Or.inr hz

end

end Work.Drive.Final
