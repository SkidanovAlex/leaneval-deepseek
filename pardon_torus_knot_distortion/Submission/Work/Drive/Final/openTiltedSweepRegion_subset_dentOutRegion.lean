import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The open tilted sweep region pulls back into the dent's removed set

`Work.Drive.Final.dentOutRegion D` is the set of points of the carrier whose image under the dent
deformation `D.deform` lies in the *interior* of the removed set of the level `ℓ D.centre`.  This
module proves that it contains the whole *open* sweep region at that level.

The two structural facts about `AnyDentDatum` used are exactly the two which make the dent a
"wall push":

* the direction `d` is orthogonal to the slab normal `v` (`d_orth_v`), so the deformation preserves
  the slab height functional `⟪v, ·⟫` *pointwise* — hence membership in the closed tilted slab;
* the level functional shifts by the nonnegative amount
  `(D.a' * D.χ (‖· − centre‖/r)) * ℓ d` (`push_pos`, `a'_pos`, `χ_nonneg`), so the deformation never
  moves a point *behind* its own level.

Together with `box_pres` (the deformation does not leave the open box) this gives, for every point
`x` of the region: a whole neighbourhood of `x` (the box intersected with either the half space
`{ℓ > ℓ D.centre}`, when `x` is on the slab, or the complement of the slab, when it is not) is mapped
into the removed set.  That is precisely `x ∈ interior (D.deform ⁻¹' removed)`.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

variable {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}

/-- The dent deformation does not change the slab height functional `⟪v, ·⟫` (since `⟪v, d⟫ = 0`). -/
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

theorem openTiltedSweepRegion_subset_dentOutRegion {ψ : Submission.Diffeo}
    {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (ℓ D.centre) ⊆ Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D := by
  intro x hx
  rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion] at hx
  rcases hx with ⟨hxcarr, hxbox, hxnot⟩
  rw [Work.Drive.Final.dentOutRegion]
  refine ⟨hxcarr, ?_⟩
  by_cases hxslab : x ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h
  · -- `x` lies on the slab, so it lies strictly past the wall `ℓ = ℓ D.centre`
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
  · -- `x` lies off the (closed) slab, so the whole neighbourhood in the complement is mapped off it
    have hsub : Submission.PBox s c σ ∩
        {y : R3 | y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h} ⊆
        D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) := by
      rintro y ⟨hybox, hyslab⟩
      rw [Set.mem_preimage, Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      refine ⟨anyDent_deform_mem_PBox D hybox, ?_⟩
      rintro ⟨hslab', -⟩
      exact hyslab ((anyDent_deform_mem_slab_iff D y).mp hslab')
    have hopen : IsOpen (Submission.PBox s c σ ∩
        {y : R3 | y ∉ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h}) :=
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ).inter
        (Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).isOpen_compl
    exact interior_maximal hsub hopen ⟨hxbox, hxslab⟩

end

end Work.Drive.Final
