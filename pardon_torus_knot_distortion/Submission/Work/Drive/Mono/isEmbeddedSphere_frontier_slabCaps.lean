import Mathlib
import Submission.Work.Drive.Mono.SlabCaps

/-!
# The frontiers of the two caps of the box cut by the slab are embedded spheres

`Work.Drive.Mono.slabCapPlus s c σ a h v = PBox s c σ ∩ {⟪v,·⟫ ≥ a + h}` and
`Work.Drive.Mono.slabCapMinus s c σ a h v = PBox s c σ ∩ {⟪v,·⟫ ≤ a - h}` are the two pieces into
which the tilted slab cuts Pardon's box `PBox s c σ`.  Their frontiers are the two spheres of
`Work.Drive.Mono.frontier_PBox_sdiff_slab_eq_caps`, and the slicings of those two spheres are the
two inputs of clause 1 of the trace data above the `ℓ`-range of the box
(`Work.Drive.Mono.traceCurvesAt_of_lt_of_slicing_caps`).

Each cap is an intersection of two convex sets — the box `PBox s c σ` (convex, `convex_PBox`) and
a closed half-space — and it has nonempty interior there (a point of the box strictly beyond the
cutting plane witnesses it) and is bounded (it lies in the box, hence in a ball).  For *any* such
convex body `K` of `ℝ³` (convex, nonempty interior, bounded), `Mathlib`'s gauge rescale
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` carries `frontier K` onto the round
unit sphere, so `frontier K` is the image of the unit sphere under a homeomorphism: an embedded
sphere in the sense of `Work.InnermostDisk.IsEmbeddedSphere`.  That is the whole content of the
theorem below; nothing is used beyond what is already assumed — `0 < s` for the boundedness of the
box, and `hcut` only through the two points lying strictly on either side of the slab, which is
exactly what `SlabCutsBox` provides.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The frontier of a convex body of `ℝ³` is an embedded sphere.**  `K` is convex, has nonempty
interior and is bounded; then the gauge rescale homeomorphism of Mathlib sends `frontier K` onto the
unit sphere, so `frontier K` is the image of that sphere under a homeomorphism. -/
theorem isEmbeddedSphere_frontier_of_convex {K : Set R3} (hK : Convex ℝ K)
    (hne : (interior K).Nonempty) (hbdd : Bornology.IsBounded K) :
    Work.InnermostDisk.IsEmbeddedSphere (frontier K) := by
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hK hne hbdd
  have h1 : h.symm '' (h '' frontier K) = frontier K := by
    rw [Set.image_image]
    simp
  have hsymm : h.symm '' Metric.sphere (0 : R3) 1 = frontier K := by
    rw [← hfr]
    exact h1
  rw [← hsymm]
  exact Work.InnermostDisk.isEmbeddedSphere_image_homeomorph h.symm
    (Work.InnermostDisk.isEmbeddedSphere_sphere (0 : R3) one_pos)

/-- The closed half-space `{y | A ≤ ⟪v,y⟫}` of `ℝ³` is convex: the inner product is additive and
positively homogeneous in its second argument. -/
theorem convex_setOf_le_inner (v : R3) (A : ℝ) : Convex ℝ {y : R3 | A ≤ inner ℝ v y} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hinner : inner ℝ v (a • x + b • y) = a * inner ℝ v x + b * inner ℝ v y := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  rw [hinner]
  calc A = a * A + b * A := by rw [← add_mul, hab, one_mul]
    _ ≤ a * inner ℝ v x + b * inner ℝ v y :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- **The cap of Pardon's box cut by the half-space `{A ≤ ⟪v,·⟫}` is an embedded sphere.**

The cap is convex (a box cut by a half-space), bounded (it lies in the box, hence in a ball) and has
nonempty interior: a point of the box strictly beyond the cutting plane `{⟪v,·⟫ = A}` is an interior
point of the cap, because the box is open and the strict half-space is open. -/
theorem isEmbeddedSphere_frontier_PBox_inter_ge (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (A : ℝ) (hs : 0 < s) (hne : ∃ y : R3, y ∈ Submission.PBox s c σ ∧ A < inner ℝ v y) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Submission.PBox s c σ ∩ {y : R3 | A ≤ inner ℝ v y})) := by
  have hcont : Continuous fun y : R3 => inner ℝ v y := continuous_const.inner continuous_id
  refine isEmbeddedSphere_frontier_of_convex ?_ ?_ ?_
  · exact (Work.Topology.SphereSlicing.convex_PBox s c σ).inter (convex_setOf_le_inner v A)
  · obtain ⟨y0, hy0P, hy0A⟩ := hne
    refine ⟨y0, ?_⟩
    rw [interior_inter]
    refine ⟨?_, ?_⟩
    · rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]
      exact hy0P
    · have hsub : {y : R3 | A < inner ℝ v y} ⊆ {y : R3 | A ≤ inner ℝ v y} := by
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        exact le_of_lt hz
      have hmem : y0 ∈ interior {y : R3 | A < inner ℝ v y} := by
        rw [(isOpen_lt continuous_const hcont).interior_eq]
        exact hy0A
      exact interior_mono hsub hmem
  · refine Bornology.IsBounded.subset
      (Metric.isBounded_ball (x := c) (r := (5 / 2) * s)) ?_
    intro y hy
    exact Submission.PBox_subset_ball s hs.le c σ hy.1

/-- **The mirror cap**: the same statement for the half-space `{⟪v,·⟫ ≤ A}`, obtained from
`isEmbeddedSphere_frontier_PBox_inter_ge` by replacing `v` with `-v` and `A` with `-A`. -/
theorem isEmbeddedSphere_frontier_PBox_inter_le (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (A : ℝ) (hs : 0 < s) (hne : ∃ y : R3, y ∈ Submission.PBox s c σ ∧ inner ℝ v y < A) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y ≤ A})) := by
  have hset : (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y ≤ A})
      = (Submission.PBox s c σ ∩ {y : R3 | -A ≤ inner ℝ (-v) y}) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [inner_neg_left]; linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [inner_neg_left] at h2
      linarith
  rw [hset]
  refine isEmbeddedSphere_frontier_PBox_inter_ge s c σ (-v) (-A) hs ?_
  obtain ⟨y, hy, hlt⟩ := hne
  exact ⟨y, hy, by rw [inner_neg_left]; linarith⟩

theorem isEmbeddedSphere_frontier_slabCaps (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (a h : ℝ) {v : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0)
    (hcut : Work.Drive.Mono.SlabCutsBox s c σ a h v) :
    Work.InnermostDisk.IsEmbeddedSphere
        (frontier (Work.Drive.Mono.slabCapPlus s c σ a h v)) ∧
      Work.InnermostDisk.IsEmbeddedSphere
        (frontier (Work.Drive.Mono.slabCapMinus s c σ a h v)) := by
  obtain ⟨yP, hyP, hyP'⟩ := hcut.1
  obtain ⟨yM, hyM, hyM'⟩ := hcut.2
  refine ⟨?_, ?_⟩
  · rw [show Work.Drive.Mono.slabCapPlus s c σ a h v
        = Submission.PBox s c σ ∩ {y : R3 | a + h ≤ inner ℝ v y} from by
      ext y
      simp [Work.Drive.Mono.slabCapPlus]]
    exact isEmbeddedSphere_frontier_PBox_inter_ge s c σ v (a + h) hs ⟨yP, hyP, hyP'⟩
  · rw [show Work.Drive.Mono.slabCapMinus s c σ a h v
        = Submission.PBox s c σ ∩ {y : R3 | inner ℝ v y ≤ a - h} from by
      ext y
      simp [Work.Drive.Mono.slabCapMinus]]
    exact isEmbeddedSphere_frontier_PBox_inter_le s c σ v (a - h) hs ⟨yM, hyM, hyM'⟩

end

end Work.Drive.Mono
