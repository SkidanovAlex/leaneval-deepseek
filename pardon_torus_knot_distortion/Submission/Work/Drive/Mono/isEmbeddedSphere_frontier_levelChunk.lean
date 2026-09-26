import Mathlib
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps

/-!
# The frontier of the removed *chunk* of a level of the tilted sweep is an embedded sphere

At a level `lam` of the tilted sweep the removed set is `PBox s c σ \ C` with

    C = PBox s c σ ∩ tiltedSlabClosed (⟪v,c⟫+u) v h ∩ {ℓ < lam}

the **convex chunk** cut out of the box by the slab and the wall; the trace of the level is contained
in `∂PBox ∪ ∂C` (`Work.Drive.Mono.frontier_tiltedLevelRemoved_subset_frontier_union_chunk`), and
`∂C` is the sphere which carries the *level* trace inside the box — this is the intermediate-level
analogue of the two caps of `Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps`, and it is the
sphere whose slicing feeds clause 1 at an intermediate level (the level frontier itself is *not* a
sphere: it is `∂PBox` with a piece of `∂C` sewn in along the seam).

The chunk is the intersection of three convex sets — the box `PBox s c σ` (open, convex:
`Work.Topology.SphereSlicing.convex_PBox`), the closed slab `{|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h}` (an
intersection of two closed half-spaces) and the open half-space `{ℓ < lam}` — and it has nonempty
interior exactly when it has a point (`hne`: a point of the box, in the *open* slab and strictly
below the wall is an interior point).  Its frontier is therefore the frontier of a convex body of
`ℝ³`, hence an embedded sphere by
`Work.Drive.Mono.isEmbeddedSphere_frontier_of_convex`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The closed half-space `{y | ⟪v,y⟫ ≤ A}` of `ℝ³` is convex. -/
theorem convex_setOf_inner_le (v : R3) (A : ℝ) : Convex ℝ {y : R3 | inner ℝ v y ≤ A} := by
  have hset : {y : R3 | inner ℝ v y ≤ A} = {y : R3 | -A ≤ inner ℝ (-v) y} := by
    ext y
    simp only [Set.mem_ofPred_eq, inner_neg_left]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact convex_setOf_le_inner (-v) (-A)

/-- The open half-space `{y | L y < lam}` of `ℝ³` is convex. -/
theorem convex_setOf_clm_lt (L : R3 →L[ℝ] ℝ) (lam : ℝ) : Convex ℝ {y : R3 | L y < lam} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hlin : L (a • x + b • y) = a * L x + b * L y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0, zero_mul, zero_add]
    have hb1 : b = 1 := by linarith
    rw [hb1, one_mul]
    exact hy
  · have h1 : a * L x < a * lam := mul_lt_mul_of_pos_left hx hapos
    have h2 : b * L y ≤ b * lam := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    have h3 : a * lam + b * lam = lam := by rw [← add_mul, hab, one_mul]
    linarith

/-- **The frontier of the removed chunk of a level of the tilted sweep is an embedded sphere.**

`C = PBox s c σ ∩ tiltedSlabClosed (⟪v,c⟫+u) v h ∩ {ℓ < lam}` is convex and, when it has a point
(`hne`, the three conditions strictly: in the box, in the *open* slab, below the wall), its interior
is nonempty; it is bounded because it lies in the box.  Hence its frontier is the frontier of a
convex body of `ℝ³`, an embedded sphere. -/
theorem isEmbeddedSphere_frontier_levelChunk {s u h lam : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    (hne : ∃ y : LeanEval.KnotTheory.PardonDistortion.R3, y ∈ Submission.PBox s c σ ∧
      |inner ℝ v y - (inner ℝ v c + u)| < h ∧ ℓ y < lam) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Submission.PBox s c σ ∩
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y < lam})) := by
  obtain ⟨y0, hy0P, hy0s, hy0ℓ⟩ := hne
  have hs : 0 < s := by
    rw [Submission.mem_PBox] at hy0P
    have h0 : |y0 (σ 0) - c (σ 0)| < s := by
      have := hy0P 0
      simpa using this
    exact lt_of_le_of_lt (abs_nonneg _) h0
  refine isEmbeddedSphere_frontier_of_convex ?_ ⟨y0, ?_⟩ ?_
  · have hslab : Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h =
        {y : R3 | inner ℝ v c + u - h ≤ inner ℝ v y} ∩
          {y : R3 | inner ℝ v y ≤ inner ℝ v c + u + h} := by
      ext y
      simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · intro hy
        rw [abs_le] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      · rintro ⟨h1, h2⟩
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
    rw [hslab]
    exact ((Work.Topology.SphereSlicing.convex_PBox s c σ).inter
      ((convex_setOf_le_inner v (inner ℝ v c + u - h)).inter
        (convex_setOf_inner_le v (inner ℝ v c + u + h)))).inter
      (convex_setOf_clm_lt ℓ lam)
  · rw [interior_inter, interior_inter]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]
      exact hy0P
    · have hopen : IsOpen {z : R3 | |inner ℝ v z - (inner ℝ v c + u)| < h} := by
        refine isOpen_lt ?_ continuous_const
        exact ((continuous_const.inner continuous_id).sub continuous_const).abs
      have hsub : {z : R3 | |inner ℝ v z - (inner ℝ v c + u)| < h} ⊆
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
        intro z hz
        show |inner ℝ v z - (inner ℝ v c + u)| ≤ h
        exact le_of_lt hz
      have hmem : y0 ∈ interior {z : R3 | |inner ℝ v z - (inner ℝ v c + u)| < h} := by
        rw [hopen.interior_eq]
        exact hy0s
      exact interior_mono hsub hmem
    · rw [(isOpen_lt ℓ.continuous continuous_const).interior_eq]
      exact hy0ℓ
  · refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := c) (r := (5 / 2) * s)) ?_
    intro y hy
    exact Submission.PBox_subset_ball s hs.le c σ hy.1.1

end

end Work.Drive.Mono
