import Mathlib
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Mono.Residual

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

/-- **The parameters of the knot in the fundamental interval bound the points of its range in the
box intersected with a fixed set.**

The image of the fundamental interval `[0, 2π)` is the whole range of the `2π`-periodic curve
(`Work.Drive.EpsForm.range_knot_eq_image_Ico`), and the cardinality of an image is at most that of
its source.  This is the `PBox`-relative form of
`Work.Drive.EpsForm.encard_range_inter_sphereSet_le_encard_param`: the extra hypothesis that the
points lie in the *open* box is carried into the parameterisation. -/
theorem encard_range_inter_PBox_inter_le (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {s : ℝ}
    (S : Set R3) :
    Set.encard (Set.range K.curve ∩ Submission.PBox s c σ ∩ S) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ S} := by
  have hsub : Set.range K.curve ∩ Submission.PBox s c σ ∩ S ⊆
      K.curve '' {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ S} := by
    rintro y ⟨⟨hyR, hyP⟩, hyS⟩
    rw [Work.Drive.EpsForm.range_knot_eq_image_Ico K] at hyR
    obtain ⟨t, ht, rfl⟩ := hyR
    exact ⟨t, ⟨ht, hyP, hyS⟩, rfl⟩
  exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)

/-- **The level count at a level lying above the whole box.**

If the sweep height `ℓ` is *below* the level `lam` at every point of the box (`hhigh`), then the
level region of the sweep is the box minus the closed tilted slab, and its frontier is contained in
the box sphere together with the two faces (`hsub`).  The points of the knot's range on that
frontier therefore lie on the box sphere (counted by `A`) or on one of the two faces *inside the
box* (each counted by `B`), so the count is at most `A + 2B < min p q`.

This is the `encard`-form counting lemma used at the top levels of the window, where the cutting
level has already left the box. -/
theorem encard_frontier_lt_min_at_top (p q : ℕ) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ} {A B : ℕ∞}
    (hs : 0 < s)
    (hhigh : ∀ y ∈ Submission.PBox s c σ, ℓ y < lam)
    (hsub : frontier (Submission.PBox s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ⊆
      Work.BoxShrink.Core.sphereSet c σ s ∪ Work.Drive.Mono.facePlanePlus c u h v ∪
        Work.Drive.Mono.facePlaneMinus c u h v)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hfaceP : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ Work.Drive.Mono.facePlanePlus c u h v} ≤ B)
    (hfaceM : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ K.curve t ∈ Work.Drive.Mono.facePlaneMinus c u h v} ≤ B)
    (harith : A + 2 * B < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) := by
  -- Above the box the level's removed set does not see the level, so it is the box minus the slab.
  have hrem : Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
      Submission.PBox s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
    ext y
    simp only [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyP, hy⟩
      exact ⟨hyP, fun hyS => hy ⟨hyS, hhigh y hyP⟩⟩
    · rintro ⟨hyP, hyS⟩
      exact ⟨hyP, fun hlt => hyS hlt.1⟩
  rw [hrem]
  -- The frontier of the box minus the slab lies in the closed box.
  have hcont : Continuous fun y : R3 => Submission.boxNorm c σ y :=
    Work.Topology.SphereSlicing.frontier_PBox_boxNorm_continuous c σ
  have hFle : frontier (Submission.PBox s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ⊆
      {y : R3 | Submission.boxNorm c σ y ≤ s} := by
    refine frontier_subset_closure.trans ?_
    refine (closure_mono Set.sdiff_subset).trans ?_
    refine closure_minimal ?_ (isClosed_le hcont continuous_const)
    intro y hy
    exact le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy)
  -- Its points in the range of the knot lie on the sphere, or in the box and one of the faces.
  have hcover : Set.range K.curve ∩ frontier (Submission.PBox s c σ \
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ⊆
      (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ∪
        (Set.range K.curve ∩ Submission.PBox s c σ ∩
          Work.Drive.Mono.facePlanePlus c u h v) ∪
        (Set.range K.curve ∩ Submission.PBox s c σ ∩
          Work.Drive.Mono.facePlaneMinus c u h v) := by
    rintro y ⟨hyR, hyF⟩
    have hyle := hFle hyF
    have hU := hsub hyF
    simp only [Set.mem_union] at hU
    rcases hU with (hsp | hfp) | hfm
    · exact Or.inl (Or.inl ⟨hyR, hsp⟩)
    · by_cases hbn : Submission.boxNorm c σ y = s
      · exact Or.inl (Or.inl ⟨hyR, Work.BoxShrink.Core.mem_sphereSet.mpr hbn⟩)
      · exact Or.inl (Or.inr ⟨⟨hyR,
          (Submission.mem_PBox_iff s c σ y).mpr (lt_of_le_of_ne hyle hbn)⟩, hfp⟩)
    · by_cases hbn : Submission.boxNorm c σ y = s
      · exact Or.inl (Or.inl ⟨hyR, Work.BoxShrink.Core.mem_sphereSet.mpr hbn⟩)
      · exact Or.inr ⟨⟨hyR,
          (Submission.mem_PBox_iff s c σ y).mpr (lt_of_le_of_ne hyle hbn)⟩, hfm⟩
  -- The three pieces are counted by `A`, `B`, `B`.
  have hX : Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ≤ A :=
    (Work.Drive.EpsForm.encard_range_inter_sphereSet_le_encard_param K c σ s).trans hS
  have hY : Set.encard (Set.range K.curve ∩ Submission.PBox s c σ ∩
      Work.Drive.Mono.facePlanePlus c u h v) ≤ B :=
    (encard_range_inter_PBox_inter_le K c σ _).trans hfaceP
  have hZ : Set.encard (Set.range K.curve ∩ Submission.PBox s c σ ∩
      Work.Drive.Mono.facePlaneMinus c u h v) ≤ B :=
    (encard_range_inter_PBox_inter_le K c σ _).trans hfaceM
  calc Set.encard (Set.range K.curve ∩ frontier (Submission.PBox s c σ \
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h))
      ≤ Set.encard ((Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ∪
          (Set.range K.curve ∩ Submission.PBox s c σ ∩
            Work.Drive.Mono.facePlanePlus c u h v) ∪
          (Set.range K.curve ∩ Submission.PBox s c σ ∩
            Work.Drive.Mono.facePlaneMinus c u h v)) :=
        Set.encard_le_encard hcover
    _ ≤ Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) +
          Set.encard (Set.range K.curve ∩ Submission.PBox s c σ ∩
            Work.Drive.Mono.facePlanePlus c u h v) +
          Set.encard (Set.range K.curve ∩ Submission.PBox s c σ ∩
            Work.Drive.Mono.facePlaneMinus c u h v) := by
        refine (Set.encard_union_le _ _).trans ?_
        exact add_le_add (Set.encard_union_le _ _) le_rfl
    _ ≤ A + B + B := add_le_add (add_le_add hX hY) hZ
    _ = A + 2 * B := by rw [add_assoc, two_mul]
    _ < (Nat.min p q : ℕ∞) := harith

end Work.Drive.Mono
