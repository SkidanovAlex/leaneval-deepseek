import Mathlib
import Submission.Work.Drive.EpsFormSphere.frontier_tiltedSweptBall_eq
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min

/-!
# Counting the knot's trace on the frontier of the removed level of the tilted sweep

The removed set of a level of the tilted sweep is the *difference*

`tiltedLevelRemoved s c σ u v h ℓ lam = PBox s c σ \ (tiltedSlabClosed a v h ∩ {ℓ < lam})`,
`a = ⟪v,c⟫ + u`,

whereas the chunk counted by `Work.Drive.Mono.encard_frontier_chunk_lt_min` is the *intersection*
`PBox ∩ tiltedSlabClosed ∩ {ℓ < lam}`.  The frontier of the difference is covered by the union of
the two frontiers (`frontier_sdiff_subset`), so a point of the knot's range on
`frontier (tiltedLevelRemoved …)` lies

* either on the box sphere `{boxNorm c σ · = s}` (counted by `A`),
* or on the frontier of the removed region `tiltedSlabClosed ∩ {ℓ < lam}`; there it is on a face of
  the tilted slab, `|⟪v,·⟫ - a| = h`, and — if it is not on the box sphere, hence is *inside* the
  open box — it is counted by `B`, or else it is on the wall `{ℓ = lam}` and, being in the closure
  of the closed slab, satisfies `|⟪v,·⟫ - a| ≤ h`, so it is counted by `C`.

This is the counting lemma which converts the three parameter counts of the crux (box sphere, slab
faces, wall inside the box and the closed slab) into the bound on the trace of the removed level
used by the tilted sweep.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The parameter set of the knot's trace on the removed level is covered by the sphere, the slab
faces and the wall**, whence the encard bound `A + B + C`. -/
theorem encard_frontier_levelRemoved_le (K : Knot) {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {A B C : ℕ∞}
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hface : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h} ≤ B)
    (hwall : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h ∧ ℓ (K.curve t) = lam} ≤ C) :
    Set.encard (Set.range K.curve ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) ≤
      A + B + C := by
  -- the wall `{ℓ = lam}` is the frontier of the open half-space `{ℓ < lam}`
  have hfrWall : frontier {y : R3 | ℓ y < lam} ⊆ {y : R3 | ℓ y = lam} := by
    intro y hy
    have hcl : y ∈ closure {z : R3 | ℓ z < lam} := frontier_subset_closure hy
    have hle : ℓ y ≤ lam :=
      closure_minimal (fun z hz => le_of_lt hz) (isClosed_Iic.preimage ℓ.continuous) hcl
    have hnot : ¬ ℓ y < lam := by
      intro hlt
      have hmem : y ∈ interior {z : R3 | ℓ z < lam} := by
        rw [(isOpen_lt ℓ.continuous continuous_const).interior_eq]
        exact hlt
      exact hy.2 hmem
    exact le_antisymm hle (not_lt.mp hnot)
  -- the cover of the parameters
  have hcover : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)} ⊆
      ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s} ∪
       {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h}) ∪
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h ∧ ℓ (K.curve t) = lam} := by
    intro t ht
    obtain ⟨htIco, htfr⟩ := ht
    rw [tiltedLevelRemoved] at htfr
    have hfr := Work.Drive.EpsFormSphere.frontier_sdiff_subset (Submission.PBox s c σ)
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y < lam}) htfr
    have hclA : K.curve t ∈ closure (Submission.PBox s c σ) :=
      closure_mono sdiff_subset (frontier_subset_closure htfr)
    have hbn : Submission.boxNorm c σ (K.curve t) ≤ s := by
      have hsub : Submission.PBox s c σ ⊆ {y : R3 | Submission.boxNorm c σ y ≤ s} :=
        fun y hy => le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy)
      exact closure_minimal hsub
        (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const) hclA
    rcases hfr with hfrA | hfrB
    · exact Or.inl (Or.inl ⟨htIco,
        Work.Drive.EpsFormSphere.frontier_PBox_subset_boxNorm s c σ hfrA⟩)
    · have hclB : K.curve t ∈ closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ y < lam}) := frontier_subset_closure hfrB
      have hle_h : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h := by
        have hclSlab : K.curve t ∈
            closure (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :=
          closure_mono inter_subset_left hclB
        rwa [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).closure_eq]
          at hclSlab
      by_cases hbneq : Submission.boxNorm c σ (K.curve t) = s
      · exact Or.inl (Or.inl ⟨htIco, hbneq⟩)
      · have hbox : K.curve t ∈ Submission.PBox s c σ :=
          (Submission.mem_PBox_iff s c σ _).mpr (lt_of_le_of_ne hbn hbneq)
        rcases frontier_inter_subset (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h)
            {y : R3 | ℓ y < lam} hfrB with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Or.inl (Or.inr ⟨htIco, hbox,
            Work.Drive.EpsFormSphere.frontier_tiltedSlabClosed_subset
              (inner ℝ v c + u) v h h1⟩)
        · exact Or.inr ⟨htIco, hbox, hle_h, hfrWall h2⟩
  -- the count
  refine le_trans (Work.Drive.EpsForm.encard_range_inter_le_param K _) ?_
  refine le_trans (Set.encard_le_encard hcover) ?_
  refine le_trans (Set.encard_union_le _ _) ?_
  refine le_trans (add_le_add (Set.encard_union_le _ _) le_rfl) ?_
  exact add_le_add (add_le_add hS hface) hwall

theorem encard_frontier_lt_min_of_face_wall (p q : ℕ) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {s u h lam : ℝ} {c v : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {A B C : ℕ∞} (hs : 0 < s)
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hface : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h} ≤ B)
    (hwall : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h ∧ ℓ (K.curve t) = lam} ≤ C)
    (harith : A + B + C < (Nat.min p q : ℕ∞)) :
    Set.encard (Set.range K.curve ∩ frontier
        (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) <
      (Nat.min p q : ℕ∞) :=
  lt_of_le_of_lt (encard_frontier_levelRemoved_le K hS hface hwall) harith

end

end Work.Drive.Mono
