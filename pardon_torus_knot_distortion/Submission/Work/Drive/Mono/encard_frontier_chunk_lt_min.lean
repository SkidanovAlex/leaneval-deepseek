import Mathlib
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_levelChunk

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- **The frontier of a triple intersection** is contained in the union of the three frontiers.
(Immediate from `frontier_inter_subset`, applied twice.) -/
theorem frontier_inter_three_subset {X : Type*} [TopologicalSpace X] (A B C : Set X) :
    frontier (A ∩ B ∩ C) ⊆ frontier A ∪ frontier B ∪ frontier C := by
  intro y hy
  rcases frontier_inter_subset (A ∩ B) C hy with ⟨h1, -⟩ | ⟨-, h2⟩
  · rcases frontier_inter_subset A B h1 with ⟨h3, -⟩ | ⟨-, h3⟩
    · exact Or.inl (Or.inl h3)
    · exact Or.inl (Or.inr h3)
  · exact Or.inr h2

/-- **The counting lemma for the frontier of the removed chunk of a level of the tilted sweep.**

Let `R = PBox s c σ ∩ tiltedSlabClosed (⟪v,c⟫ + u) v h ∩ {ℓ < lam}` be the chunk cut out of the
box by the tilted slab and the wall `{ℓ = lam}`.  A point of `frontier R` lies on the box sphere
(`boxNorm c σ · = s`), or on one of the two faces of the slab (`|⟪v,·⟫ - (⟪v,c⟫+u)| = h`), or on
the wall (`ℓ · = lam`, and then in the closed slab).  Hence the points of the knot's range on
`frontier R` are counted by the parameters of the knot on the box sphere (`A`), on the slab faces
inside the box (`B`) and on the wall inside the box and the closed slab (`C`); the `encard` of the
range is at most the `encard` of the parameter set (`K` is `2π`-periodic, so its range is the image
of the fundamental interval). -/
theorem encard_frontier_chunk_le (K : Knot) {s u h lam : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {A B C : ℕ∞}
    (hS : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} ≤ A)
    (hface : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h} ≤ B)
    (hwall : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h ∧ ℓ (K.curve t) = lam} ≤ C) :
    Set.encard (Set.range K.curve ∩ frontier (Submission.PBox s c σ ∩
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : R3 | ℓ y < lam})) ≤ A + B + C := by
  -- the two projections of the chunk
  have hRP : (Submission.PBox s c σ ∩
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < lam}) ⊆ Submission.PBox s c σ := fun y hy => hy.1.1
  have hRS : (Submission.PBox s c σ ∩
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
      {y : R3 | ℓ y < lam}) ⊆
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := fun y hy => hy.1.2
  -- the wall is the frontier of the open half-space
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
  -- the closure of the box is contained in the closed box
  have hclPBox : closure (Submission.PBox s c σ) ⊆
      {y : R3 | Submission.boxNorm c σ y ≤ s} :=
    closure_minimal (fun y hy => le_of_lt ((Submission.mem_PBox_iff s c σ y).mp hy))
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const)
  -- ### the parameter set of the frontier splits into the sphere, the faces and the wall
  have hcover : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ frontier (Submission.PBox s c σ ∩
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
          {y : R3 | ℓ y < lam})} ⊆
      ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s} ∪
       {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h}) ∪
      {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ ∧
          |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h ∧ ℓ (K.curve t) = lam} := by
    intro t ht
    obtain ⟨htIco, htfr⟩ := ht
    have hclR : K.curve t ∈ closure (Submission.PBox s c σ ∩
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : R3 | ℓ y < lam}) := frontier_subset_closure htfr
    have hbn : Submission.boxNorm c σ (K.curve t) ≤ s :=
      hclPBox (closure_mono hRP hclR)
    by_cases hbneq : Submission.boxNorm c σ (K.curve t) = s
    · exact Or.inl (Or.inl ⟨htIco, hbneq⟩)
    · have hbox : K.curve t ∈ Submission.PBox s c σ :=
        (Submission.mem_PBox_iff s c σ _).mpr (lt_of_le_of_ne hbn hbneq)
      have hfr_sub : K.curve t ∈ frontier (Submission.PBox s c σ) ∪
          frontier (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) ∪
          frontier {y : R3 | ℓ y < lam} :=
        frontier_inter_three_subset _ _ _ htfr
      rcases hfr_sub with hfr1 | hfr2
      · rcases hfr1 with hfrA | hfrB
        · -- on the box frontier: the box norm equals `s`, contrary to `hbneq`
          exact absurd (Work.Drive.EpsFormSphere.frontier_PBox_subset_boxNorm s c σ hfrA) hbneq
        · -- on a face of the slab
          exact Or.inl (Or.inr ⟨htIco, hbox,
            Work.Drive.EpsFormSphere.frontier_tiltedSlabClosed_subset
              (inner ℝ v c + u) v h hfrB⟩)
      · -- on the wall; the point is in the closure of the chunk, hence in the closed slab
        have hlam : ℓ (K.curve t) = lam := hfrWall hfr2
        have hle_h : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h := by
          have h2 : K.curve t ∈ closure
              (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :=
            closure_mono hRS hclR
          rwa [(Work.Drive.EpsForm.isClosed_tiltedSlabClosed (inner ℝ v c + u) v h).closure_eq]
            at h2
        exact Or.inr ⟨htIco, hbox, hle_h, hlam⟩
  -- ### the count
  refine le_trans (Work.Drive.EpsForm.encard_range_inter_le_param K _) ?_
  refine le_trans (Set.encard_le_encard hcover) ?_
  refine le_trans (Set.encard_union_le _ _) ?_
  refine le_trans (add_le_add (Set.encard_union_le _ _) le_rfl) ?_
  exact add_le_add (add_le_add hS hface) hwall

end

theorem encard_frontier_chunk_lt_min (p q : ℕ) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {s u h lam : ℝ} {c v : LeanEval.KnotTheory.PardonDistortion.R3}
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
    Set.encard (Set.range K.curve ∩ frontier (Submission.PBox s c σ ∩
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩
        {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y < lam})) <
      (Nat.min p q : ℕ∞) :=
  lt_of_le_of_lt (encard_frontier_chunk_le K hS hface hwall) harith

end Work.Drive.Mono
