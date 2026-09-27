import Mathlib
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.endLevelObstruction

/-!
# The level lift: a common-class triple of the planes is a triple point of the radial sweeps

`Work.Drive.endTripleReg_of_meet3Hyp_sweeps` (the row-1 producer of the ends clause) needs, at a
common-class triple of plane parameters `y k`, a *sweep* triple point `x k` whose plane parameter is
`y k` — because `Meet3Hyp.trans` is only available at triple points of the three sweeps.

This file constructs it: block `0` sits on the radial face `x 0 2 = 0` (where the sweep of level
`c 0` *is* the shadow of the plane on the level `c 0`, `Work.Drive.clampedSweep_face_zero`), and the
other two blocks are lifted along their radial coordinate by the unique-interior-parameter theorem
`Work.Drive.existsUnique_levelOf_clampedSweep_eq`.  The three lifted points then have the same level
`c 0` and the same projective class (`Work.Drive.cls_clampedSweep` and the common class of the `y k`),
hence are the same point of the capping space `(0,∞) × ℝP³`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- The plane parameter of the lifted point `radVec y t` is `y`. -/
lemma mk2_radVec (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mk2 (radVec y t 0) (radVec y t 1) = y := by
  ext i
  fin_cases i <;> simp [radVec, mk2]

/-- **The level lift.**  A triple of plane parameters with a common projective class, lying in the
closed unit square and whose planes have levels strictly above the truncation level `c 0`, is the plane
parameter of a triple point of the three radial sweeps at the levels `c k` (with `c 0` the largest). -/
theorem exists_sweepTriple_of_commonClass
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hcpos : ∀ k, 0 < c k) (hc10 : c 1 < c 0) (hc20 : c 2 < c 0)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hcont : ContinuousOn ψ (Set.Icc 0 1))
    (hanti : StrictAntiOn ψ (Set.Icc 0 1))
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hy : ∀ k, y k ∈ Submission.Drive.unitBox 1)
    (hlev : ∀ k, c 0 < Work.Drive.levelOf (P k (y k)))
    (hcls : ∀ k, Work.Drive.planeClassMap (P k) (y k) = Work.Drive.planeClassMap (P 0) (y 0)) :
    ∃ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) ∧
      (∀ k, Work.Drive.mk2 (x k 0) (x k 1) = y k) ∧
      (∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
        = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)) := by
  obtain ⟨t1, ht1, -⟩ :=
    Work.Drive.existsUnique_levelOf_clampedSweep_eq (c := c 1) (L := c 0) (hcpos 1)
      hψ0 hψ1 hcont hanti hc10 (hlev 1)
  obtain ⟨t2, ht2, -⟩ :=
    Work.Drive.existsUnique_levelOf_clampedSweep_eq (c := c 2) (L := c 0) (hcpos 2)
      hψ0 hψ1 hcont hanti hc20 (hlev 2)
  refine ⟨![Work.Drive.radVec (y 0) 0, Work.Drive.radVec (y 1) t1, Work.Drive.radVec (y 2) t2],
    ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · -- block `0` lies on the radial face
      intro i
      fin_cases i
      · simpa [Work.Drive.radVec, mk2] using hy 0 0
      · simpa [Work.Drive.radVec, mk2] using hy 0 1
      · simp [Work.Drive.radVec]
    · intro i
      fin_cases i
      · simpa [Work.Drive.radVec, mk2] using hy 1 0
      · simpa [Work.Drive.radVec, mk2] using hy 1 1
      · exact ⟨le_of_lt ht1.1.1, le_of_lt ht1.1.2⟩
    · intro i
      fin_cases i
      · simpa [Work.Drive.radVec, mk2] using hy 2 0
      · simpa [Work.Drive.radVec, mk2] using hy 2 1
      · exact ⟨le_of_lt ht2.1.1, le_of_lt ht2.1.2⟩
  · intro k
    fin_cases k
    · exact mk2_radVec (y 0) 0
    · exact mk2_radVec (y 1) t1
    · exact mk2_radVec (y 2) t2
  · intro k
    have hlvl0 : Work.Drive.levelOf
        (Work.Drive.clampedSweep (c 0) ψ (P 0) (Work.Drive.radVec (y 0) 0)) = c 0 := by
      rw [Work.Drive.clampedSweep_face_zero (c 0) (hcpos 0) ψ (P 0) hψ0 _
          (by simp [Work.Drive.radVec]), Work.Drive.levelOf_shadow]
    have hcl : ∀ k : Fin 3,
        (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) (Work.Drive.radVec (y k) (if k = 0 then 0 else if k = 1 then t1 else t2)))).2
          = (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c 0) ψ (P 0) (Work.Drive.radVec (y 0) 0))).2 := by
      intro k
      rw [Work.Drive.cls_clampedSweep, Work.Drive.cls_clampedSweep, mk2_radVec, mk2_radVec]
      exact hcls k
    fin_cases k
    · rfl
    · refine Work.Drive.cappingSpaceHomeoProj.injective (Prod.ext ?_ (hcl 1))
      exact Subtype.ext (by
        have h1 : Work.Drive.levelOf
            (Work.Drive.clampedSweep (c 1) ψ (P 1) (Work.Drive.radVec (y 1) t1)) = c 0 := ht1.2
        simp only [if_neg (by decide : ¬ (1 : Fin 3) = 0), if_pos rfl]
        simpa [Work.Drive.levelOf] using h1.trans hlvl0.symm)
    · refine Work.Drive.cappingSpaceHomeoProj.injective (Prod.ext ?_ (hcl 2))
      exact Subtype.ext (by
        have h2 : Work.Drive.levelOf
            (Work.Drive.clampedSweep (c 2) ψ (P 2) (Work.Drive.radVec (y 2) t2)) = c 0 := ht2.2
        simp only [if_neg (by decide : ¬ (2 : Fin 3) = 0), if_neg (by decide : ¬ (2 : Fin 3) = 1)]
        simpa [Work.Drive.levelOf] using h2.trans hlvl0.symm)

end

end Work.Drive
