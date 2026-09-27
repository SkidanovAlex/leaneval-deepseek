import Mathlib
import Submission.Work.Drive.endLevelObstruction
import Submission.Work.Drive.exists_radial_level_eq_of_lt_level

/-!
# The corrected end design: pairwise distinct truncation levels do satisfy the face condition

`Submission/Work/Drive/END_LEVEL_OBSTRUCTION.md` §3 prescribes that the three radial sweeps of the end
contribution be truncated at **pairwise distinct** levels `c 0 > c 1 > c 2` (all below the planes'
levels): with equal levels every bottom triple point has all three radial coordinates on their bottom
faces, so the face condition of the parity engine (`Work.Drive.Meet3Hyp.face`,
`Work.Drive.Meet3Generic.face`) is false there; with distinct levels only the block with the largest
truncation level can be on its bottom face (`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level`).

This file shows that the corrected design *does* produce a bottom boundary triple intersection at which
the face condition holds: given a point `y` of the class square whose three shadows on the level `c 0`
coincide (the design's free choice of the three bottom `2`-cycles), there is a parameter triple `x` at
which the three *sweeps* meet, whose `0`-th parameter is on its bottom face and whose other two radial
coordinates are strictly interior — and if the class coordinates of `y` are strictly interior, the
"unique face coordinate" pattern of the face condition holds at `x`.  The two radial parameters are
supplied by `Work.Drive.exists_radial_level_eq_of_lt_level` (a sweep truncated at `c j < c 0` meets the
level `c 0` at an interior radial parameter).

So: **the face condition is satisfiable in the corrected design, and the bottom count is nonzero** —
which is exactly what the equal-level design cannot have.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The level of a radial dilation**: `scaleCapping` multiplies the level by the scale.  (Local copy
of `Work.Drive.levelOf_scaleCapping`: the module `Submission/Work/Drive/levelOf_clampedSweep.lean` that
declares it cannot be imported together with `clampedSweepChart.lean`, see
`END_LEVEL_OBSTRUCTION.md` §5.) -/
lemma levelOf_scaleCappingEnd (A : Work.Drive.Pos) (p : CappingSpace) :
    levelOf (scaleCapping A p) = (A : ℝ) * levelOf p := by
  rw [levelOf, levelOf, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

/-- A radial dilation of `p` whose level is `c` is the shadow of `p` on the level `c`. -/
lemma eq_shadow_of_levelOf_eq (c : ℝ) (hc : 0 < c) (A : Work.Drive.Pos) (p : CappingSpace)
    (h : levelOf (scaleCapping A p) = c) :
    scaleCapping A p = shadow c hc p := by
  have hp : 0 < levelOf p := levelOf_pos p
  have hmul : (A : ℝ) * levelOf p = c := by
    rw [← levelOf_scaleCappingEnd A p]; exact h
  have hA : (A : ℝ) = c / levelOf p := by
    rw [eq_div_iff (ne_of_gt hp)]; exact hmul
  rw [shadow]
  exact congrArg (fun B : Work.Drive.Pos => scaleCapping B p) (Subtype.ext hA)

/-- A point with prescribed class coordinates and a radial coordinate in `[0,1]` lies in the cube. -/
lemma radVec_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : radVec y t ∈ Submission.Drive.unitBox 2 := by
  intro i
  fin_cases i
  · show y 0 ∈ Set.Icc (0 : ℝ) 1
    exact hy 0
  · show y 1 ∈ Set.Icc (0 : ℝ) 1
    exact hy 1
  · show t ∈ Set.Icc (0 : ℝ) 1
    exact ht

/-- **The corrected end design.**  With `c 0 > c 1`, `c 2` (all below the planes' levels), a point `y`
of the class square whose three shadows on the level `c 0` coincide and whose class coordinates are
strictly interior gives a triple point `x` of the three sweeps with `x 0 2 = 0`, `x 1 2, x 2 2 ∈ (0,1)`
and every other coordinate strictly interior — i.e. a boundary triple point of
`bottomBdryMeet CappingSpace D 0` at which the face condition holds. -/
theorem exists_facePattern_of_distinct_levels
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hy : ∀ k, y k ∈ Submission.Drive.unitBox 1)
    (hyint : ∀ (k : Fin 3) (i : Fin 2), y k i ∈ Set.Ioo (0 : ℝ) 1)
    (hmeet : shadow (c 0) (hc 0) (P 0 (y 0)) = shadow (c 0) (hc 0) (P 1 (y 1)) ∧
      shadow (c 0) (hc 0) (P 0 (y 0)) = shadow (c 0) (hc 0) (P 2 (y 2))) :
    ∃ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) ∧
      clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) ∧
      clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) ∧
      x ∈ Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0 ∧
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) := by
  classical
  obtain ⟨t1, ht1, hlev1⟩ :=
    exists_radial_level_eq_of_lt_level (c 0) (c 1) (hc 1) hc1 ψ hψ0 hψ1 hcont (P 1) (y 1)
      (hlev 1 (y 1))
  obtain ⟨t2, ht2, hlev2⟩ :=
    exists_radial_level_eq_of_lt_level (c 0) (c 2) (hc 2) hc2 ψ hψ0 hψ1 hcont (P 2) (y 2)
      (hlev 2 (y 2))
  -- the sweep of block `j` at the radial parameter supplied by the intermediate value theorem is the
  -- shadow of its plane point on the level `c 0`
  have key : ∀ (j : Fin 3) (t : ℝ),
      levelOf (clampedSweep (c j) ψ (P j) (radVec (y j) t)) = c 0 →
      clampedSweep (c j) ψ (P j) (radVec (y j) t) = shadow (c 0) (hc 0) (P j (y j)) := by
    intro j t ht
    have hpoint : mk2 (radVec (y j) t 0) (radVec (y j) t 1) = y j := by
      rw [radVec_apply_zero, radVec_apply_one, mk2_eta]
    have hclamp : clampedSweep (c j) ψ (P j) (radVec (y j) t)
        = scaleCapping (pos (clampScale (c j) ψ (P j) (radVec (y j) t))
            (clampScale_pos (c j) ψ (P j) (radVec (y j) t))) (P j (y j)) := by
      rw [clampedSweep_apply, hpoint]
    rw [hclamp] at ht ⊢
    exact eq_shadow_of_levelOf_eq (c 0) (hc 0) _ (P j (y j)) ht
  let A : EuclideanSpace ℝ (Fin 3) := botVec (y 0 0) (y 0 1)
  let B : EuclideanSpace ℝ (Fin 3) := radVec (y 1) t1
  let C : EuclideanSpace ℝ (Fin 3) := radVec (y 2) t2
  let X : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun k => ![A, B, C] k
  have hX : ∀ k : Fin 3, X k = ![A, B, C] k := fun k => rfl
  have hA0 : A 2 = 0 := botVec_apply_two (y 0 0) (y 0 1)
  have hboxA : A ∈ Submission.Drive.unitBox 2 :=
    botVec_mem_unitBox _ _ (hy 0 0) (hy 0 1)
  have hboxB : B ∈ Submission.Drive.unitBox 2 :=
    radVec_mem_unitBox (hy 1) ⟨ht1.1.le, ht1.2.le⟩
  have hboxC : C ∈ Submission.Drive.unitBox 2 :=
    radVec_mem_unitBox (hy 2) ⟨ht2.1.le, ht2.2.le⟩
  have hbox : ∀ k, X k ∈ Submission.Drive.unitBox 2 := by
    intro k
    fin_cases k
    · rw [hX]; show A ∈ Submission.Drive.unitBox 2; exact hboxA
    · rw [hX]; show B ∈ Submission.Drive.unitBox 2; exact hboxB
    · rw [hX]; show C ∈ Submission.Drive.unitBox 2; exact hboxC
  have heq1 : clampedSweep (c 0) ψ (P 0) (X 0) = clampedSweep (c 1) ψ (P 1) (X 1) := by
    rw [hX]
    show clampedSweep (c 0) ψ (P 0) A = clampedSweep (c 1) ψ (P 1) B
    rw [show A = botVec (y 0 0) (y 0 1) from rfl, show B = radVec (y 1) t1 from rfl,
      clampedSweep_bottom (c 0) (hc 0) ψ hψ0 (P 0) (y 0), key 1 t1 hlev1, hmeet.1]
  have heq2 : clampedSweep (c 0) ψ (P 0) (X 0) = clampedSweep (c 2) ψ (P 2) (X 2) := by
    rw [hX]
    show clampedSweep (c 0) ψ (P 0) A = clampedSweep (c 2) ψ (P 2) C
    rw [show A = botVec (y 0 0) (y 0 1) from rfl, show C = radVec (y 2) t2 from rfl,
      clampedSweep_bottom (c 0) (hc 0) ψ hψ0 (P 0) (y 0), key 2 t2 hlev2, hmeet.2]
  have hzero : X 0 2 = 0 := by
    rw [hX]
    show A 2 = 0
    exact hA0
  have hbox0 : X 0 ∈ Submission.Drive.unitBox 2 := hbox 0
  have hmem : X ∈ Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0 :=
    ⟨⟨hbox, heq1, heq2, ⟨hbox0, ⟨(2 : Fin 3), Or.inl hzero⟩⟩⟩, hzero⟩
  have hface : ∃ (k : Fin 3) (i : Fin 3), (X k i = 0 ∨ X k i = 1) ∧
      (∀ j : Fin 3, j ≠ i → X k j ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, X k' j ∈ Set.Ioo (0 : ℝ) 1) := by
    refine ⟨0, 2, Or.inl hzero, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · rw [hX]
        show A 0 ∈ Set.Ioo (0 : ℝ) 1
        exact hyint 0 0
      · rw [hX]
        show A 1 ∈ Set.Ioo (0 : ℝ) 1
        exact hyint 0 1
      · exact absurd rfl hj
    · intro k' hk' j
      fin_cases k'
      · exact absurd rfl hk'
      · rw [hX]
        show B j ∈ Set.Ioo (0 : ℝ) 1
        fin_cases j
        · show y 1 0 ∈ Set.Ioo (0 : ℝ) 1
          exact hyint 1 0
        · show y 1 1 ∈ Set.Ioo (0 : ℝ) 1
          exact hyint 1 1
        · show t1 ∈ Set.Ioo (0 : ℝ) 1
          exact ht1
      · rw [hX]
        show C j ∈ Set.Ioo (0 : ℝ) 1
        fin_cases j
        · show y 2 0 ∈ Set.Ioo (0 : ℝ) 1
          exact hyint 2 0
        · show y 2 1 ∈ Set.Ioo (0 : ℝ) 1
          exact hyint 2 1
        · show t2 ∈ Set.Ioo (0 : ℝ) 1
          exact ht2
  exact ⟨X, hbox, heq1, heq2, hmem, hface⟩

end

end Work.Drive
