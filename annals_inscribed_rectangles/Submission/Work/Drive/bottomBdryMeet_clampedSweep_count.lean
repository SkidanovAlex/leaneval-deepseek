import Mathlib
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.endDistinctLevelDesign
import Submission.Work.Drive.bottomBdryMeet_clampedSweep_eq

/-!
# The end contribution of the corrected design: the bottom count is exactly one

`Submission/Work/Drive/END_LEVEL_OBSTRUCTION.md` §3 prescribes that the three radial sweeps of the end
contribution be truncated at **pairwise distinct** levels `c 0 > c 1 > c 2` (all below the planes'
levels): with equal levels every bottom triple point has all three radial parameters on their bottom
faces, so the face condition of the parity engine fails there
(`Work.Drive.not_faceHyp_of_bottomTriple`); with distinct levels only the block with the largest
truncation level carries a bottom triple point
(`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level`) and the face condition is satisfiable
(`Work.Drive.exists_facePattern_of_distinct_levels`).

This file computes the *value*: with distinct levels the bottom count of the largest block is exactly
**one**, so `Σ_k bottom_k ≡ 1` — the end contribution `n_{-λ} = 1` of Hugelmeyer's Lemmas 3–4.  The two
ingredients are

* the sweep preserves the projective class (`Work.Drive.cls_clampedSweep`), so the three sweeps of a
  triple point agree in class, and that class is pinned to the **collision class** `q` of the three
  rotated planes (the hypotheses `hy`/`huniq` below);
* the level of a sweep is a strictly increasing function of its radial parameter
  (`Work.Drive.existsUnique_levelOf_clampedSweep_eq`), so the two *interior* radial parameters are
  forced by the common level.

So the bottom triple point is: the collision parameters `y k` of the three plane charts, the bottom
face for the block `0`, and the unique interior radial parameters `t 1, t 2` of the other two blocks.
Nothing here needs a *linear* bottom plane, a reparametrisation, or the diagonal obstruction
(`END_CONTRIBUTION_STATUS.md` §2(a)): with the distinct-level design the shadow bottoms suffice.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- The shadow of a point on a level depends only on its projective class. -/
theorem shadow_congr (c : ℝ) (hc : 0 < c) {p p' : CappingSpace}
    (h : (cappingSpaceHomeoProj p).2 = (cappingSpaceHomeoProj p').2) :
    shadow c hc p = shadow c hc p' := by
  apply cappingSpaceHomeoProj.injective
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    show levelOf (shadow c hc p) = levelOf (shadow c hc p')
    rw [levelOf_shadow, levelOf_shadow]
  · rw [cls_shadow, cls_shadow, h]

/-- **A clamped sweep at a prescribed level is the shadow of its plane point.** -/
theorem clampedSweep_eq_shadow_of_level (c c' : ℝ) (hc' : 0 < c') (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
    (h : levelOf (clampedSweep c ψ P (radVec y t)) = c') :
    clampedSweep c ψ P (radVec y t) = shadow c' hc' (P y) := by
  have hpt : mk2 ((radVec y t) 0) ((radVec y t) 1) = y := by
    rw [radVec_apply_zero, radVec_apply_one, mk2_eta]
  have h' : levelOf (scaleCapping (pos (clampScale c ψ P (radVec y t))
      (clampScale_pos c ψ P (radVec y t))) (P y)) = c' := by
    rw [← h, clampedSweep_apply, hpt]
  rw [clampedSweep_apply, hpt]
  exact eq_shadow_of_levelOf_eq c' hc' _ (P y) h'

/-- **The end contribution of the corrected (distinct-level) design is exactly one.**  For three plane
presentations `P k` whose classes collide in a single point `q`, attained uniquely in the box by each
chart (`hy`) and with no other common class (`huniq`), and truncation levels `c 0 > c 1`, `c 2` below
the planes' levels, the bottom triple intersection of the block with the largest truncation level is a
singleton. -/
theorem ncard_bottomBdryMeet_clampedSweep_eq_one
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard = 1 := by
  classical
  set y : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun k => (hy k).choose with hydef
  have hybox : ∀ k, y k ∈ Submission.Drive.unitBox 1 := fun k => ((hy k).choose_spec.1).1
  have hycls : ∀ k, (cappingSpaceHomeoProj (P k (y k))).2 = q := fun k => ((hy k).choose_spec.1).2
  have hyuniq : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 2)), z ∈ Submission.Drive.unitBox 1 →
      (cappingSpaceHomeoProj (P k z)).2 = q → z = y k := by
    intro k z hz hq
    exact (hy k).choose_spec.2 z ⟨hz, hq⟩
  -- the two interior radial parameters of the blocks below the maximal truncation level
  obtain ⟨t1, ht1, ht1u⟩ := existsUnique_levelOf_clampedSweep_eq (c := c 1) (L := c 0) (hc 1)
    hψ0 hψ1 hcont hanti (y := y 1) (hLc := hc1) (hLr := hlev 1 (y 1))
  obtain ⟨t2, ht2, ht2u⟩ := existsUnique_levelOf_clampedSweep_eq (c := c 2) (L := c 0) (hc 2)
    hψ0 hψ1 hcont hanti (y := y 2) (hLc := hc2) (hLr := hlev 2 (y 2))
  -- the candidate bottom triple point
  set Y : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    fun k => ![botVec (y 0 0) (y 0 1), radVec (y 1) t1, radVec (y 2) t2] k with hYdef
  have hY0 : Y 0 = botVec (y 0 0) (y 0 1) := rfl
  have hY1 : Y 1 = radVec (y 1) t1 := rfl
  have hY2 : Y 2 = radVec (y 2) t2 := rfl
  -- the shadows of the three plane points coincide, since their classes do
  have hsh : ∀ j : Fin 3, shadow (c 0) (hc 0) (P j (y j)) = shadow (c 0) (hc 0) (P 0 (y 0)) :=
    fun j => shadow_congr (c 0) (hc 0) (by rw [hycls j, hycls 0])
  refine (Set.ncard_eq_one).mpr ⟨Y, ?_⟩
  ext X
  constructor
  · -- any bottom triple point agrees with the candidate
    intro hX
    obtain ⟨⟨hbox, h01, h02, -⟩, hx0⟩ := hX
    have hmk2 : ∀ k : Fin 3, mk2 (X k 0) (X k 1) ∈ Submission.Drive.unitBox 1 := by
      intro k i
      fin_cases i
      · simpa [mk2_apply_zero] using hbox k 0
      · simpa [mk2_apply_one] using hbox k 1
    -- the three sweeps agree, hence so do the classes of the three plane points
    have hD : ∀ k : Fin 3, clampedSweep (c k) ψ (P k) (X k) = clampedSweep (c 0) ψ (P 0) (X 0) := by
      intro k
      fin_cases k
      · rfl
      · exact h01.symm
      · exact h02.symm
    have hcls_chain : ∀ k : Fin 3,
        (cappingSpaceHomeoProj (P k (mk2 (X k 0) (X k 1)))).2
          = (cappingSpaceHomeoProj (P 0 (mk2 (X 0 0) (X 0 1)))).2 := by
      intro k
      rw [← cls_clampedSweep (c k) ψ (P k) (X k), hD k,
        cls_clampedSweep (c 0) ψ (P 0) (X 0)]
    have hq0 : (cappingSpaceHomeoProj (P 0 (mk2 (X 0 0) (X 0 1)))).2 = q :=
      huniq _ (fun k => ⟨mk2 (X k 0) (X k 1), hmk2 k, hcls_chain k⟩)
    have hclassq : ∀ k : Fin 3, (cappingSpaceHomeoProj (P k (mk2 (X k 0) (X k 1)))).2 = q :=
      fun k => by rw [hcls_chain k]; exact hq0
    -- hence each class coordinate is the corresponding collision parameter
    have hXy : ∀ k : Fin 3, mk2 (X k 0) (X k 1) = y k :=
      fun k => hyuniq k _ (hmk2 k) (hclassq k)
    -- the common level is the maximal truncation level
    have h0lev : levelOf (clampedSweep (c 0) ψ (P 0) (X 0)) = c 0 := by
      rw [clampedSweep_face_zero (c 0) (hc 0) ψ (P 0) hψ0 (X 0) hx0, levelOf_shadow]
    have hklev : ∀ k : Fin 3, levelOf (clampedSweep (c k) ψ (P k) (X k)) = c 0 := by
      intro k
      rw [hD k]
      exact h0lev
    -- the block `0` is at its bottom face
    have hX0 : X 0 = Y 0 := by
      rw [hY0, botVec]
      ext i
      fin_cases i
      · simpa [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hXy 0)
      · simpa [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hXy 0)
      · simpa using hx0
    -- the other two blocks are at the unique interior radial parameter of the level `c 0`
    have hXk1 : X 1 = radVec (y 1) (X 1 2) := by
      rw [radVec]
      ext i
      fin_cases i
      · simpa [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hXy 1)
      · simpa [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hXy 1)
      · simp
    have hmem1 : X 1 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le (hbox 1 2).1 with h | h
        · exfalso
          have hlevc : levelOf (clampedSweep (c 1) ψ (P 1) (X 1)) = c 1 := by
            rw [hXk1, clampedSweep_face_zero (c 1) (hc 1) ψ (P 1) hψ0 (radVec (y 1) (X 1 2))
              (by rw [radVec_apply_two]; exact h.symm), levelOf_shadow]
          rw [hklev 1] at hlevc
          exact absurd hlevc.symm (ne_of_lt hc1)
        · exact h
      · rcases eq_or_lt_of_le (hbox 1 2).2 with h | h
        · exfalso
          have hlevc : levelOf (clampedSweep (c 1) ψ (P 1) (X 1)) = levelOf (P 1 (y 1)) := by
            rw [hXk1, clampedSweep_face_one (c 1) ψ (P 1) hψ1 (radVec (y 1) (X 1 2))
              (by rw [radVec_apply_two]; exact h)]
            simp only [radVec_apply_zero, radVec_apply_one, mk2_eta]
          rw [hklev 1] at hlevc
          exact absurd hlevc.symm (ne_of_gt (hlev 1 (y 1)))
        · exact h
    have hX1 : X 1 = Y 1 := by
      rw [hY1, hXk1, ht1u (X 1 2) ⟨hmem1, by rw [← hXk1]; exact hklev 1⟩]
    have hXk2 : X 2 = radVec (y 2) (X 2 2) := by
      rw [radVec]
      ext i
      fin_cases i
      · simpa [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hXy 2)
      · simpa [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hXy 2)
      · simp
    have hmem2 : X 2 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le (hbox 2 2).1 with h | h
        · exfalso
          have hlevc : levelOf (clampedSweep (c 2) ψ (P 2) (X 2)) = c 2 := by
            rw [hXk2, clampedSweep_face_zero (c 2) (hc 2) ψ (P 2) hψ0 (radVec (y 2) (X 2 2))
              (by rw [radVec_apply_two]; exact h.symm), levelOf_shadow]
          rw [hklev 2] at hlevc
          exact absurd hlevc.symm (ne_of_lt hc2)
        · exact h
      · rcases eq_or_lt_of_le (hbox 2 2).2 with h | h
        · exfalso
          have hlevc : levelOf (clampedSweep (c 2) ψ (P 2) (X 2)) = levelOf (P 2 (y 2)) := by
            rw [hXk2, clampedSweep_face_one (c 2) ψ (P 2) hψ1 (radVec (y 2) (X 2 2))
              (by rw [radVec_apply_two]; exact h)]
            simp only [radVec_apply_zero, radVec_apply_one, mk2_eta]
          rw [hklev 2] at hlevc
          exact absurd hlevc.symm (ne_of_gt (hlev 2 (y 2)))
        · exact h
    have hX2 : X 2 = Y 2 := by
      rw [hY2, hXk2, ht2u (X 2 2) ⟨hmem2, by rw [← hXk2]; exact hklev 2⟩]
    funext k
    fin_cases k
    · exact hX0
    · exact hX1
    · exact hX2
  · -- the candidate is a bottom triple point
    intro hX
    rw [Set.mem_singleton_iff] at hX
    rw [hX]
    have hboxY0 : Y 0 ∈ Submission.Drive.unitBox 2 := by
      rw [hY0]; exact botVec_mem_unitBox _ _ (hybox 0 0) (hybox 0 1)
    have hboxY1 : Y 1 ∈ Submission.Drive.unitBox 2 := by
      rw [hY1]; exact radVec_mem_unitBox (hybox 1) ⟨le_of_lt ht1.1.1, le_of_lt ht1.1.2⟩
    have hboxY2 : Y 2 ∈ Submission.Drive.unitBox 2 := by
      rw [hY2]; exact radVec_mem_unitBox (hybox 2) ⟨le_of_lt ht2.1.1, le_of_lt ht2.1.2⟩
    have hbox : ∀ k : Fin 3, Y k ∈ Submission.Drive.unitBox 2 := by
      intro k
      fin_cases k
      · exact hboxY0
      · exact hboxY1
      · exact hboxY2
    have h01 : clampedSweep (c 0) ψ (P 0) (Y 0) = clampedSweep (c 1) ψ (P 1) (Y 1) := by
      rw [hY0, hY1, clampedSweep_bottom (c 0) (hc 0) ψ hψ0 (P 0) (y 0),
        clampedSweep_eq_shadow_of_level (c 1) (c 0) (hc 0) ψ (P 1) (y 1) t1 ht1.2, hsh 1]
    have h02 : clampedSweep (c 0) ψ (P 0) (Y 0) = clampedSweep (c 2) ψ (P 2) (Y 2) := by
      rw [hY0, hY2, clampedSweep_bottom (c 0) (hc 0) ψ hψ0 (P 0) (y 0),
        clampedSweep_eq_shadow_of_level (c 2) (c 0) (hc 0) ψ (P 2) (y 2) t2 ht2.2, hsh 2]
    have hzero : Y 0 2 = 0 := by rw [hY0]; exact botVec_apply_two _ _
    exact ⟨⟨hbox, h01, h02, ⟨hbox 0, 2, Or.inl hzero⟩⟩, hzero⟩

/-- **The end contribution `Σ_k bottom_k = 1` of the corrected design.**  Packaged form of
`Work.Drive.ncard_bottomBdryMeet_clampedSweep_eq_one`: with pairwise distinct truncation levels
`c 0 > c 1 > c 2` only the largest block carries a bottom triple point
(`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level`), and that one carries exactly one.  This is the
`n_{-λ} = 1` of Hugelmeyer's parity identities. -/
theorem sum_bottomBdryMeet_clampedSweep_eq_one
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard = 1 := by
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y) := by
    intro k y
    fin_cases k
    · exact le_of_lt (hlev 0 y)
    · exact le_trans (le_of_lt hc1) (le_of_lt (hlev 1 y))
    · exact le_trans (le_of_lt hc2) (le_of_lt (hlev 2 y))
  have h1 : Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level c hc ψ hψ0 hψ01 P hlev' (k := 1) (l := 0) hc1
  have h2 : Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level c hc ψ hψ0 hψ01 P hlev' (k := 2) (l := 0) hc2
  rw [h1, h2]
  simp only [Set.ncard_empty, add_zero]
  exact ncard_bottomBdryMeet_clampedSweep_eq_one c hc hc1 hc2 ψ hψ0 hψ1 hcont hanti P hlev q hy huniq

/-- **A block whose truncation level is not maximal has no bottom triple intersection** (local form of
`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level`, with the cutoff bounded only on `[0,1]`, which is what
the endgame's profile `ψ t = 1 - t` satisfies). -/
theorem bottomBdryMeet_eq_empty_of_lt_level_local
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y))
    {k l : Fin 3} (hlt : c k < c l) :
    Work.Drive.bottomBdryMeet CappingSpace (fun i => clampedSweep (c i) ψ (P i)) k = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hbox, h01, h02, -⟩, hk2⟩
  have hLk : levelOf (clampedSweep (c k) ψ (P k) (x k)) = c k := by
    rw [clampedSweep_face_zero (c k) (hc k) ψ (P k) hψ0 (x k) hk2, levelOf_shadow]
  have hD : ∀ i : Fin 3, clampedSweep (c i) ψ (P i) (x i)
      = clampedSweep (c 0) ψ (P 0) (x 0) := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
  have hLl : levelOf (clampedSweep (c l) ψ (P l) (x l)) = c k := by
    rw [hD l, ← hD k, hLk]
  have hle : c l ≤ levelOf (clampedSweep (c l) ψ (P l) (x l)) :=
    le_levelOf_clampedSweep_local (hc l) hψ01 (P l) (x l) (hbox l 2)
      (hlev l (mk2 (x l 0) (x l 1)))
  rw [hLl] at hle
  exact absurd hle (not_le.mpr hlt)

/-- **The end contribution `Σ_k bottom_k = 1` of the corrected design, in local-cutoff form.** -/
theorem sum_bottomBdryMeet_clampedSweep_eq_one_local
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard = 1 := by
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y) := by
    intro k y
    fin_cases k
    · exact le_of_lt (hlev 0 y)
    · exact le_trans (le_of_lt hc1) (le_of_lt (hlev 1 y))
    · exact le_trans (le_of_lt hc2) (le_of_lt (hlev 2 y))
  have h1 : Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local c hc ψ hψ0 hψ01 P hlev' (k := 1) (l := 0) hc1
  have h2 : Work.Drive.bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local c hc ψ hψ0 hψ01 P hlev' (k := 2) (l := 0) hc2
  rw [h1, h2]
  simp only [Set.ncard_empty, add_zero]
  exact ncard_bottomBdryMeet_clampedSweep_eq_one c hc hc1 hc2 ψ hψ0 hψ1 hcont hanti P hlev q hy huniq

end

end Work.Drive
