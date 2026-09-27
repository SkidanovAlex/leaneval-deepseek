import Mathlib
import Submission.Work.Drive.clampedSweepChart
import Submission.Work.Drive.SeamMeetDefs

/-!
# The truncation levels of the end sweeps: what the bottom triple points force

*(agent owning `Submission/Work/Drive/parityCore_of_isSmoothEmbedding.lean`.)*

The end contribution of the chain route (`ENDS_AND_SEAMS_NOTES.md` §2, `COUNTING_HALF_REMAINING.md` §3)
is computed from the *bottom faces* of the three radial sweeps `D k = clampedSweep (c k) ψ (P k)`:
`bottomBdryMeet CappingSpace D k` is the set of *boundary triple points* `x ∈ (unitBox 2)³` at which
the three sweeps agree and `x k 2 = 0`.  The route needs the corresponding count to be **odd** (it is
the `n_{−λ}` of Hugelmeyer's parity identity, `n_{−λ} = 1`), and the engine
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes` needs the *face condition*
`Work.Drive.Meet3Generic.face` at every boundary triple point: exactly one coordinate of exactly one
parameter is on a face, everything else strictly interior.

This file records what the geometry of the clamped sweep forces on the truncation levels.

* `Work.Drive.le_levelOf_clampedSweep`: for a cutoff with values in `[0,1]` and a truncation level `c`
  below the plane's levels, the level of the sweep is `≥ c`.
* `Work.Drive.level_eq_of_bottomTriple`: at a bottom triple point the common level is the truncation
  level `c k` of the block that is on its bottom face.
* **`Work.Drive.le_trunc_of_bottomTriple`**: hence `c k ≤ c j` for *every* other block `j`; in
  particular **a block whose truncation level is strictly smaller than another's can never be the one
  on its bottom face at a triple point** (`Work.Drive.not_bottomTriple_of_lt`).
* **`Work.Drive.eq_zero_all_of_bottomTriple`**: if all three truncation levels are *equal* to `c`, then
  every bottom triple point has `x 0 2 = x 1 2 = x 2 2 = 0`, i.e. **all three** parameters are on their
  bottom faces.
* **`Work.Drive.not_faceHyp_of_bottomTriple`**: a point all three of whose radial coordinates vanish
  satisfies *none* of the "unique face coordinate" patterns — so `Meet3Hyp.face` (and the engine's
  `hface`/`Meet3Generic.face`) **fails** at every bottom triple point of the equal-level design.

## Consequences for the endgame design

`ENDS_AND_SEAMS_NOTES.md` §2 instructs that the three bottom faces be chosen to be three linear
projective planes **of one level**, and `LINEAR_PLANE_CHAPTER.md` §1 computes the end contribution as
`Σ_k bottom_k = 3 · #(Z_0 ∩ Z_1 ∩ Z_2) ≡ 1`.  The lemmas here show that this *cannot* be combined with
the face condition the engine needs:

* with **equal** truncation levels `c 0 = c 1 = c 2 = c`, every bottom triple point has
  `x 0 2 = x 1 2 = x 2 2 = 0` (`eq_zero_all_of_bottomTriple`, and `eq_zero_all_of_mem_bottomBdryMeet`
  in the engine's vocabulary) — so all three parameters are on a face, and the "unique face coordinate"
  requirement of `Meet3Hyp.face` / `Meet3Generic.face` / the engine's `hface` is **false** there
  (`not_faceHyp_of_bottomTriple`; `exists_bottomTriple_not_facePattern_of_commonShadow` produces such a
  point as soon as the design's three bottoms actually meet, which is exactly the case in which
  `Σ_k bottom_k` is odd);
* with **pairwise distinct** truncation levels, `bottomBdryMeet D k = ∅` for every non-maximal `k`
  (`bottomBdryMeet_eq_empty_of_lt_level`), so `Σ_k bottom_k` is the *single* count of the block with
  the largest truncation level.

The corrected design is therefore: **truncate the three sweeps at pairwise distinct levels** (all below
the planes' levels), so that the face condition is satisfiable, and arrange the *one* surviving bottom
count to be odd.  See `END_LEVEL_OBSTRUCTION.md` for the discussion and for the open construction this
leaves.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The level of a clamped sweep is at least its truncation level.**  For a cutoff with values in
`[0,1]` and a plane whose levels are all `≥ c`, the radial coordinate of `clampedSweep c ψ P x` is
`r · (c/r)^{ψ (x 2)} ≥ c`. -/
theorem le_levelOf_clampedSweep (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hr : c ≤ levelOf (P (mk2 (x 0) (x 1)))) :
    c ≤ levelOf (clampedSweep c ψ P x) := by
  have hrpos : 0 < levelOf (P (mk2 (x 0) (x 1))) := levelOf_pos _
  rw [levelOf_clampedSweep, clampScale]
  set r : ℝ := levelOf (P (mk2 (x 0) (x 1))) with hrdef
  have hlog : Real.log c ≤ Real.log r := Real.log_le_log hc hr
  have hd : Real.log c - Real.log r ≤ 0 := by linarith
  have hu1 : ψ (x 2) ≤ 1 := (hψ01 (x 2)).2
  have hu0 : 0 ≤ ψ (x 2) := (hψ01 (x 2)).1
  have hmul : (1 : ℝ) * (Real.log c - Real.log r)
      ≤ ψ (x 2) * (Real.log c - Real.log r) := by
    have h : (1 - ψ (x 2)) * (Real.log c - Real.log r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hd
    nlinarith
  have hexp : Real.exp (Real.log c - Real.log r)
      ≤ Real.exp (ψ (x 2) * (Real.log c - Real.log r)) :=
    Real.exp_le_exp.mpr (by simpa using hmul)
  have hbase : Real.exp (Real.log c - Real.log r) * r = c := by
    rw [Real.exp_sub, Real.exp_log hc, Real.exp_log hrpos,
      div_mul_cancel₀ c (ne_of_gt hrpos)]
  calc c = Real.exp (Real.log c - Real.log r) * r := hbase.symm
    _ ≤ Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r :=
        mul_le_mul_of_nonneg_right hexp (le_of_lt hrpos)

/-- **The sweep meets its own truncation level only at its bottom face.**  Local form of
`Work.Drive.levelOf_clampedSweep` of `Submission/Work/Drive/levelOf_clampedSweep.lean`, reproduced here
under a different name because that module's declaration of the same name clashes with
`Work.Drive.levelOf_clampedSweep` of `Submission/Work/Drive/clampedSweepChart.lean` (which this file
imports). -/
theorem levelOf_clampedSweep_eq_bottom (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψlt : ∀ t : ℝ, 0 < t → ψ t < 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3))
    (hx : 0 ≤ x 2) (hrc : levelOf (P (mk2 (x 0) (x 1))) ≠ c) :
    levelOf (clampedSweep c ψ P x) = c ↔ x 2 = 0 := by
  constructor
  · intro h
    set r : ℝ := levelOf (P (mk2 (x 0) (x 1))) with hrdef
    have hr : 0 < r := by rw [hrdef]; exact levelOf_pos _
    have hrne : r ≠ c := by rw [hrdef]; exact hrc
    have hlev : levelOf (clampedSweep c ψ P x)
        = Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r := by
      rw [levelOf_clampedSweep, clampScale, hrdef]
    have h1 : Real.exp (ψ (x 2) * (Real.log c - Real.log r)) * r = c := by
      rw [← hlev, h]
    have h2 : Real.exp (Real.log c - Real.log r) * r = c := by
      rw [Real.exp_sub, Real.exp_log hc, Real.exp_log hr, div_mul_cancel₀ c (ne_of_gt hr)]
    have hexp : Real.exp (ψ (x 2) * (Real.log c - Real.log r))
        = Real.exp (Real.log c - Real.log r) :=
      mul_right_cancel₀ (ne_of_gt hr) (h1.trans h2.symm)
    have hlogne : Real.log c - Real.log r ≠ 0 := by
      intro h0
      exact hrne ((Real.log_injOn_pos (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr hr)
        (sub_eq_zero.mp h0)).symm)
    have hψ1 : ψ (x 2) = 1 := by
      have hx2 := Real.exp_eq_exp.mp hexp
      exact mul_right_cancel₀ hlogne (by rw [hx2, one_mul])
    by_contra hxne
    exact absurd hψ1 (ne_of_lt (hψlt (x 2) (lt_of_le_of_ne hx (Ne.symm hxne))))
  · intro hx0
    have hr : 0 < levelOf (P (mk2 (x 0) (x 1))) := levelOf_pos _
    rw [levelOf_clampedSweep, clampScale, hx0, hψ0, one_mul, Real.exp_sub,
      Real.exp_log hc, Real.exp_log hr, div_mul_cancel₀ c (ne_of_gt hr)]

/-- **The common level at a bottom triple point is the truncation level of the block on its bottom
face.**  All three levels agree (the three sweeps meet in one point), and the level of the block whose
radial coordinate is `0` is its truncation level by `Work.Drive.clampedSweep_face_zero`. -/
theorem level_eq_of_bottomTriple (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h01 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2))
    {k : Fin 3} (hk : x k 2 = 0) (j : Fin 3) :
    levelOf (clampedSweep (c j) ψ (P j) (x j)) = c k := by
  have hLk : levelOf (clampedSweep (c k) ψ (P k) (x k)) = c k := by
    rw [clampedSweep_face_zero (c k) (hc k) ψ (P k) hψ0 (x k) hk,
      levelOf_shadow (c k) (hc k)]
  have hL : ∀ i : Fin 3, levelOf (clampedSweep (c i) ψ (P i) (x i))
      = levelOf (clampedSweep (c 0) ψ (P 0) (x 0)) := by
    intro i
    fin_cases i
    · rfl
    · exact (congrArg levelOf h01).symm
    · exact (congrArg levelOf h02).symm
  rw [hL j]
  exact (hL k).symm.trans hLk

/-- **Only a block with a maximal truncation level can be the one on its bottom face at a triple
point.** -/
theorem le_trunc_of_bottomTriple (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h01 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2))
    {k j : Fin 3} (hk : x k 2 = 0) :
    c j ≤ c k := by
  rw [← level_eq_of_bottomTriple c hc ψ hψ0 P x h01 h02 hk j]
  exact le_levelOf_clampedSweep (c j) (hc j) ψ hψ01 (P j) (x j)
    (hlev j (mk2 (x j 0) (x j 1)))

/-- **A block whose truncation level is strictly smaller than another's is never the one on its bottom
face at a triple point.** -/
theorem not_bottomTriple_of_lt (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h01 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2))
    {k j : Fin 3} (hlt : c k < c j) : x k 2 ≠ 0 := by
  intro hk
  exact absurd (le_trunc_of_bottomTriple c hc ψ hψ0 hψ01 P hlev x h01 h02 hk) (not_le.mpr hlt)

/-- **Equal truncation levels: every bottom triple point has all three radial coordinates zero.** -/
theorem eq_zero_all_of_bottomTriple (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψlt : ∀ t : ℝ, 0 < t → ψ t < 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), levelOf (P k y) ≠ c)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hbox : ∀ k, x k ∈ Submission.Drive.unitBox 2)
    (h01 : clampedSweep c ψ (P 0) (x 0) = clampedSweep c ψ (P 1) (x 1))
    (h02 : clampedSweep c ψ (P 0) (x 0) = clampedSweep c ψ (P 2) (x 2))
    {k : Fin 3} (hk : x k 2 = 0) :
    x 0 2 = 0 ∧ x 1 2 = 0 ∧ x 2 2 = 0 := by
  have hcommon : ∀ j : Fin 3, levelOf (clampedSweep c ψ (P j) (x j)) = c := by
    intro j
    have h := level_eq_of_bottomTriple (fun _ => c) (fun _ => hc) ψ hψ0 P x
      (by simpa using h01) (by simpa using h02) hk j
    simpa using h
  have hone : ∀ j : Fin 3, x j 2 = 0 := by
    intro j
    have hx0 : 0 ≤ x j 2 := (hbox j 2).1
    exact (levelOf_clampedSweep_eq_bottom c hc ψ hψ0 hψlt (P j) (x j) hx0
      (hlev j (mk2 (x j 0) (x j 1)))).mp (hcommon j)
  exact ⟨hone 0, hone 1, hone 2⟩

/-- **A point all three of whose radial coordinates vanish satisfies none of the "unique face
coordinate" patterns.**  Hence the face condition of the parity engine (`Meet3Hyp.face`,
`Meet3Generic.face`, the engine's `hface`) fails at every such point. -/
theorem not_faceHyp_of_bottomTriple (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h0 : x 0 2 = 0) (h1 : x 1 2 = 0) (h2 : x 2 2 = 0) :
    ¬ (∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
      (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) := by
  rintro ⟨k, i, -, hi, hall⟩
  have hk : x k 2 = 0 := by fin_cases k <;> assumption
  by_cases hi2 : i = 2
  · obtain ⟨k', hk'⟩ : ∃ k' : Fin 3, k' ≠ k := by
      fin_cases k
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have hk'2 : x k' 2 = 0 := by
      fin_cases k' <;> assumption
    have := (hall k' hk' 2).1
    rw [hk'2] at this
    exact lt_irrefl 0 this
  · have hne : (2 : Fin 3) ≠ i := fun h => hi2 h.symm
    have := (hi 2 hne).1
    rw [hk] at this
    exact lt_irrefl 0 this

/-- The three-vector `(a, b, 0)` used to lift the parameters of a bottom face to a cube parameter. -/
def botVec (a b : ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a, b, 0]

@[simp] lemma botVec_apply_zero (a b : ℝ) : botVec a b 0 = a := rfl

@[simp] lemma botVec_apply_one (a b : ℝ) : botVec a b 1 = b := rfl

@[simp] lemma botVec_apply_two (a b : ℝ) : botVec a b 2 = 0 := rfl

lemma botVec_mem_unitBox (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    botVec a b ∈ Submission.Drive.unitBox 2 := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simp

lemma mk2_botVec (a b : ℝ) : mk2 (botVec a b 0) (botVec a b 1) = mk2 a b := by
  simp

/-- The bottom face of the clamped sweep of a plane at the square parameter `y`. -/
lemma clampedSweep_bottom (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (y : EuclideanSpace ℝ (Fin 2)) :
    clampedSweep c ψ P (botVec (y 0) (y 1)) = shadow c hc (P y) := by
  rw [clampedSweep_face_zero c hc ψ P hψ0 _ (botVec_apply_two _ _), mk2_botVec, mk2_eta]

/-- **If the three bottom faces of the clamped sweeps meet, then the face condition of the parity
engine fails at a bottom triple point.**  Concretely: from a common point of the three bottom shadows
one builds a boundary triple point `x` of the parameter cubes at which **all three** radial coordinates
vanish (when the three truncation levels are equal and below the planes' levels), and
`Work.Drive.not_faceHyp_of_bottomTriple` shows that no "unique face coordinate" pattern holds there.
So `Meet3Hyp.face` / `Meet3Generic.face` / the engine's `hface` is *false* for the equal-level design,
whenever the design's bottoms actually meet (which the end contribution requires, since
`Σ_k bottom_k` has to be odd). -/
theorem exists_bottomTriple_not_facePattern_of_commonShadow (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hy : ∀ k, y k ∈ Submission.Drive.unitBox 1)
    (hmeet : shadow c hc (P 0 (y 0)) = shadow c hc (P 1 (y 1)) ∧
      shadow c hc (P 0 (y 0)) = shadow c hc (P 2 (y 2))) :
    ∃ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) ∧
      clampedSweep c ψ (P 0) (x 0) = clampedSweep c ψ (P 1) (x 1) ∧
      clampedSweep c ψ (P 0) (x 0) = clampedSweep c ψ (P 2) (x 2) ∧
      x 0 2 = 0 ∧ x 1 2 = 0 ∧ x 2 2 = 0 ∧
      ¬ (∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) := by
  refine ⟨fun k => botVec (y k 0) (y k 1), fun k => botVec_mem_unitBox _ _ (hy k 0) (hy k 1), ?_, ?_,
    rfl, rfl, rfl, ?_⟩
  · rw [clampedSweep_bottom c hc ψ hψ0 (P 0) (y 0), clampedSweep_bottom c hc ψ hψ0 (P 1) (y 1),
      hmeet.1]
  · rw [clampedSweep_bottom c hc ψ hψ0 (P 0) (y 0), clampedSweep_bottom c hc ψ hψ0 (P 2) (y 2),
      hmeet.2]
  · exact not_faceHyp_of_bottomTriple _ rfl rfl rfl

/-- The three-vector `(y 0, y 1, t)`: a cube parameter with prescribed class coordinates and radial
coordinate. -/
def radVec (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![y 0, y 1, t]

@[simp] lemma radVec_apply_zero (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : radVec y t 0 = y 0 := rfl

@[simp] lemma radVec_apply_one (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : radVec y t 1 = y 1 := rfl

@[simp] lemma radVec_apply_two (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : radVec y t 2 = t := rfl

/-- **In the engine's own vocabulary: a block whose truncation level is not maximal has no bottom
boundary triple intersection.** -/
theorem bottomBdryMeet_eq_empty_of_lt_level (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y))
    {k l : Fin 3} (hlt : c k < c l) :
    Work.Drive.bottomBdryMeet CappingSpace (fun i => clampedSweep (c i) ψ (P i)) k = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h01, h02, -⟩, hk2⟩
  exact not_bottomTriple_of_lt c hc ψ hψ0 hψ01 P hlev x h01 h02 hlt hk2

/-- **In the engine's own vocabulary: with all three truncation levels equal, every bottom boundary
triple intersection has all three radial coordinates on their bottom faces.** -/
theorem eq_zero_all_of_mem_bottomBdryMeet (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1)
    (hψlt : ∀ t : ℝ, 0 < t → ψ t < 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), levelOf (P k y) ≠ c)
    {x : Fin 3 → EuclideanSpace ℝ (Fin 3)} {k : Fin 3}
    (hx : x ∈ Work.Drive.bottomBdryMeet CappingSpace (fun i => clampedSweep c ψ (P i)) k) :
    x 0 2 = 0 ∧ x 1 2 = 0 ∧ x 2 2 = 0 := by
  obtain ⟨⟨hbox, h01, h02, -⟩, hk2⟩ := hx
  exact eq_zero_all_of_bottomTriple c hc ψ hψ0 hψlt P hlev x hbox h01 h02 hk2

/-- **At a bottom corner the common tangent direction of three clamped sweeps points *into* the
cube.**  `Work.Drive.tripleCommonDir_clampedSweeps` gives the common direction of the three sweeps as
`(1 / A k) • e₂` with `A k = deriv ψ (x k 2) · (log (c k) − log r k)`; at a bottom corner
(`x k 2 = 0`), with a strictly decreasing cutoff at `0` and truncation levels below the planes' levels
(`c k < r k`), the two factors of `A k` are both negative, so `A k > 0` and the radial component
`1 / A k` of the common direction is **positive**.  This is the *entry condition* that a relaxation of
`Work.Drive.boxParity` / `Work.Drive.manifold_triple_inter_boundary_parity` to corner boundary points
needs (transversality alone does not force a curve to enter a cube at a corner, see
`Work.Drive.not_boxParity_of_forall_face` and `END_LEVEL_OBSTRUCTION.md` §2bis). -/
theorem pos_radialCoeff_of_bottom (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψd : deriv ψ 0 < 0)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k < levelOf (P k y))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ k, x k 2 = 0) (k : Fin 3) :
    0 < 1 / (deriv ψ (x k 2) * (Real.log (c k)
      - Real.log (levelOf (P k (mk2 (x k 0) (x k 1)))))) := by
  have hr : 0 < levelOf (P k (mk2 (x k 0) (x k 1))) := levelOf_pos _
  have hcr : c k < levelOf (P k (mk2 (x k 0) (x k 1))) := hlev k _
  have hlog : Real.log (c k) - Real.log (levelOf (P k (mk2 (x k 0) (x k 1)))) < 0 :=
    sub_neg.mpr (Real.log_lt_log (hc k) hcr)
  have hd : deriv ψ (x k 2) < 0 := by rw [hx k]; exact hψd
  exact one_div_pos.mpr (mul_pos_of_neg_of_neg hd hlog)

end

end Work.Drive
