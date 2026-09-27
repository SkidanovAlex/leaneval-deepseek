import Mathlib
import Submission.Work.Drive.isOpen_T6GenAtDBox_refTriple
import Submission.Work.Drive.dense_T6GenAtDBox_refTriple
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.norm_blkSpan

namespace Work.Drive

set_option linter.unusedTactic false

/-! ## The block swap of the parameter `ℝ¹² = (ℝ⁴)³`

The two block-`0` producers `Work.Drive.isOpen_T6GenAtDBox_refTriple` and
`Work.Drive.dense_T6GenAtDBox_refTriple` hard-wire *which* block of the parameter carries the core
chart (`blk 0`) and which carries the level-`cblk 1` plane (`blk 1`).  The block-`1` bundle needed by
the `hn2` clause 6 is obtained from the block-`0` one by transporting along the block swap

`σ t := blkSpan 0 (blk 1 t) + blkSpan 1 (blk 0 t) + blkSpan 2 (blk 2 t)`,

which interchanges the first two blocks of `ℝ¹²` and fixes the third.  This section builds `σ` as a
continuous linear map (`refBlkSwapCLM`, whose underlying function is `refBlkSwap`) together with the three
facts the transport uses:

* `blk i (refBlkSwap t) = blk (i ± 1) t` (the block relations `blk_zero_refBlkSwap`, `blk_one_refBlkSwap`,
  `blk_two_refBlkSwap`);
* `refBlkSwap (refBlkSwap t) = t` (`refBlkSwap_invol`);
* `‖refBlkSwap t‖ = ‖t‖` (`norm_refBlkSwap`) — the block swap is a *coordinate permutation* of `ℝ¹²`, hence
  an isometry.  (The triangle inequality only gives `‖refBlkSwap t‖ ≤ 3‖t‖` and does not suffice for the
  ball hypothesis `‖x‖ ≤ 1` of the density statement.)
-/

/-- **The index permutation of `Fin 12`** that interchanges the two four-blocks `0` and `1`: it sends
`i` to `i + 4` on the first block, to `i - 4` on the second and fixes the third. -/
def refBlkSwapIdx (i : Fin 12) : Fin 12 :=
  ⟨if i.val < 4 then i.val + 4 else if i.val < 8 then i.val - 4 else i.val, by
    split_ifs with h1 h2
    · omega
    · omega
    · omega⟩

/-- The index permutation of `Fin 12` as an equivalence (it is an involution). -/
def refBlkSwapIdxEquiv : Fin 12 ≃ Fin 12 where
  toFun := refBlkSwapIdx
  invFun := refBlkSwapIdx
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

/-- **The block swap of the parameter** `ℝ¹² = (ℝ⁴)³`: the first two blocks are exchanged by
`Work.Drive.blkSpan`, the third is kept. -/
noncomputable def refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) : EuclideanSpace ℝ (Fin 12) :=
  blkSpan 0 (blk 1 t) + blkSpan 1 (blk 0 t) + blkSpan 2 (blk 2 t)

/-- **The coordinates of the block swap**: `refBlkSwap` is the permutation `refBlkSwapIdx` of the twelve
coordinates. -/
lemma ofLp_refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) (i : Fin 12) :
    (refBlkSwap t).ofLp i = t.ofLp (refBlkSwapIdx i) := by
  fin_cases i <;>
    simp only [refBlkSwap, PiLp.add_apply, blkSpan_ofLp_apply, blk_apply, refBlkSwapIdx] <;>
    norm_num <;> rfl

/-- **The block swap is an involution.** -/
lemma refBlkSwap_invol (t : EuclideanSpace ℝ (Fin 12)) : refBlkSwap (refBlkSwap t) = t := by
  apply PiLp.ext
  intro i
  have h : refBlkSwapIdx (refBlkSwapIdx i) = i := Equiv.left_inv refBlkSwapIdxEquiv i
  rw [ofLp_refBlkSwap, ofLp_refBlkSwap, h]

/-- **The block swap is an isometry.**  The triangle inequality gives only `‖refBlkSwap t‖ ≤ 3‖t‖`,
which is not enough for the ball hypothesis `‖x‖ ≤ 1` of the density statement; the exact equality
comes from the fact that the block swap permutes the twelve coordinates. -/
lemma norm_refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) : ‖refBlkSwap t‖ = ‖t‖ := by
  have h2 : ‖refBlkSwap t‖ ^ 2 = ‖t‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [show ∑ i : Fin 12, ‖(refBlkSwap t).ofLp i‖ ^ 2
          = ∑ i : Fin 12, ‖t.ofLp (refBlkSwapIdx i)‖ ^ 2 from
      Finset.sum_congr rfl (fun i _ => by rw [ofLp_refBlkSwap])]
    exact Equiv.sum_comp refBlkSwapIdxEquiv (fun i => ‖t.ofLp i‖ ^ 2)
  have ha : 0 ≤ ‖refBlkSwap t‖ := norm_nonneg _
  have hb : 0 ≤ ‖t‖ := norm_nonneg _
  have h := (sq_eq_sq_iff_abs_eq_abs _ _).mp h2
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at h

/-- **The first block of the block swap** is the second block of the parameter. -/
lemma blk_zero_refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) : blk 0 (refBlkSwap t) = blk 1 t := by
  rw [refBlkSwap, map_add, map_add, blk_blkSpan,
    blk_blkSpan_of_ne (k := 1) (j := 0) (by decide),
    blk_blkSpan_of_ne (k := 2) (j := 0) (by decide), add_zero, add_zero]

/-- **The second block of the block swap** is the first block of the parameter. -/
lemma blk_one_refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) : blk 1 (refBlkSwap t) = blk 0 t := by
  rw [refBlkSwap, map_add, map_add, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), zero_add,
    blk_blkSpan, blk_blkSpan_of_ne (k := 2) (j := 1) (by decide), add_zero]

/-- **The third block of the block swap** is the third block of the parameter. -/
lemma blk_two_refBlkSwap (t : EuclideanSpace ℝ (Fin 12)) : blk 2 (refBlkSwap t) = blk 2 t := by
  rw [refBlkSwap, map_add, map_add, blk_blkSpan_of_ne (k := 0) (j := 2) (by decide), zero_add,
    blk_blkSpan_of_ne (k := 1) (j := 2) (by decide), zero_add, blk_blkSpan]

/-! ## `σ` as a continuous linear map -/

/-- **The `k`-th block insertion as a continuous linear map.** -/
noncomputable def blkSpanCLM (k : Fin 3) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 12) :=
  ContinuousLinearMap.comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 12 => ℝ)).symm :
      (Fin 12 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 12))
    (ContinuousLinearMap.pi (fun i : Fin 12 =>
      if i.val / 4 = k.val then
        PiLp.proj 2 (fun _ : Fin 4 => ℝ) ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩
      else 0))

/-- The coordinates of the block insertion `blkSpanCLM`. -/
lemma blkSpanCLM_ofLp (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) (i : Fin 12) :
    (blkSpanCLM k z).ofLp i =
      if i.val / 4 = k.val then z.ofLp ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ else 0 := by
  have h1 : (blkSpanCLM k z).ofLp i =
      ((ContinuousLinearMap.pi (fun i : Fin 12 =>
        if i.val / 4 = k.val then
          PiLp.proj 2 (fun _ : Fin 4 => ℝ) ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩
        else 0)) z) i := rfl
  rw [h1, ContinuousLinearMap.pi_apply]
  split_ifs with h
  · rw [PiLp.proj_apply]
  · rfl

/-- `blkSpanCLM` computes the block-spanning vector. -/
lemma blkSpanCLM_apply (k : Fin 3) (z : EuclideanSpace ℝ (Fin 4)) :
    blkSpanCLM k z = blkSpan k z := by
  apply PiLp.ext
  intro i
  rw [blkSpanCLM_ofLp, blkSpan_ofLp_apply]

/-- **The block swap as a continuous linear map.** -/
noncomputable def refBlkSwapCLM : EuclideanSpace ℝ (Fin 12) →L[ℝ] EuclideanSpace ℝ (Fin 12) :=
  (blkSpanCLM 0).comp (blk 1) + (blkSpanCLM 1).comp (blk 0) + (blkSpanCLM 2).comp (blk 2)

/-- `refBlkSwapCLM` computes the block swap. -/
lemma refBlkSwapCLM_apply (t : EuclideanSpace ℝ (Fin 12)) : refBlkSwapCLM t = refBlkSwap t := by
  simp only [refBlkSwapCLM, refBlkSwap, add_apply, ContinuousLinearMap.comp_apply,
    blkSpanCLM_apply]

/-- `refBlkSwapCLM` is an involution. -/
lemma refBlkSwapCLM_invol (t : EuclideanSpace ℝ (Fin 12)) : refBlkSwapCLM (refBlkSwapCLM t) = t := by
  rw [refBlkSwapCLM_apply, refBlkSwapCLM_apply, refBlkSwap_invol]

/-- **The block-`1` forms of the two `T6` genericity producers of the reference triple.**

`Work.Drive.isOpen_T6GenAtDBox_refTriple` and `Work.Drive.dense_T6GenAtDBox_refTriple` produce the
transport bundle `T6GenAtDBox` at **block `0`** of the reference triple
`![rotPresentation Q u, rotPresentation Q v, R]` (core chart = the perturbed rotated presentation at
angle `u` and block `0`; the two planes = the perturbed rotated presentation at angle `v` at block `1`
and the disk plane `diskPlane QR` at block `2`).  The `hn2` clause 6 needs the *same* bundle at
**block `1`** (core chart = the perturbed rotated presentation at angle `v` at block `1`; the two planes
= the perturbed rotated presentation at angle `u` at block `0` — level `cblk 0` — and the disk plane
`diskPlane QR` at block `2` — level `cblk 2`), which is not an instance of the block-`0` statements
because the *parameter block* of a presentation is hard-wired in `blockChart`/`blockPlane`.
(The consumer is `Work.Drive.refTripleAt_blockT6At_of_data`, `Drive/refTripleClause6Data.lean`;
the transport it feeds is `Work.Drive.refTriple_topBdryMeet_zero_iff_block1`,
`Drive/refTripleBlockT6.lean`.)

RECIPE (transfer along the block-swap of the parameter).
Let `σ t := blkSpan 0 (blk 1 t) + blkSpan 1 (blk 0 t) + blkSpan 2 (blk 2 t)`.  Then
`blk 0 (σ t) = blk 1 t`, `blk 1 (σ t) = blk 0 t`, `blk 2 (σ t) = blk 2 t`, `σ` is linear, `σ (σ t) = t`,
and `σ` is an **isometry**, `‖σ y‖ = ‖y‖` (each `blk i` is a coordinate projection onto a block of four
coordinates, the supports are disjoint, so `‖σ y‖ ^ 2 = ‖blk 0 y‖ ^ 2 + ‖blk 1 y‖ ^ 2 + ‖blk 2 y‖ ^ 2
= ‖y‖ ^ 2`; the triangle inequality only gives `3‖y‖` and is *not* enough for the ball hypothesis
`‖x‖ ≤ 1`).  Instantiate the block-`0` statements with the angle vector `a := ![v, u, u]`, the level
vector `c' := ![cblk 0, cblk 0, cblk 2]` and the same `QR`: the block-`0` bundle at the parameter `σ t`
is the block-`1` bundle at `t` (rewrite with `blk 1 (σ t) = blk 0 t`, `a 0 = v`, `a 1 = u`,
`c' 1 = cblk 0`, `c' 2 = cblk 2`, `blk 2 (σ t) = blk 2 t`, and
`blockPlane … ![v,u,u] … 1 = fun y => chartPert (blk 1 (σ t)) (rotPresentation Q u y)`).
Then: openness is the preimage of the open block-`0` set under the continuous map `σ` (continuity of
`σ` follows from linearity on finite-dimensional spaces; one may also copy the block-`0` openness proof
verbatim with the pattern changed); density follows from the block-`0` density statement at the base
point `σ x` (its half-space hypothesis `0 ≤ (blk 0 (σ x)) 0` is `0 ≤ (blk 1 x) 0`, its ball hypothesis
`‖σ x‖ ≤ 1` follows from `‖x‖ ≤ 1` by the isometry) and the identification above, using `σ (σ t) = t`
and `σ (t - x) = σ t - σ x`.

The two conjuncts are exactly the `hAopen`/`hA0` inputs that the enriched Sard of the `hn2` clause 6
(`Drive/hn2Clause6Sard.lean`) adds to the dense open set of `exists_meet3Hyp_opens_near_zero`, so both
are needed. -/
theorem t6GenAtDBox_refTriple_block1_bundles {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    {QR : ℂ → Work.Drive.CappingSpace} (hQR : Work.Drive.IsSmoothChart QR)
    (hQRseam : ∀ z : ℂ, ‖z‖ = 1 → QR (-z) = QR z)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk 2 < Work.Drive.levelOf (Q z))
    (hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → Work.Drive.levelOf (QR z) > cblk 2) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
        Work.Drive.T6GenAtDBox (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 1 t)
            (Work.Drive.rotCapping v (Q z)))
          (fun y => Work.Drive.chartPert (Work.Drive.blk 0 t) (Work.Drive.rotPresentation Q u y))
          (fun y => Work.Drive.chartPert (Work.Drive.blk 2 t) (Work.Drive.diskPlane QR y))
          (cblk 0) (cblk 2)} ∧
      (∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (Work.Drive.blk 1 x) 0 →
        ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          Work.Drive.T6GenAtDBox (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 1 t)
              (Work.Drive.rotCapping v (Q z)))
            (fun y => Work.Drive.chartPert (Work.Drive.blk 0 t) (Work.Drive.rotPresentation Q u y))
            (fun y => Work.Drive.chartPert (Work.Drive.blk 2 t) (Work.Drive.diskPlane QR y))
            (cblk 0) (cblk 2)) := by
  classical
  -- the level/angle data of the block-`0` statements
  let c' : Fin 3 → ℝ := ![cblk 0, cblk 0, cblk 2]
  have hc'1 : c' 1 = cblk 0 := rfl
  have hc'2 : c' 2 = cblk 2 := rfl
  have hcpos' : ∀ k : Fin 3, 0 < c' k := by
    intro k; fin_cases k <;> simp [c', hcpos]
  have hlev' : ∀ z : ℂ, ‖z‖ ≤ 1 → Work.Drive.levelOf (Q z) > c' 2 := by
    intro z hz; rw [hc'2]; exact hlev z hz
  -- the block-`0` openness statement, in the unfolded form of the three presentations
  have hS0 : IsOpen {s : EuclideanSpace ℝ (Fin 12) |
      Work.Drive.T6GenAtDBox (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 0 s)
          (Work.Drive.rotCapping v (Q z)))
        (fun y => Work.Drive.chartPert (Work.Drive.blk 1 s) (Work.Drive.rotPresentation Q u y))
        (fun y => Work.Drive.chartPert (Work.Drive.blk 2 s) (Work.Drive.diskPlane QR y))
        (c' 1) (c' 2)} := by
    have h := isOpen_T6GenAtDBox_refTriple hQ hQR hQRseam v u c' hcpos'
    unfold blockChart blockPlane at h
    simp only [hc'1, hc'2] at h
    exact h
  refine ⟨?_, ?_⟩
  · -- ## openness: the block-`1` bundle is the block-`0` bundle pulled back along `σ`
    have hset : {t : EuclideanSpace ℝ (Fin 12) |
        Work.Drive.T6GenAtDBox (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 1 t)
            (Work.Drive.rotCapping v (Q z)))
          (fun y => Work.Drive.chartPert (Work.Drive.blk 0 t) (Work.Drive.rotPresentation Q u y))
          (fun y => Work.Drive.chartPert (Work.Drive.blk 2 t) (Work.Drive.diskPlane QR y))
          (cblk 0) (cblk 2)}
        = refBlkSwapCLM ⁻¹' {s : EuclideanSpace ℝ (Fin 12) |
          Work.Drive.T6GenAtDBox (fun z : ℂ => Work.Drive.chartPert (Work.Drive.blk 0 s)
              (Work.Drive.rotCapping v (Q z)))
            (fun y => Work.Drive.chartPert (Work.Drive.blk 1 s) (Work.Drive.rotPresentation Q u y))
            (fun y => Work.Drive.chartPert (Work.Drive.blk 2 s) (Work.Drive.diskPlane QR y))
            (c' 1) (c' 2)} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [refBlkSwapCLM_apply, blk_zero_refBlkSwap, blk_one_refBlkSwap, blk_two_refBlkSwap, hc'1, hc'2]
    rw [hset]
    exact hS0.preimage refBlkSwapCLM.continuous
  · -- ## density: transport the block-`0` density statement along `σ`
    intro x hxle hx0 ε hε
    have hxnorm : ‖refBlkSwapCLM x‖ ≤ 1 := by
      rw [refBlkSwapCLM_apply, norm_refBlkSwap]; exact hxle
    have hxhalf : 0 ≤ (blk 0 (refBlkSwapCLM x)) 0 := by
      rw [refBlkSwapCLM_apply, blk_zero_refBlkSwap]; exact hx0
    obtain ⟨s, hs, hTs⟩ := dense_T6GenAtDBox_refTriple hQ hQR hQRseam v u c' hcpos' hlev' hlevR
      (refBlkSwapCLM x) hxnorm hxhalf ε hε
    refine ⟨refBlkSwapCLM s, ?_, ?_⟩
    · -- the distance: `σ s - x = σ (s - σ x)` and `σ` is an isometry
      have hd : refBlkSwapCLM s - x = refBlkSwapCLM (s - refBlkSwapCLM x) := by
        rw [map_sub, refBlkSwapCLM_invol]
      rw [hd, refBlkSwapCLM_apply, norm_refBlkSwap]
      exact hs
    · -- the bundle at `σ s` is the block-`0` bundle at `s`
      simp only [hc'1, hc'2] at hTs
      unfold blockChart blockPlane at hTs
      simp only [refBlkSwapCLM_apply, blk_zero_refBlkSwap, blk_one_refBlkSwap, blk_two_refBlkSwap] at hTs ⊢
      exact hTs

end Work.Drive
