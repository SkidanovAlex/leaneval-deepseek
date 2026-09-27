import Mathlib
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.hdenseNodeGerm
import Submission.Work.Drive.hdenseNodeE3
import Submission.Work.Drive.blockT6Wrapper
import Submission.Work.Drive.exists_small_chartPert_disjoint
import Submission.Work.Drive.meet3Hyp_perm
import Submission.Work.Drive.sweepTripleRot
import Submission.Work.Drive.cutTransport
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.chartPlaneDisjoint

/-!
# The block-level transport of the `hdense` design (§4.2 of `NOTES_LEAD_hodd_blockT6.md`)

**This is the `hdense` lane's own piece** (`NOTES_LEAD_hodd_blockT6.md` §5, "H4-L1574 (hdense)"): the
per-block instantiation of the transport wrapper
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` (`Drive/blockT6Wrapper.lean`, §4.1) at
the design's three blocks, i.e. the producer of `Work.Drive.BlockT6AtN` from the design's goodness data
`Work.Drive.DesignGoodData`, the three `Work.Drive.T6GenAtDBox` bundles and the whole-plane
disjointness `hdisjZc`.

Contents:

* `Work.Drive.chartPert_rotCapping_comm_unit` — the `UnitAddCircle`-angle form of `chartPert`'s
  equivariance under the rotations;
* `Work.Drive.disjoint_perturbed_blocks_of_small` (§5 P1 of `NOTES_LEAD_hdense.md`) — the design's
  pairwise whole-plane disjointness for small parameters, *proved* here from the already-proved
  `Work.Drive.exists_small_chartPert_disjoint` plus the range dictionary of the blocks;
* `Work.Drive.level_blockChart_of_small` — the level bands of the design's blocks at a small
  parameter, from `Work.Drive.levelOf_pertChart_loop`;
* the block-level smoothness/seam API of `blockChart`/`blockPlane`;
* `Work.Drive.BlockT6AtN_of_design` — the §4.2 assembly: `ncard_topBdryMeet_eq_perm` +
  `meet3Hyp_reindex_add` + the wrapper.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The chart perturbation is equivariant under the rotations, in the `UnitAddCircle` angle.** -/
lemma chartPert_rotCapping_comm_unit (w : UnitAddCircle) (s : EuclideanSpace ℝ (Fin 4))
    (p : CappingSpace) : chartPert s (rotCapping w p) = rotCapping w (chartPert s p) := by
  obtain ⟨v, hv⟩ := Quotient.mk''_surjective w
  rw [← hv]
  exact chartPert_rotCapping_comm v s p


/-- **The block plane is the perturbed rotated chart**, in the `rotCapping` form: the rotation applied
to the unperturbed disk, then perturbed. -/
lemma blockPlane_eq_chartPert_rotCapping (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)) :
    blockPlane (fun s p => chartPert s p) Q u τ k y
      = chartPert (τ k) (rotCapping (u k) (diskPlane Q y)) := by
  rw [show blockPlane (fun s p => chartPert s p) Q u τ k y
      = chartPert (τ k) (rotPresentation Q (u k) y) from rfl]
  rw [rotPresentation, diskPlane_apply]
  rfl

/-- **The block chart is the perturbed rotated chart.** -/
lemma blockChart_eq_chartPert_rotCapping (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) (z : ℂ) :
    blockChart (fun s p => chartPert s p) Q u τ k z
      = chartPert (τ k) (rotCapping (u k) (Q z)) := rfl

/-- **The design's perturbed blocks are pairwise disjoint at a small parameter.**  For the three
rotated plane presentations `rotPresentation Q (u k)` of the design, perturbed by the small parameters
`blk k t`, the chart's disk image of the block `k` misses the plane of the block `j`, and the planes of
two distinct blocks miss each other, as soon as `‖t‖` is small.

This is §5 P1 of `NOTES_LEAD_hdense.md`: the "small-`Ξ` robustness" of the whole-plane disjointness,
obtained from the already-proved `Work.Drive.exists_small_chartPert_disjoint` (two *independent*
perturbations of two disjoint compact disks) and the range dictionary
`Set.range (blockPlane Ξ Q u τ j) = Ξ (τ j) '' rotCapping (u j) '' chartDisk Q` of the blocks. -/
theorem disjoint_perturbed_blocks_of_small {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u : Fin 3 → UnitAddCircle) (hu : ∀ k j : Fin 3, k ≠ j → u j - u k ∈ Zc γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ρ →
      (∀ k j : Fin 3, k ≠ j → ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z
          ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y) ∧
      (∀ k j : Fin 3, k ≠ j → ∀ y y' : EuclideanSpace ℝ (Fin 2),
        blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) k y
          ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y') := by
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- ## 1. one radius per ordered pair of distinct blocks
  let ι := {q : Fin 3 × Fin 3 // q.1 ≠ q.2}
  haveI : Fintype ι := Fintype.ofFinite ι
  have hpair : ∀ q : ι, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ t t' : EuclideanSpace ℝ (Fin 4), ‖t‖ < ρ → ‖t'‖ < ρ →
        Disjoint (chartDisk (pertChart (fun s p => chartPert s p) Q t))
          (rotCapping (u q.1.2 - u q.1.1) ''
            chartDisk (pertChart (fun s p => chartPert s p) Q t')) :=
    fun q => exists_small_chartPert_disjoint hQ.1 hΞc hdisjZc (hu q.1.1 q.1.2 q.2)
  choose ρf hρfpos hρf using hpair
  let S : Finset ℝ := Finset.univ.image ρf
  have hSne : S.Nonempty :=
    ⟨ρf ⟨(0, 1), by decide⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hSpos : ∀ r ∈ S, 0 < r := by
    intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact hρfpos q
  refine ⟨S.min' hSne, hSpos _ (Finset.min'_mem _ _), ?_⟩
  intro t ht
  have htq : ∀ q : ι, ‖t‖ < ρf q := fun q =>
    lt_of_lt_of_le ht (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩))
  -- ## 2. the block-vs-block contradiction
  have key : ∀ (k j : Fin 3) (hkj : k ≠ j) (p q : CappingSpace), p ∈ chartDisk Q →
      q ∈ chartDisk Q →
      chartPert (blk k t) (rotCapping (u k) p) ≠ rotCapping (u j) (chartPert (blk j t) q) := by
    intro k j hkj p q hp hq heq
    have hd := hρf ⟨(k, j), hkj⟩ (blk k t) (blk j t)
      (lt_of_le_of_lt (norm_blk_le k t) (htq ⟨(k, j), hkj⟩))
      (lt_of_le_of_lt (norm_blk_le j t) (htq ⟨(k, j), hkj⟩))
    rw [chartPert_rotCapping_comm_unit (u k) (blk k t) p] at heq
    have hconj : rotCapping (u j) (chartPert (blk j t) q)
        = rotCapping (u k) (rotCapping (u j - u k) (chartPert (blk j t) q)) := by
      rw [rotCapping_apply_add]
      congr 1
      abel
    rw [hconj] at heq
    have h3 : chartPert (blk k t) p
        = rotCapping (u j - u k) (chartPert (blk j t) q) :=
      rotCapping_injective (u k) heq
    have hm1 : chartPert (blk k t) p
        ∈ chartDisk (pertChart (fun s p => chartPert s p) Q (blk k t)) := by
      rw [chartDisk_pertChart]
      exact ⟨p, hp, rfl⟩
    have hm2 : chartPert (blk j t) q
        ∈ chartDisk (pertChart (fun s p => chartPert s p) Q (blk j t)) := by
      rw [chartDisk_pertChart]
      exact ⟨q, hq, rfl⟩
    exact (Set.disjoint_left.mp hd hm1) ⟨chartPert (blk j t) q, hm2, h3.symm⟩
  -- ## 3. the two pointwise conclusions
  have hmem : ∀ y : EuclideanSpace ℝ (Fin 2), diskPlane Q y ∈ chartDisk Q := by
    intro y
    refine ⟨sqDisk (foldBox y), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox y)
    · rw [diskPlane_apply]
  constructor
  · intro k j hkj z y hz
    have hz' : Q z ∈ chartDisk Q :=
      ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact hz, rfl⟩
    have hbc : blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z
        = chartPert (blk k t) (rotCapping (u k) (Q z)) :=
      blockChart_eq_chartPert_rotCapping Q u (fun i => blk i t) k z
    have hbp : blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y
        = rotCapping (u j) (chartPert (blk j t) (diskPlane Q y)) := by
      rw [blockPlane_eq_chartPert_rotCapping, chartPert_rotCapping_comm_unit]
    rw [hbc, hbp]
    exact key k j hkj (Q z) (diskPlane Q y) hz' (hmem y)
  · intro k j hkj y y'
    have hbp : blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) k y
        = chartPert (blk k t) (rotCapping (u k) (diskPlane Q y)) :=
      blockPlane_eq_chartPert_rotCapping Q u (fun i => blk i t) k y
    have hbp' : blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y'
        = rotCapping (u j) (chartPert (blk j t) (diskPlane Q y')) := by
      rw [blockPlane_eq_chartPert_rotCapping, chartPert_rotCapping_comm_unit]
    rw [hbp, hbp']
    exact key k j hkj (diskPlane Q y) (diskPlane Q y') (hmem y) (hmem y')

/-- **The level bands of the design's blocks at a small parameter.**  If the unperturbed chart's disk
lies above the level `c` and the truncation levels `cblk` are all below `c`, then for a small parameter
`t` the level of every block chart on the closed disk is above every `cblk i`. -/
theorem level_blockChart_of_small {Q : ℂ → CappingSpace} (hQ : IsSmoothChart Q) {c : ℝ}
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (u : Fin 3 → UnitAddCircle) {cblk : Fin 3 → ℝ}
    (hcblk : ∀ i : Fin 3, cblk i < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ρ →
      ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → ∀ i : Fin 3,
        cblk i < levelOf (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k z) := by
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hper : ∀ k : Fin 3, ∃ ε : ℝ, 0 < ε ∧
      ∀ a : EuclideanSpace ℝ (Fin 4), ‖a‖ < ε →
        ∀ p ∈ rotCapping (u k) '' chartDisk Q, c < levelOf (chartPert a p) := by
    intro k
    obtain ⟨ε, hε, hε'⟩ := levelOf_pertChart_loop (Ξ := fun s p => chartPert s p) hΞc
      (K := rotCapping (u k) '' chartDisk Q) (c := c)
      ((chartDisk_compact hQ.continuous).image (continuous_rotCapping (u k)))
      (fun p hp => by
        rcases hp with ⟨q, hq, rfl⟩
        rw [levelOf_rotCapping]
        exact hcbot q hq)
    exact ⟨ε, hε, fun a ha p hp => hε' a p ha hp⟩
  choose εf hεfpos hεf using hper
  let S : Finset ℝ := Finset.univ.image εf
  have hSne : S.Nonempty := ⟨εf 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hSpos : ∀ r ∈ S, 0 < r := by
    intro r hr
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hr
    exact hεfpos k
  refine ⟨S.min' hSne, hSpos _ (Finset.min'_mem _ _), ?_⟩
  intro t ht k z hz i
  have htk : ‖t‖ < εf k :=
    lt_of_lt_of_le ht (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩))
  have hbtk : ‖blk k t‖ < εf k := lt_of_le_of_lt (norm_blk_le k t) htk
  have hp : rotCapping (u k) (Q z) ∈ rotCapping (u k) '' chartDisk Q :=
    ⟨Q z, ⟨z, by rw [Metric.mem_closedBall, dist_zero_right]; exact hz, rfl⟩, rfl⟩
  have h := hεf k (blk k t) hbtk _ hp
  show cblk i < levelOf (chartPert (blk k t) (rotCapping (u k) (Q z)))
  exact lt_trans (hcblk i) h

/-! ## The block-level smoothness/seam API and the §4.2 assembly -/

/-- **Smoothness of a block chart** of the perturbed design. -/
lemma contMDiff_blockChart (Q : ℂ → CappingSpace)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (hΞsm : ∀ s : EuclideanSpace ℝ (Fin 4),
      ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Ξ s))
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (blockChart Ξ Q u τ k) := by
  have h1 : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => rotCapping (u k) (Q z)) :=
    (contMDiff_rotCapping_const (u k)).comp hQ
  show ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℂ => Ξ (τ k) (rotCapping (u k) (Q z)))
  exact (hΞsm (τ k)).comp h1

/-- **Seam invariance of a block plane**: a rotation of a seam-invariant chart is seam-invariant. -/
lemma blockPlane_seam (Q : ℂ → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) :
    ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      blockPlane Ξ Q u τ k y = blockPlane Ξ Q u τ k (seamInv2 y) := by
  intro y hy
  show Ξ (τ k) (rotPresentation Q (u k) y) = Ξ (τ k) (rotPresentation Q (u k) (seamInv2 y))
  rw [rotPresentation_seamInv Q hQseam (u k) y hy]

/-- **The `Fin 3` bookkeeping of the cyclic relabelling of the blocks.** -/
private lemma fin3_add_zero (k : Fin 3) : (0 : Fin 3) + k = k := by
  apply Fin.ext
  simp [Fin.val_add, Nat.mod_eq_of_lt k.isLt]

/-- `k ≠ k + 1` in `Fin 3`. -/
private lemma fin3_ne_add_one (k : Fin 3) : k ≠ k + 1 := by fin_cases k <;> decide

/-- `k ≠ k + 2` in `Fin 3`. -/
private lemma fin3_ne_add_two (k : Fin 3) : k ≠ k + 2 := by fin_cases k <;> decide

/-- `k + 1 ≠ k + 2` in `Fin 3`. -/
private lemma fin3_add_one_ne_add_two (k : Fin 3) : k + 1 ≠ k + 2 := by fin_cases k <;> decide

/-- **The `hdense` design's block transport (§4.2 of `NOTES_LEAD_hodd_blockT6.md`).**  Given the design's
`Meet3Hyp` of the three radial sweeps, the three box-restricted transport bundles `T6GenAtDBox` of the
blocks, the pairwise separation of the blocks and the level bands, the transport `T6` holds at **every**
block `k` of the design, i.e. `Work.Drive.BlockT6AtN` — the per-block conclusion the endpoint
`Work.Drive.hdense_identity_of_designTripleAtN` consumes.

Proof: at block `k` the triple of the wrapper is the *cyclic* relabelling of the design's triple
(`Work.Drive.ncard_topBdryMeet_eq_perm` for the count, `Work.Drive.meet3Hyp_reindex_add` for the
`Meet3Hyp`), and the block's chart/planes are `Qk`/`P₁`/`P₂`; then the wrapper
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` applies verbatim. -/
theorem BlockT6AtN_of_design {Q : ℂ → CappingSpace} (hQ : IsChartData Q) (c : ℝ)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (t : EuclideanSpace ℝ (Fin 12))
    (hDG : Meet3Hyp CappingSpace (sweepChartFam (fun j => rotPresentation Q (u j))
      (fun s p => chartPert s p) cblk t))
    (hgen : ∀ k : Fin 3, T6GenAtDBox
      (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
      (cblk (k + 1)) (cblk (k + 2)))
    (hsep : ∀ k j : Fin 3, k ≠ j →
      ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
        blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z
          ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y)
    (hsep' : ∀ k j : Fin 3, k ≠ j → ∀ y y' : EuclideanSpace ℝ (Fin 2),
        blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) k y
          ≠ blockPlane (fun s p => chartPert s p) Q u (fun i => blk i t) j y')
    (hlev : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → max (cblk (k + 1)) (cblk (k + 2))
        < levelOf (blockChart (fun s p => chartPert s p) Q u (fun i => blk i t) k z)) :
    BlockT6AtN Q c cblk u t  := by
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hΞsm := fun s => contMDiff_apply_of_chartPert hΞc s
  have hQd : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diskPlane Q) :=
    contMDiff_diskPlane (Q := Q) hQ.1
  intro k
  -- ## the design's Meet3Hyp and its cyclic relabelling
  have hfam0 : sweepChartFam (fun j => rotPresentation Q (u j)) (fun s p => chartPert s p) cblk t
      = (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) := by
    funext j x
    rfl
  have hDG' : Meet3Hyp CappingSpace (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) := by
    have h := hDG
    rw [hfam0] at h
    exact h
  have hD : Meet3Hyp CappingSpace (fun i : Fin 3 => (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) (i + k)) :=
    meet3Hyp_reindex_add hDG' k
  -- ## the family of the wrapper is that relabelling
  have hfam : (fun i : Fin 3 => clampedSweep (![cblk k, cblk (k + 1), cblk (k + 2)] i)
        (fun r => 1 - r)
        (![diskPlane (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))] i))
      = (fun i : Fin 3 => (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) (i + k)) := by
    funext i
    fin_cases i <;> fin_cases k <;>
      simp [designSweep, diskPlane_blockChart]
  have hM : Meet3Hyp CappingSpace (fun i : Fin 3 =>
      clampedSweep (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun r => 1 - r)
        (![diskPlane (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))] i)) := by
    rw [hfam]
    exact hD
  have hgk : T6GenAtDBox (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2)) (cblk (k + 1)) (cblk (k + 2)) := hgen k
  -- ## the wrapper at block `k`, with all its arguments as local data
  have hQc : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) :=
    contMDiff_blockChart Q hQ.1 (fun s p => chartPert s p) hΞsm u (fun j => blk j t) k
  have hQseamC : ∀ z : ℂ, ‖z‖ = 1 → ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)) (-z) = ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)) z :=
    blockChart_seam (fun s p => chartPert s p) Q u (fun j => blk j t) k hQ.2
  have hP₁c : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) :=
    contMDiff_blockPlane (fun s p => chartPert s p) hΞsm Q u (fun j => blk j t) (k + 1) hQd
  have hP₂c : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))) :=
    contMDiff_blockPlane (fun s p => chartPert s p) hΞsm Q u (fun j => blk j t) (k + 2) hQd
  have hP₁seamC : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) y = ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) (seamInv2 y) :=
    blockPlane_seam Q hQ.2 (fun s p => chartPert s p) u (fun j => blk j t) (k + 1)
  have hP₂seamC : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))) y = ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))) (seamInv2 y) :=
    blockPlane_seam Q hQ.2 (fun s p => chartPert s p) u (fun j => blk j t) (k + 2)
  have hdisj₁C : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)) z ≠ ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) y :=
    fun z y hz => hsep k (k + 1) (fin3_ne_add_one k) z y hz
  have hdisj₂C : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)) z ≠ ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))) y :=
    fun z y hz => hsep k (k + 2) (fin3_ne_add_two k) z y hz
  have hdisj₁₂C : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) y ≠ ((blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))) y' :=
    fun y y' => hsep' (k + 1) (k + 2) (fin3_add_one_ne_add_two k) y y'
  have hlev₁C : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 1) < levelOf ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) z) :=
    fun z hz => lt_of_le_of_lt (le_max_left _ _) (hlev k z hz)
  have hlev₂C : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < levelOf ((blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) z) :=
    fun z hz => lt_of_le_of_lt (le_max_right _ _) (hlev k z hz)
  have hwrap := odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp
    (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))
    (cblk k) (cblk (k + 1)) (cblk (k + 2)) (hcpos (k + 1)) (hcpos (k + 2))
    hQc hQseamC hP₁c hP₂c hP₁seamC hP₂seamC hdisj₁C hdisj₂C hdisj₁₂C hlev₁C hlev₂C hM hgk
  -- ## the count dictionary: the wrapper's triple is the cyclic relabelling of the design's
  have hbridge : (topBdryMeet CappingSpace (fun i : Fin 3 =>
      clampedSweep (![cblk k, cblk (k + 1), cblk (k + 2)] i) (fun r => 1 - r)
        (![diskPlane (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)), (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))] i)) 0).ncard
      = (topBdryMeet CappingSpace (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) k).ncard := by
    rw [hfam]
    have hσ : (fun i : Fin 3 => designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (i + k))
        = (fun i : Fin 3 => designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk
            ((Equiv.addRight k) i)) := by
      funext i
      rfl
    rw [hσ, ncard_topBdryMeet_eq_perm
      (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) (Equiv.addRight k)]
    rw [show (Equiv.addRight k) (0 : Fin 3) = k from fin3_add_zero k]
  show Odd (topBdryMeet CappingSpace (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk) k).ncard ↔
    (Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) (cblk (k + 1)) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1))) ∧
     Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) (cblk (k + 2)) (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2))))
  rw [← hbridge]
  exact hwrap

end

end Work.Drive
