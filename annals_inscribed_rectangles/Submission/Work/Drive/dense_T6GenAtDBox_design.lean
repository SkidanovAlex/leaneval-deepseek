import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.deltaCDesignDense
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.deltaCDesignSet
import Submission.Work.Drive.goodPair_pertChart_exists_near
import Submission.Work.Drive.hdenseT6Bridge
import Submission.Work.Drive.chartPert_rotCapping_comm
import Submission.Work.Drive.sgGoodChain_of_small_shift_sweep
import Submission.Work.Drive.loopBoxData_sweep
import Submission.Work.Drive.denseOpenBall
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.loopBoxData_eventually
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.rotSweepEquivariance
import Submission.Work.Drive.chartPertTransfer
import Submission.Work.Drive.norm_blkSpan
import Submission.Work.Drive.contMDiff_loopFam
import Submission.Work.Drive.contMDiff_clampedSweep_family

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 400000000
set_option linter.unusedVariables false

/-! ## The helper lemmas of the design's density

These are the bookkeeping lemmas the argument needs: the level of a chart perturbation (hence of a
block chart), the block bookkeeping of `blk`/`blkSpan`, the equivalence between the box-restricted
`DiamFamReg` and the two `LoopBoxData` clauses, and the two "open + dense" tools.  -/

/-- Three is odd: the distinguished block does not meet its successor. -/
private lemma denseT6_fin3_add_one_ne (k : Fin 3) : (k + 1 : Fin 3) ≠ k := by fin_cases k <;> decide

/-- Three is odd: the distinguished block does not meet its successor's successor. -/
private lemma denseT6_fin3_add_two_ne (k : Fin 3) : (k + 2 : Fin 3) ≠ k := by fin_cases k <;> decide

/-- The diameter block is not the core-sweep block. -/
private lemma denseT6_fin3_add_two_ne_add_one (k : Fin 3) : (k + 2 : Fin 3) ≠ k + 1 := by
  fin_cases k <;> decide

/-- **The level of a chart perturbation**: `levelOf (chartPert τ p) = levelOf p * exp (τ 0)`. -/
lemma denseT6_levelOf_chartPert_mul (τ : EuclideanSpace ℝ (Fin 4)) (p : CappingSpace) :
    levelOf (chartPert τ p) = levelOf p * Real.exp (τ 0) := by
  rw [levelOf_chartPert, levelScale_apply, Real.exp_add, Real.exp_log (levelOf_pos p)]

/-- **The level of a block chart**: the perturbation scales the level by `exp ((τ k) 0)` and the
rotation preserves it. -/
lemma denseT6_levelOf_blockChart {Q : ℂ → CappingSpace} (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) (z : ℂ) :
    levelOf (blockChart (fun s p => chartPert s p) Q u τ k z)
      = levelOf (Q z) * Real.exp ((τ k) 0) := by
  simp only [blockChart]
  rw [denseT6_levelOf_chartPert_mul, levelOf_rotCapping]

/-- **The block bookkeeping of a concentrated move**: adding `blkSpan i σ` changes only the `i`-th
block, by `σ`. -/
lemma denseT6_blk_add_blkSpan (t : EuclideanSpace ℝ (Fin 12)) (i j : Fin 3)
    (σ : EuclideanSpace ℝ (Fin 4)) :
    blk j (t + blkSpan i σ) = blk j t + (if j = i then σ else 0) := by
  rw [map_add]
  by_cases h : j = i
  · subst h; rw [blk_blkSpan, if_pos rfl]
  · rw [blk_blkSpan_of_ne h, if_neg h, add_zero]

/-- A single coordinate of a block of `ℝ¹²` is bounded by the norm. -/
lemma denseT6_coord_bound (k : Fin 3) (w : EuclideanSpace ℝ (Fin 12)) : |(blk k w) 0| ≤ ‖w‖ := by
  have h : (blk k w) 0 = w.ofLp (blkIdx k ⟨0, by norm_num⟩) := blk_apply k w ⟨0, by norm_num⟩
  rw [h, ← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (p := 2) w (blkIdx k ⟨0, by norm_num⟩)

/-- A coordinate of `ℝ⁴` is bounded by the norm. -/
lemma denseT6_coord_bound4 (v : EuclideanSpace ℝ (Fin 4)) : |v 0| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (p := 2) v 0

/-- **`DiamFamReg` is the conjunction of the two `LoopBoxData` clauses** of its two families against
the sweep (the two definitions carry the same four clauses). -/
lemma denseT6_diamFamReg_iff (Q : ℂ → CappingSpace) (θ c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    DiamFamReg Q θ c P ↔
      (LoopBoxData (diamFam Q θ) (clampedSweep c (fun s => 1 - s) P) ∧
        LoopBoxData (arcFam Q θ) (clampedSweep c (fun s => 1 - s) P)) := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
  · intro h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-- **The block chart is smooth.**  (The chart perturbation applied to the rotated chart.) -/
lemma denseT6_isSmoothChart_blockChart {Q : ℂ → CappingSpace} (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3) (hQ : IsSmoothChart Q) :
    IsSmoothChart (blockChart (fun s p => chartPert s p) Q u τ k) := by
  have h1 : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop (fun z : ℂ => rotCapping (u k) (Q z)) :=
    (contMDiff_rotCapping_apply (u k)).comp hQ
  have hmain := contMDiff_chartPert.comp ((contMDiff_const (c := τ k)).prodMk h1)
  refine hmain.congr fun z => ?_
  simp only [Function.comp_apply, blockChart]

/-- **A rotated chart is smooth.** -/
lemma denseT6_isSmoothChart_rotCapping {Q : ℂ → CappingSpace} (w : UnitAddCircle)
    (hQ : IsSmoothChart Q) :
    IsSmoothChart (fun z : ℂ => rotCapping w (Q z)) :=
  (contMDiff_rotCapping_apply w).comp hQ

/-- **A move concentrated outside the two distinguished blocks leaves the block chart unchanged.** -/
lemma denseT6_blockChart_update_of_ne {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (j : Fin 3)
    (w : EuclideanSpace ℝ (Fin m)) (mm : Fin 3) (h : mm ≠ j) :
    blockChart Ξ Q u (Function.update τ j w) mm = blockChart Ξ Q u τ mm := by
  funext z
  simp only [blockChart, Function.update_of_ne h w τ]

/-- **A move concentrated outside the two distinguished blocks leaves the block plane unchanged.** -/
lemma denseT6_blockPlane_update_of_ne {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m)) (j : Fin 3)
    (w : EuclideanSpace ℝ (Fin m)) (mm : Fin 3) (h : mm ≠ j) :
    blockPlane Ξ Q u (Function.update τ j w) mm = blockPlane Ξ Q u τ mm := by
  funext y
  simp only [blockPlane, Function.update_of_ne h w τ]

/-- **Two conditions, one of which is open, can be satisfied simultaneously.**  If `A` and `B` are
both dense at every point and both are open at their own points (in the form of the `∀ᶠ` hypothesis,
which is what the Sard statements of the lane supply), then they hold simultaneously arbitrarily close
to every point. -/
lemma denseT6_exists_both_of_open_dense {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A B : P → Prop)
    (hAo : ∀ x, A x → ∀ᶠ y in 𝓝 x, A y) (hBo : ∀ x, B x → ∀ᶠ y in 𝓝 x, B y)
    (hAd : ∀ x, ∀ γ : ℝ, 0 < γ → ∃ y, A y ∧ ‖y - x‖ < γ)
    (hBd : ∀ x, ∀ γ : ℝ, 0 < γ → ∃ y, B y ∧ ‖y - x‖ < γ)
    (x : P) (γ : ℝ) (hγ : 0 < γ) : ∃ y, A y ∧ B y ∧ ‖y - x‖ < γ := by
  obtain ⟨y₁, hB₁, hy₁⟩ := hBd x (γ / 2) (by linarith)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hBo y₁ hB₁)
  obtain ⟨y₂, hA₂, hy₂⟩ := hAd y₁ (min (γ / 2) r) (lt_min (by linarith) hrpos)
  have hB₂ : B y₂ :=
    hrsub (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hy₂ (min_le_right _ _))
  refine ⟨y₂, hA₂, hB₂, ?_⟩
  calc ‖y₂ - x‖ = dist y₂ x := by rw [dist_eq_norm]
    _ ≤ dist y₂ y₁ + dist y₁ x := dist_triangle _ _ _
    _ = ‖y₂ - y₁‖ + ‖y₁ - x‖ := by rw [dist_eq_norm, dist_eq_norm]
    _ < min (γ / 2) r + γ / 2 := add_lt_add_of_lt_of_le hy₂ (le_of_lt hy₁)
    _ ≤ γ / 2 + γ / 2 := by linarith [min_le_left (γ / 2) r]
    _ = γ := by ring

theorem dense_T6GenAtDBox_design {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hcpos : ∀ j : Fin 3, 0 < cblk j)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < Work.Drive.levelOf (Q z)) :
    ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (Work.Drive.blk k x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          Work.Drive.T6GenAtDBox
            (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
              (fun j => Work.Drive.blk j t) k)
            (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
              (fun j => Work.Drive.blk j t) (k + 1))
            (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
              (fun j => Work.Drive.blk j t) (k + 2))
            (cblk (k + 1)) (cblk (k + 2)) := by
  intro x hxle hx0 ε hε
  -- ## 0. the chart perturbation and the chart's smoothness
  let Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace := fun s p => chartPert s p
  have hΞ : ChartPert Q 4 Ξ :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQsm : IsSmoothChart Q := hQ.1
  -- ## 1. the budget
  let δ : ℝ := ε / 8
  have hδdef : δ = ε / 8 := rfl
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδ4 : 0 < δ / 4 := by linarith
  -- ## 2. the first move: raise the level of the block `k` parameter
  let w₀ : EuclideanSpace ℝ (Fin 4) := δ • EuclideanSpace.single 0 (1 : ℝ)
  have hw₀0 : w₀ 0 = δ := by
    show (δ • EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 4)) 0 = δ
    rw [PiLp.smul_apply, PiLp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  have hw₀norm : ‖w₀‖ = δ := by
    show ‖(δ • EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 4))‖ = δ
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos hδpos]
  let t₁ : EuclideanSpace ℝ (Fin 12) := x + blkSpan k w₀
  have ht₁x : ‖t₁ - x‖ = δ := by
    show ‖(x + blkSpan k w₀) - x‖ = δ
    rw [add_sub_cancel_left, norm_blkSpan, hw₀norm]
  have hblk₁ : blk k t₁ = blk k x + w₀ := by
    show blk k (x + blkSpan k w₀) = blk k x + w₀
    rw [denseT6_blk_add_blkSpan, if_pos rfl]
  have hlev₁ : δ ≤ (blk k t₁) 0 := by
    rw [hblk₁, PiLp.add_apply, hw₀0]
    linarith
  -- ## 3. the cut-avoidance move, which only moves the block `k` parameter
  obtain ⟨t₂, ht₂, hIII₂⟩ := exists_designCutAvoids_near hQ u cblk k t₁ (δ / 4) hδ4
  have hlev₂ : 3 * δ / 4 ≤ (blk k t₂) 0 := by
    have hsplit : blk k t₂ = blk k t₁ + blk k (t₂ - t₁) := by rw [map_sub]; abel
    have hb : |(blk k (t₂ - t₁)) 0| ≤ ‖t₂ - t₁‖ := denseT6_coord_bound k _
    have hlow : -(δ / 4) < (blk k (t₂ - t₁)) 0 :=
      (abs_lt.mp (lt_of_le_of_lt hb ht₂)).1
    rw [hsplit, PiLp.add_apply]
    linarith
  -- ## 4. the openness radius of the cut avoidance at `t₂`
  have hEvIII : ∀ᶠ t in 𝓝 t₂, DesignCutAvoids (Q := Q) u cblk k t :=
    (isOpen_designCutAvoids hQ u cblk k).mem_nhds hIII₂
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hEvIII
  have hρsub' : ∀ t : EuclideanSpace ℝ (Fin 12), ‖t - t₂‖ < ρ →
      DesignCutAvoids (Q := Q) u cblk k t := by
    intro t ht
    have hb : t ∈ Metric.ball t₂ ρ := by rwa [Metric.mem_ball, dist_eq_norm]
    exact hρsub hb
  -- ## 5. the core clause: move the block `k` chart by a small perturbation
  let ε₁ : ℝ := min (ρ / 4) (δ / 4)
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) hδ4
  have hε₁δ : ε₁ ≤ δ / 4 := min_le_right _ _
  have hε₁ρ : ε₁ ≤ ρ / 4 := min_le_left _ _
  obtain ⟨p₁, hp₁, hgp₁⟩ := sgGoodPair_of_small_shift (Ξ := Ξ) (Q := Q) (c := cblk (k + 1))
    hΞ hQsm (u (k + 1) - u k) (blk k t₂) (blk (k + 1) t₂) ε₁ hε₁pos
  let t₃ : EuclideanSpace ℝ (Fin 12) := t₂ + blkSpan k p₁
  let τ : Fin 3 → EuclideanSpace ℝ (Fin 4) := fun j => blk j t₃
  have hτk : τ k = blk k t₂ + p₁ := by
    show blk k (t₂ + blkSpan k p₁) = blk k t₂ + p₁
    rw [denseT6_blk_add_blkSpan, if_pos rfl]
  have hτk1 : τ (k + 1) = blk (k + 1) t₂ := by
    show blk (k + 1) (t₂ + blkSpan k p₁) = blk (k + 1) t₂
    rw [denseT6_blk_add_blkSpan, if_neg (denseT6_fin3_add_one_ne k), add_zero]
  have hτk0 : 0 < (τ k) 0 := by
    have hple : ‖p₁‖ ≤ δ / 4 := le_trans (le_of_lt hp₁) hε₁δ
    have hc : |p₁ 0| ≤ ‖p₁‖ := denseT6_coord_bound4 p₁
    have hlow : -(δ / 4) ≤ p₁ 0 := (abs_le.mp (le_trans hc hple)).1
    rw [hτk, PiLp.add_apply]
    linarith
  have hGoodAt : GoodAt Ξ Q (cblk (k + 1)) (u (k + 1) - u k) (τ k, τ (k + 1)) := by
    show GoodPair (pertChart Ξ Q (τ k))
      (fun p => rotCapping (u (k + 1) - u k) (pertChart Ξ Q (τ (k + 1)) p)) (cblk (k + 1))
    rw [hτk, hτk1]
    exact hgp₁
  have hcomm : ∀ (s : EuclideanSpace ℝ (Fin 4)) (w : UnitAddCircle) (p : CappingSpace),
      Ξ s (rotCapping w p) = rotCapping w (Ξ s p) := by
    intro s w p
    obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : UnitAddCircle) = w := ⟨Quotient.out w, Quotient.out_eq w⟩
    rw [← hv]
    exact chartPert_rotCapping_comm v s p
  have hI : GoodLoopChain (coreLoop (blockChart Ξ Q u τ k))
      (clampedSweep (cblk (k + 1)) (fun r => 1 - r) (blockPlane Ξ Q u τ (k + 1))) := by
    have hgp := goodPair_blockChart_of_goodAt Ξ hcomm Q u τ hGoodAt
    have h := goodLoopChain_of_goodPair hgp
    simpa only [blockPlane_eq_diskPlane_blockChart] using h
  have hSfin : (coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))).Finite := hI.1
  -- ## 6. the loop, the level band and the diameter block's family
  let Qk : ℂ → CappingSpace := blockChart Ξ Q u τ k
  let Qw : ℂ → CappingSpace := fun z => rotCapping (u (k + 2)) (Q z)
  have hQksm : IsSmoothChart Qk := denseT6_isSmoothChart_blockChart u τ k hQsm
  have hQwsm : IsSmoothChart Qw := denseT6_isSmoothChart_rotCapping (u (k + 2)) hQsm
  have hlevQk : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk (k + 2) < levelOf (Qk z) := by
    intro z hz
    have h1 : levelOf (Qk z) = levelOf (Q z) * Real.exp ((τ k) 0) := by
      show levelOf (blockChart Ξ Q u τ k z) = levelOf (Q z) * Real.exp ((τ k) 0)
      exact denseT6_levelOf_blockChart u τ k z
    rw [h1]
    have hexp : 1 ≤ Real.exp ((τ k) 0) := Real.one_le_exp (le_of_lt hτk0)
    calc cblk (k + 2) < levelOf (Q z) := hlev z hz
      _ = levelOf (Q z) * 1 := (mul_one _).symm
      _ ≤ levelOf (Q z) * Real.exp ((τ k) 0) :=
          mul_le_mul_of_nonneg_left hexp (le_of_lt (levelOf_pos _))
  have hlevLoop : ∀ (θ s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      cblk (k + 2) < levelOf (diamLoop Qk θ s) := by
    intro θ s hs
    rw [diamLoop_eq]
    apply hlevQk
    rw [norm_polPt, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  -- the family of swept planes in the shift of the diameter block's parameter
  let DP : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    fun y => diskPlane (pertChart Ξ Qw (τ (k + 2) + y))
  have hDPfun : ∀ s : EuclideanSpace ℝ (Fin 4),
      pertChart Ξ Qw s = blockChart Ξ Q u (Function.update τ (k + 2) s) (k + 2) := by
    intro s
    funext z
    show Ξ s (rotCapping (u (k + 2)) (Q z))
      = Ξ ((Function.update τ (k + 2) s) (k + 2)) (rotCapping (u (k + 2)) (Q z))
    rw [Function.update_self]
  have hDP : ∀ y : EuclideanSpace ℝ (Fin 4),
      DP y = blockPlane Ξ Q u (Function.update τ (k + 2) (τ (k + 2) + y)) (k + 2) := by
    intro y
    show diskPlane (pertChart Ξ Qw (τ (k + 2) + y)) = _
    rw [hDPfun (τ (k + 2) + y), diskPlane_blockChart]
  have hDP0 : ∀ y : EuclideanSpace ℝ (Fin 4),
      DP (y + 0) = DP y := by
    intro y
    congr 1
    abel
  -- ## 7. openness of the two conditions in the shift of the block `(k+2)` parameter
  have hopenA : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      IsOpen {y : EuclideanSpace ℝ (Fin 4) |
        GoodLoopChain (diamLoop Qk q.1.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y))} := by
    intro q
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hLsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × ℝ)) (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × ℝ => diamLoop Qk q.1.1 r.2) := by
      have hproj : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × ℝ)) (𝓘(ℝ, ℝ)) Ctop
          (fun r : EuclideanSpace ℝ (Fin 4) × ℝ => r.2) :=
        contMDiff_iff_contDiff.mpr (by fun_prop)
      exact (isSmoothLoop_diamLoop hQksm q.1.1).comp hproj
    have hDsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + r.1)) r.2) := by
      have h := contMDiff_sggSweepFam (m := 4) Ξ Qw (cblk (k + 2)) hΞ hQwsm (τ (k + 2) + y)
      simpa only [DP, add_assoc] using h
    have h0 : GoodLoopChain (diamLoop Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      simpa only [Set.mem_ofPred_eq, add_zero] using hy
    have hEv := eventually_good_meetBox (P := EuclideanSpace ℝ (Fin 4))
      (L := fun _ : EuclideanSpace ℝ (Fin 4) => diamLoop Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y')))
      hLsm hDsm h0.1 h0.2.1 h0.2.2
    have htend : Tendsto (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) := by fun_prop
      simpa using hc.tendsto y
    filter_upwards [htend.eventually hEv] with y' hy'
    have harg : DP (y + (y' - y)) = DP y' := by congr 1; abel
    rw [harg] at hy'
    exact hy'
  have hopenB : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      IsOpen {y : EuclideanSpace ℝ (Fin 4) |
        DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y)} := by
    intro q
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hDsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
        (𝓡 4) Ctop
        (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
          clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + r.1)) r.2) := by
      have h := contMDiff_sggSweepFam (m := 4) Ξ Qw (cblk (k + 2)) hΞ hQwsm (τ (k + 2) + y)
      simpa only [DP, add_assoc] using h
    have hAd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
          diamFam Qk q.1.1 r.2) :=
      (contMDiff_diamFam hQksm q.1.1).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4))
          (EuclideanSpace ℝ (Fin 2))).contMDiff
    have hAa : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop (fun r : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 2) =>
          arcFam Qk q.1.1 r.2) :=
      (contMDiff_arcFam hQksm q.1.1).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 4))
          (EuclideanSpace ℝ (Fin 2))).contMDiff
    have hyD : LoopBoxData (diamFam Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      have h := ((denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y)).mp
        (by simpa only [Set.mem_ofPred_eq] using hy)).1
      simpa only [add_zero] using h
    have hyA : LoopBoxData (arcFam Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + 0))) := by
      have h := ((denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y)).mp
        (by simpa only [Set.mem_ofPred_eq] using hy)).2
      simpa only [add_zero] using h
    have hEvD := loopBoxData_eventually (A := fun _ : EuclideanSpace ℝ (Fin 4) =>
        diamFam Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y'))) hAd hDsm hyD
    have hEvA := loopBoxData_eventually (A := fun _ : EuclideanSpace ℝ (Fin 4) =>
        arcFam Qk q.1.1)
      (D := fun y' => clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP (y + y'))) hAa hDsm hyA
    have htend : Tendsto (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun y' : EuclideanSpace ℝ (Fin 4) => y' - y) := by fun_prop
      simpa using hc.tendsto y
    filter_upwards [htend.eventually (hEvD.and hEvA)] with y' hy'
    have harg : DP (y + (y' - y)) = DP y' := by congr 1; abel
    rw [harg] at hy'
    exact (denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP y')).mpr hy'
  -- ## 8. the two conditions jointly, at one core meet
  have hndens : ∀ q : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1))),
      ∀ y : EuclideanSpace ℝ (Fin 4), ‖y‖ ≤ 1 → ∀ γ : ℝ, 0 < γ →
        ∃ y' : EuclideanSpace ℝ (Fin 4),
          GoodLoopChain (diamLoop Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y')) ∧
          DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y') ∧ ‖y' - y‖ < γ := by
    intro q y hy γ hγ
    refine denseT6_exists_both_of_open_dense
      (A := fun y' => GoodLoopChain (diamLoop Qk q.1.1)
        (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y')))
      (B := fun y' => DiamFamReg Qk q.1.1 (cblk (k + 2)) (DP y'))
      (fun y' hy' => (hopenA q).mem_nhds hy') (fun y' hy' => (hopenB q).mem_nhds hy')
      (fun y' γ' hγ' => ?_) (fun y' γ' hγ' => ?_) y γ hγ
    · obtain ⟨p, hp, hgood⟩ := sgGoodChain_of_small_shift_sweep (m := 4) (by norm_num)
        (diamLoop Qk q.1.1) (isSmoothLoop_diamLoop hQksm q.1.1) Ξ Qw (cblk (k + 2))
        (hcpos (k + 2)) hΞ hQwsm (fun s hs => hlevLoop q.1.1 s hs) (τ (k + 2) + y') γ' hγ'
      refine ⟨y' + p, ?_, ?_⟩
      · have h1 : GoodLoopChain (diamLoop Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hgood
        simpa only [DP, add_assoc] using h1
      · rw [add_sub_cancel_left]
        exact hp
    · obtain ⟨p, hp, hLBD, hLBA⟩ := exists_loopBoxData_of_small_shift (m := 4) Qk hQksm q.1.1
        (cblk (k + 2)) (hcpos (k + 2)) hlevQk Ξ Q hΞ hQsm (u (k + 2)) (τ (k + 2) + y') γ' hγ'
      refine ⟨y' + p, ?_, ?_⟩
      · have h1 : LoopBoxData (diamFam Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hLBD
        have h2 : LoopBoxData (arcFam Qk q.1.1)
            (clampedSweep (cblk (k + 2)) (fun s => 1 - s)
              (diskPlane (pertChart Ξ Qw ((τ (k + 2) + y') + p)))) := hLBA
        have hassoc : (τ (k + 2) + y') + p = τ (k + 2) + (y' + p) := by abel
        rw [hassoc] at h1 h2
        exact (denseT6_diamFamReg_iff Qk q.1.1 (cblk (k + 2)) (DP (y' + p))).mpr
          (by simpa only [DP] using And.intro h1 h2)
      · rw [add_sub_cancel_left]
        exact hp
  -- ## 9. the finite intersection over the core meet set
  let ε₂ : ℝ := min (min (ρ / 4) (δ / 4)) (1 / 2)
  have hε₂pos : 0 < ε₂ := lt_min (lt_min (by linarith) hδ4) (by norm_num)
  have hε₂δ : ε₂ ≤ δ / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₂ρ : ε₂ ≤ ρ / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₂1 : ε₂ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  haveI : Fintype ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))) := hSfin.fintype
  let e : ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1)) (blockPlane Ξ Q u τ (k + 1))) ≃
      Fin (Fintype.card ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
        (blockPlane Ξ Q u τ (k + 1)))) :=
    Fintype.equivFin _
  obtain ⟨p₂, hp₂, hp₂all⟩ := exists_mem_all_of_isOpen_dense (m := 4)
    (Fintype.card ↥(coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1))))
    (fun n => {y : EuclideanSpace ℝ (Fin 4) |
        GoodLoopChain (diamLoop Qk (e.symm n).1.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP y))} ∩
      {y : EuclideanSpace ℝ (Fin 4) |
        DiamFamReg Qk (e.symm n).1.1 (cblk (k + 2)) (DP y)})
    (fun n => (hopenA (e.symm n)).inter (hopenB (e.symm n)))
    (fun n y hy γ hγ => by
      obtain ⟨y', h1, h2, h3⟩ := hndens (e.symm n) y hy γ hγ
      exact ⟨y', ⟨h1, h2⟩, h3⟩)
    ε₂ hε₂pos hε₂1
  have hp₂mem : ∀ q ∈ coreMeet (blockChart Ξ Q u τ k) (cblk (k + 1))
      (blockPlane Ξ Q u τ (k + 1)),
      GoodLoopChain (diamLoop Qk q.1)
          (clampedSweep (cblk (k + 2)) (fun s => 1 - s) (DP p₂)) ∧
        DiamFamReg Qk q.1 (cblk (k + 2)) (DP p₂) := by
    intro q hq
    have hn := hp₂all (e ⟨q, hq⟩)
    simpa only [Equiv.symm_apply_apply, Set.mem_inter_iff, Set.mem_ofPred_eq] using hn
  -- ## 10. the final parameter and its block values
  let tfin : EuclideanSpace ℝ (Fin 12) := t₃ + blkSpan (k + 2) p₂
  have hτfin : (fun j : Fin 3 => blk j tfin)
      = Function.update τ (k + 2) (τ (k + 2) + p₂) := by
    funext j
    show blk j (t₃ + blkSpan (k + 2) p₂)
      = Function.update τ (k + 2) (τ (k + 2) + p₂) j
    rw [denseT6_blk_add_blkSpan]
    by_cases h : j = k + 2
    · subst h
      rw [if_pos rfl, Function.update_self]
    · rw [if_neg h, add_zero, Function.update_of_ne h]
  refine ⟨tfin, ?_, ?_⟩
  -- ## 11. the distance bound
  · have hA : ‖tfin - t₃‖ = ‖p₂‖ := by
      show ‖(t₃ + blkSpan (k + 2) p₂) - t₃‖ = ‖p₂‖
      rw [add_sub_cancel_left, norm_blkSpan]
    have hB : ‖t₃ - t₂‖ = ‖p₁‖ := by
      show ‖(t₂ + blkSpan k p₁) - t₂‖ = ‖p₁‖
      rw [add_sub_cancel_left, norm_blkSpan]
    have hp₂b : ‖p₂‖ ≤ δ / 4 := le_trans (le_of_lt hp₂) hε₂δ
    have hp₁b : ‖p₁‖ ≤ δ / 4 := le_trans (le_of_lt hp₁) hε₁δ
    have hs1 : ‖tfin - x‖ ≤ ‖tfin - t₃‖ + ‖t₃ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    have hs2 : ‖t₃ - x‖ ≤ ‖t₃ - t₂‖ + ‖t₂ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    have hs3 : ‖t₂ - x‖ ≤ ‖t₂ - t₁‖ + ‖t₁ - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle _ _ _
    linarith [hs1, hs2, hs3, hA, hB, ht₂, ht₁x, hp₂b, hp₁b, hδdef]
  -- ## 12. the bundle
  · rw [hτfin]
    rw [denseT6_blockChart_update_of_ne Ξ Q u τ (k + 2) (τ (k + 2) + p₂) k
        (denseT6_fin3_add_two_ne k).symm]
    rw [denseT6_blockPlane_update_of_ne Ξ Q u τ (k + 2) (τ (k + 2) + p₂) (k + 1)
        (denseT6_fin3_add_two_ne_add_one k).symm]
    refine ⟨⟨hI, ?_, ?_⟩, ?_⟩
    · intro q hq
      have hn := hp₂mem q hq
      rw [← hDP p₂]
      exact hn.1
    · -- the cut avoidance at the final parameter
      rw [← denseT6_blockChart_update_of_ne Ξ Q u τ (k + 2) (τ (k + 2) + p₂) k
        (denseT6_fin3_add_two_ne k).symm]
      have hnorm : ‖tfin - t₂‖ < ρ := by
        have hs1 : ‖tfin - t₂‖ ≤ ‖tfin - t₃‖ + ‖t₃ - t₂‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        have hA : ‖tfin - t₃‖ = ‖p₂‖ := by
          show ‖(t₃ + blkSpan (k + 2) p₂) - t₃‖ = ‖p₂‖
          rw [add_sub_cancel_left, norm_blkSpan]
        have hB : ‖t₃ - t₂‖ = ‖p₁‖ := by
          show ‖(t₂ + blkSpan k p₁) - t₂‖ = ‖p₁‖
          rw [add_sub_cancel_left, norm_blkSpan]
        have hp₂b : ‖p₂‖ ≤ ρ / 4 := le_trans (le_of_lt hp₂) hε₂ρ
        have hp₁b : ‖p₁‖ ≤ ρ / 4 := le_trans (le_of_lt hp₁) hε₁ρ
        linarith [hs1, hA, hB, hp₂b, hp₁b, hρpos]
      have hIII := hρsub' tfin hnorm
      simpa only [DesignCutAvoids, designSweep, hτfin] using hIII
    · intro q hq
      have hn := hp₂mem q hq
      rw [← hDP p₂]
      exact hn.2

end

end Work.Drive
