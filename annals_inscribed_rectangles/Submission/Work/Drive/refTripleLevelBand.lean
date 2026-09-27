import Mathlib
import Submission.Work.Drive.refTripleRows

/-!
# The **strict** level bands of the perturbed reference blocks

`Drive/refTripleRows.lean` §7–§8 supplies the level data of the reference triple in the form the
**stale** transport wrapper consumed: `levelOf (chartPert (blk k t) (rotCapping u (Q z))) ≠ cblk 2`
(`Work.Drive.levelOf_chartPert_rotCapping_ne_cblk`) and the *upper* separation of the reference block.

The **corrected** wrapper `Work.Drive.blockT6Wrapper_of_T6GenAtD`
(`Drive/blockT6Wrapper_of_T6GenAtD.lean`, proved) needs the two *strict* bands

> `hc₁ : 0 < c₁`, `hlev₁ : ∀ z, ‖z‖ ≤ 1 → c₁ < levelOf (Q z)`, and likewise for `c₂`

(`WALL_NODES_H3_STATUS.md` §5, `ENCODED_FAMILY_STATUS.md` §7.4): the avoidance `ftY2 x ≠ 0` of the
swept face is produced by `Work.Drive.ppMeet_face_avoidances`, whose hypotheses are exactly those two
strict inequalities; the `≠ c₂` form does not imply them.

This module supplies the strict bands for the **reference triple's** configuration charts, in the
bordism-compatible vocabulary (it imports only `refTripleRows`, so it may be co-imported with
`classTripleOdd` and with `hn2_refTripleAt_producer` — unlike anything importing the transport lane,
cf. the `Work.Drive.mk3` clash recorded in the module's sibling `ASSEMBLY_CLASH_STATUS.md`).

In the design `cblk = ![c/2, c/3, c/4]` with `c` below the chart's disk levels, and the perturbation
*raises* the levels, so both bands are free: the content is the elementary estimate
`c / j ≤ c * exp (-‖t‖)` for `‖t‖ < log j` (`Work.Drive.levelOf_chartPert_mul`,
`Work.Drive.exp_coord_blk_ge`).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The strict level band of a perturbed rotated chart on the closed disk.**  If the chart's levels on
the disk are at least `c ≥ 0` and `c' < c * exp (-‖t‖)`, then the level of the perturbed rotated chart
`chartPert (blk k t) ∘ rotCapping u ∘ Q` exceeds `c'` on the disk. -/
theorem levelOf_chartPert_rotCapping_gt {Q : ℂ → CappingSpace} {u : UnitAddCircle} {c c' : ℝ}
    (hc : 0 ≤ c) (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    {t : EuclideanSpace ℝ (Fin 12)} (ht : c' < c * Real.exp (-‖t‖)) (k : Fin 3) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → c' < levelOf (chartPert (blk k t) (rotCapping u (Q z))) := by
  intro z hz
  have h1 : levelOf (chartPert (blk k t) (rotCapping u (Q z)))
      = levelOf (Q z) * Real.exp ((blk k t) 0) := by
    rw [levelOf_chartPert_mul, levelOf_rotCapping]
  rw [h1]
  have h2 : c * Real.exp (-‖t‖) ≤ levelOf (Q z) * Real.exp ((blk k t) 0) :=
    mul_le_mul (hcbot z hz) (exp_coord_blk_ge k t) (Real.exp_pos _).le (levelOf_pos (Q z)).le
  linarith

/-- **The strict level band at the design's levels** `cblk 1 = c / 3`, `cblk 2 = c / 4`: for
`‖t‖ < log 3` (so in particular for `‖t‖ < log 3 < log 4`) the perturbed rotated chart of any block
stays strictly above `cblk 1` and `cblk 2` on the closed disk.  These are the `hlev₁`/`hlev₂` inputs of
the corrected transport wrapper at the reference triple. -/
theorem levelOf_chartPert_rotCapping_gt_cblk {Q : ℂ → CappingSpace} (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) (u : UnitAddCircle) {cblk : Fin 3 → ℝ}
    (hcblk1 : cblk 1 = c / 3) (hcblk2 : cblk 2 = c / 4)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < Real.log 3) (k : Fin 3) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 1 < levelOf (chartPert (blk k t) (rotCapping u (Q z))) ∧
        cblk 2 < levelOf (chartPert (blk k t) (rotCapping u (Q z))) := by
  have hcnn : (0 : ℝ) ≤ c := hc.le
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z) := fun z hz => (hcbot z hz).le
  -- `exp (-‖t‖) > 1/4`, hence also `> 1/3`
  have h4 : (1 : ℝ) / 4 < Real.exp (-‖t‖) := by
    have h := Real.exp_lt_exp.mpr (show -Real.log 4 < -‖t‖ by linarith [Real.log_le_log (by norm_num : (0:ℝ) < 3) (show (3:ℝ) ≤ 4 by norm_num)])
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using h
  have h3 : (1 : ℝ) / 3 < Real.exp (-‖t‖) := by
    have h := Real.exp_lt_exp.mpr (show -Real.log 3 < -‖t‖ by linarith)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] using h
  refine fun z hz => ⟨?_, ?_⟩
  · have hlt : cblk 1 < c * Real.exp (-‖t‖) := by rw [hcblk1]; nlinarith [hc]
    exact levelOf_chartPert_rotCapping_gt hcnn hcbot' hlt k z hz
  · have hlt : cblk 2 < c * Real.exp (-‖t‖) := by rw [hcblk2]; nlinarith [hc]
    exact levelOf_chartPert_rotCapping_gt hcnn hcbot' hlt k z hz

/-- **The strict band at the *first* design level** `cblk 0 = c / 2`: for `‖t‖ < log 2` the perturbed
rotated chart of any block stays strictly above `cblk 0` on the closed disk. -/
theorem levelOf_chartPert_rotCapping_gt_cblk0 {Q : ℂ → CappingSpace} (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) (u : UnitAddCircle) {cblk : Fin 3 → ℝ}
    (hcblk0 : cblk 0 = c / 2) {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < Real.log 2) (k : Fin 3) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → cblk 0 < levelOf (chartPert (blk k t) (rotCapping u (Q z))) := by
  have h2 : (1 : ℝ) / 2 < Real.exp (-‖t‖) := by
    have h := Real.exp_lt_exp.mpr (show -Real.log 2 < -‖t‖ by linarith)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hlt : cblk 0 < c * Real.exp (-‖t‖) := by rw [hcblk0]; nlinarith [hc]
  exact levelOf_chartPert_rotCapping_gt hc.le (fun z hz => (hcbot z hz).le) hlt k

/-- **The same strict band, in the vocabulary of the *design's* block charts** (no rotation: the level
of `chartPert (blk k t)` applied to a disk point of `Q` directly).  This is the form in which the
corrected wrapper's `hlev₁`/`hlev₂` are needed at the design's blocks, where the core chart of block `k`
is `chartPert (blk k t) ∘ rotCapping (u k) ∘ Q`. -/
theorem levelOf_chartPert_gt_cblk {Q : ℂ → CappingSpace} (c : ℝ) (hc : 0 < c)
    (hcbot : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z)) {cblk : Fin 3 → ℝ}
    (hcblk1 : cblk 1 = c / 3) (hcblk2 : cblk 2 = c / 4)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : ‖t‖ < Real.log 3) (k : Fin 3) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 1 < levelOf (chartPert (blk k t) (Q z)) ∧
        cblk 2 < levelOf (chartPert (blk k t) (Q z)) := by
  intro z hz
  obtain ⟨h1, h2⟩ := levelOf_chartPert_rotCapping_gt_cblk c hc hcbot (0 : UnitAddCircle) hcblk1
    hcblk2 ht k z hz
  have hzero : levelOf (chartPert (blk k t) (rotCapping (0 : UnitAddCircle) (Q z)))
      = levelOf (chartPert (blk k t) (Q z)) := by
    rw [levelOf_chartPert_mul, levelOf_chartPert_mul, levelOf_rotCapping]
  exact ⟨by rw [← hzero]; exact h1, by rw [← hzero]; exact h2⟩

/-! ## The level of the perturbed reference plane, and the `(F1)` level condition

`Work.Drive.odd_coreSideCount_reference_mixed` (`Drive/mixedFactorBox.lean`, the `(F1)` factor of `hn2`
in the *box*-count form) carries the hypothesis

> `hβ'lam : β' < ((levelScale σ ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) : ℝ)`

where `β'` is an upper bound of the levels of the perturbed configuration chart on the closed disk and
`lam` is the *unperturbed* level of the linear reference plane, perturbed by the block parameter `σ`.
The estimate below is that hypothesis at the reference triple, with
`β' = β * exp ‖t‖` and `σ = blk k t`: it is `Work.Drive.beta_exp_lt_lam_exp` (`refTripleRows.lean`) plus
the elementary lower bound `lam * exp (-‖t‖) ≤ levelScale (blk k t) ⟨lam, _⟩`. -/

/-- **The perturbed reference level is at least `lam * exp (-‖t‖)`.** -/
theorem levelScale_blk_ge {lam : ℝ} (hlam : 0 < lam) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    lam * Real.exp (-‖t‖) ≤ ((levelScale (blk k t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) : ℝ) := by
  have h1 : ((levelScale (blk k t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) : ℝ)
      = Real.exp (Real.log lam + (blk k t) 0) := by
    rw [levelScale_apply]
  rw [h1]
  have hy : -‖t‖ ≤ (blk k t) 0 := by
    have h := neg_abs_le ((blk k t).ofLp 0)
    have h' := abs_coord_blk_le k t
    linarith [neg_le_neg h']
  calc lam * Real.exp (-‖t‖) = Real.exp (Real.log lam) * Real.exp (-‖t‖) := by
        rw [Real.exp_log hlam]
    _ = Real.exp (Real.log lam + (-‖t‖)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log lam + (blk k t) 0) := Real.exp_le_exp.mpr (by linarith)

/-- **The `(F1)` level condition at the reference triple**: the perturbed configuration chart's level
bound `β * exp ‖t‖` is strictly below the perturbed level of the reference plane, as soon as
`2 ‖t‖ < log (lam / β)` and `β < lam`. -/
theorem mixedFactor_level_lt {β lam : ℝ} (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
    {t : EuclideanSpace ℝ (Fin 12)} (ht : 2 * ‖t‖ < Real.log (lam / β)) (k : Fin 3) :
    β * Real.exp ‖t‖ < ((levelScale (blk k t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) : ℝ) :=
  lt_of_lt_of_le (beta_exp_lt_lam_exp hβpos hlam hβlam ht) (levelScale_blk_ge hlam k t)

end

end Work.Drive
