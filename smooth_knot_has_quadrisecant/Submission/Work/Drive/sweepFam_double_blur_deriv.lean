import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.sweepWideEndCore
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.sweepLoopChamfer_ftc
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.chamferVel_hasDerivAt

/-!
# The loop derivative of the doubly blurred chord sweep

`Work.Drive.sweepFam r D lam δ₁ δ₂ σ` is the doubly blurred chamfered chord sweep: the raw loop
`Work.Drive.sweepLoopChamfer r D lam σ` is convolved with the bump `sweepBump` in the loop
parameter (`δ₁`) and then in the sweep parameter (`δ₂`).  This module computes the derivative of
the doubly blurred family in its *loop* parameter at an arbitrary sweep parameter `σ ∈ (δ₂, 1-δ₂)`:

    (sweepFam σ)' (t) = ∫ v, sweepBump v • ∫ u, sweepBump u • chamferVel (σ - δ₂ v) (t - δ₁ u).

The proof has three ingredients:

* the derivative of the singly blurred slice `sweepSmoothT` (`Work.Drive.wideEnd_hasDerivAt_sweepSmoothT`,
  whose hypotheses are a uniform bound on `chamferVel` and a uniform Lipschitz constant for the raw
  loop);
* differentiation under the integral sign in the outer (sweep-parameter) integral
  (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip`);
* the uniform bounds and Lipschitz constants, which are produced here *by hand* rather than from the
  sharp wide-end estimate: the raw loop is a concatenation of two knot arcs and two chords, so a
  global bound `‖r‖ ≤ R` on the knot and a global bound `‖velocity r‖ ≤ L` on its velocity suffice.
  `doubleBlurLam` is the resulting constant.

## Main results

* `Work.Drive.doubleBlurLam` — the uniform bound on `chamferVel` and on the loop derivative;
* `Work.Drive.sweepLoopChamfer_norm_le` — the raw loop is bounded by the bound `R` of the knot;
* `Work.Drive.doubleBlur_chamferVel_bound` — `‖chamferVel r D lam σ t‖ ≤ doubleBlurLam …`;
* `Work.Drive.doubleBlur_loop_lipschitz` — the raw loop is `doubleBlurLam …`-Lipschitz;
* `Work.Drive.doubleBlur_sweepFam_hasDerivAt` — the derivative of the doubly blurred slice;
* `Work.Drive.sweepFam_double_blur_deriv` — the target.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open MeasureTheory
open scoped Real Topology intervalIntegral

set_option maxHeartbeats 1000000

variable {r : ℝ → Space} {d : BandArcData} {D : SweepData d}

/-! ## Periodicity and global boundedness -/

/-- The velocity of a smooth knot is `period`-periodic. -/
theorem doubleBlur_velocity_periodic (hr : IsSmoothKnot r) :
    Function.Periodic (velocity r) period := by
  have h : Function.Periodic (deriv r) period := by
    intro x
    have h1 : deriv r (x + period) = deriv (fun y : ℝ => r (y + period)) x := by
      have h2 : (fun y : ℝ => r (period + y)) = (fun y : ℝ => r (y + period)) := by
        funext y; rw [add_comm]
      have h3 := deriv_comp_const_add r period x
      rw [h2, add_comm period x] at h3
      exact h3.symm
    rw [h1, hr.periodic.funext]
  simpa [velocity] using h

/-! ## The uniform constant -/

/-- **The uniform bound of the doubly blurred sweep.**  `doubleBlurLam lam L R Tw` bounds both the
chamfered loop velocity `chamferVel` and the derivative of the raw loop in the loop parameter,
whenever `L` bounds the knot velocity, `R` the knot itself and `Tw` the width `sweepW'` of the
retained arc. -/
def doubleBlurLam (lam L R Tw : ℝ) : ℝ :=
  2 * Tw * L / period + 4 * R / (lam * period) + 4 * R / period

lemma doubleBlurLam_nonneg {lam L R Tw : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hTw : 0 ≤ Tw) : 0 ≤ doubleBlurLam lam L R Tw := by
  have hp : (0 : ℝ) < period := period_pos
  have h1 : 0 ≤ 2 * Tw * L / period :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTw) hL) hp.le
  have h2 : 0 ≤ 4 * R / (lam * period) :=
    div_nonneg (mul_nonneg (by norm_num) hR) (mul_pos hlam hp).le
  have h3 : 0 ≤ 4 * R / period := div_nonneg (mul_nonneg (by norm_num) hR) hp.le
  rw [doubleBlurLam]
  linarith

/-! ## Bounds on the raw loop -/

/-- A convex combination of two vectors of norm at most `R` has norm at most `R`. -/
lemma doubleBlur_norm_smul_add_le {c R : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {a b : Space}
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) : ‖(1 - c) • a + c • b‖ ≤ R := by
  calc ‖(1 - c) • a + c • b‖ ≤ ‖(1 - c) • a‖ + ‖c • b‖ := norm_add_le _ _
    _ = (1 - c) * ‖a‖ + c * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0]
    _ ≤ (1 - c) * R + c * R :=
        add_le_add (mul_le_mul_of_nonneg_left ha (by linarith)) (mul_le_mul_of_nonneg_left hb h0)
    _ = R := by ring

lemma doubleBlur_sweepArc'_norm_le {R : ℝ} (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (s ξ : ℝ) :
    ‖sweepArc' r D s ξ‖ ≤ R := hR _

lemma doubleBlur_sweepChord'_norm_le {R : ℝ} (hR : ∀ x : ℝ, ‖r x‖ ≤ R) {ξ : ℝ}
    (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (s : ℝ) : ‖sweepChord' r D s ξ‖ ≤ R := by
  have h := doubleBlur_norm_smul_add_le h0 h1 (hR (taR D s)) (hR (tbR D s))
  simpa only [sweepChord'] using h

/-- **The raw chamfered loop is bounded by the bound of the knot.**  Every point of the loop is
either a point of the knot or lies on one of its chords, hence has norm at most `R` whenever
`‖r‖ ≤ R` everywhere. -/
lemma sweepLoopChamfer_norm_le {R : ℝ} (hR : ∀ x : ℝ, ‖r x‖ ≤ R) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1 / 2) (s t : ℝ) : ‖sweepLoopChamfer r D lam s t‖ ≤ R := by
  have hArc : ∀ ξ : ℝ, ‖sweepArc' r D s ξ‖ ≤ R := fun ξ => doubleBlur_sweepArc'_norm_le hR s ξ
  have hChd : ∀ ξ ∈ Set.Icc (0 : ℝ) 1, ‖sweepChord' r D s ξ‖ ≤ R :=
    fun ξ hξ => doubleBlur_sweepChord'_norm_le hR hξ.1 hξ.2 s
  simp only [sweepLoopChamfer]
  split_ifs with hA hB hC
  · exact hArc _
  · have hc0 : 0 ≤ (2 * sweepParam t - 1) / lam := div_nonneg (by linarith) h0.le
    have hc1 : (2 * sweepParam t - 1) / lam ≤ 1 := by
      rw [div_le_one h0]; linarith
    exact doubleBlur_norm_smul_add_le hc0 hc1 (hArc _) (hChd _ ⟨by linarith, by linarith⟩)
  · have hr0 : 0 ≤ (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) :=
      div_nonneg (by linarith) (by linarith)
    have hr1 : (sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hξ0 : 0 ≤ (1 - lam) - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam) := by
      nlinarith [hr1, h0, h1]
    have hξ1 : (1 - lam) - ((sweepParam t - (1 / 2 + lam / 2)) / (1 / 2 - lam)) * (1 - 2 * lam) ≤ 1 := by
      nlinarith [hr0, h0, h1]
    exact hChd _ ⟨hξ0, hξ1⟩
  · have hc0 : 0 ≤ (sweepParam t - (1 - lam / 2)) / (lam / 2) :=
      div_nonneg (by linarith) (by linarith)
    have hc1 : (sweepParam t - (1 - lam / 2)) / (lam / 2) ≤ 1 := by
      rw [div_le_one (by linarith)]
      have := (sweepParam_mem t).2
      linarith
    exact doubleBlur_norm_smul_add_le hc0 hc1 (hChd _ ⟨h0.le, by linarith⟩) (hArc _)

/-- The bump is at most one. -/
lemma doubleBlur_sweepBump_le_one (u : ℝ) : sweepBump u ≤ 1 := by
  have h := wideEnd_sweepBump_le_one u
  rwa [Real.norm_of_nonneg (sweepBump_nonneg u)] at h

/-- The singly blurred slice is bounded by twice any bound of the raw loop. -/
lemma doubleBlur_sweepSmoothT_norm_le (lam sig : ℝ) {M : ℝ}
    (hM : ∀ y : ℝ, ‖sweepLoopChamfer r D lam sig y‖ ≤ M) (δ s : ℝ) :
    ‖sweepSmoothT r D lam δ sig s‖ ≤ 2 * M := by
  rw [sweepSmoothT]
  calc ‖∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam sig (s - δ * u)‖
      ≤ M * |(1 : ℝ) - (-1)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (C := M) (fun u _ => ?_)
        rw [norm_smul]
        calc ‖sweepBump u‖ * ‖sweepLoopChamfer r D lam sig (s - δ * u)‖ ≤ 1 * M :=
              mul_le_mul (wideEnd_sweepBump_le_one u) (hM _) (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    _ = 2 * M := by rw [show |(1 : ℝ) - (-1)| = 2 by norm_num]; ring

/-! ## Bounds on the four branch values of the derivative -/

lemma doubleBlur_sweepBranch1_norm_le {lam L Tw : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hL : ∀ x : ℝ, ‖deriv r x‖ ≤ L) (hTw : 0 ≤ Tw) (s : ℝ) (hW : |sweepW' D s| ≤ Tw)
    (u : ℝ) :
    ‖sweepBranch1 r D lam s u‖ ≤ 2 * Tw * L := by
  have habs : |2 * (1 - 2 * lam)| ≤ 2 := by
    rw [abs_mul]
    have hle : |(1 : ℝ) - 2 * lam| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith
  have hsplit : ‖sweepBranch1 r D lam s u‖
      = |2 * (1 - 2 * lam)| * |sweepW' D s|
        * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖ := by
    rw [sweepBranch1, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    ring
  rw [hsplit]
  have h1' : |2 * (1 - 2 * lam)| * |sweepW' D s| ≤ 2 * Tw :=
    mul_le_mul habs hW (abs_nonneg _) (by norm_num)
  calc |2 * (1 - 2 * lam)| * |sweepW' D s|
        * ‖deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s)‖
      ≤ (2 * Tw) * L := mul_le_mul h1' (hL _) (norm_nonneg _) (mul_nonneg (by norm_num) hTw)
    _ = 2 * Tw * L := by ring

lemma doubleBlur_sweepBranch2_norm_le {lam R : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (s : ℝ) : ‖sweepBranch2 r D lam s‖ ≤ 4 * R / lam := by
  have hdel : ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖ ≤ 2 * R := by
    calc ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖
        ≤ ‖sweepChord' r D s (1 - lam)‖ + ‖sweepArc' r D s (1 - lam)‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (doubleBlur_sweepChord'_norm_le hR (by linarith) (by linarith) s)
          (doubleBlur_sweepArc'_norm_le hR s _)
      _ = 2 * R := by ring
  rw [sweepBranch2, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos h0)]
  calc (2 / lam) * ‖sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam)‖
      ≤ (2 / lam) * (2 * R) := mul_le_mul_of_nonneg_left hdel (by positivity)
    _ = 4 * R / lam := by ring

lemma doubleBlur_sweepBranch3_norm_le {lam R : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (s : ℝ) : ‖sweepBranch3 r D lam s‖ ≤ 4 * R := by
  have hpos : (0 : ℝ) < 1 - 2 * lam := by linarith
  have hd : (0 : ℝ) < 1 / 2 - lam := by linarith
  have hcoef : |(-(1 - 2 * lam) / (1 / 2 - lam))| = 2 := by
    rw [abs_div, abs_neg, abs_of_pos hd, abs_of_pos hpos, div_eq_iff (ne_of_gt hd)]
    ring
  rw [sweepBranch3, norm_smul, Real.norm_eq_abs, hcoef]
  calc 2 * ‖r (tbR D s) - r (taR D s)‖
      ≤ 2 * (2 * R) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ‖r (tbR D s) - r (taR D s)‖ ≤ ‖r (tbR D s)‖ + ‖r (taR D s)‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (hR _) (hR _)
          _ = 2 * R := by ring
    _ = 4 * R := by ring

lemma doubleBlur_sweepBranch4_norm_le {lam R : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (s : ℝ) : ‖sweepBranch4 r D lam s‖ ≤ 4 * R / lam := by
  have hdel : ‖sweepArc' r D s lam - sweepChord' r D s lam‖ ≤ 2 * R := by
    calc ‖sweepArc' r D s lam - sweepChord' r D s lam‖
        ≤ ‖sweepArc' r D s lam‖ + ‖sweepChord' r D s lam‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (doubleBlur_sweepArc'_norm_le hR s _)
          (doubleBlur_sweepChord'_norm_le hR h0.le (by linarith) s)
      _ = 2 * R := by ring
  rw [sweepBranch4, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos two_pos h0)]
  calc (2 / lam) * ‖sweepArc' r D s lam - sweepChord' r D s lam‖
      ≤ (2 / lam) * (2 * R) := mul_le_mul_of_nonneg_left hdel (by positivity)
    _ = 4 * R / lam := by ring

/-! ## The bound on the loop derivative and on `chamferVel` -/

/-- `sweepLoopChamferDeriv` is the selection of the four branch values by the profile. -/
lemma sweepLoopChamferDeriv_eq_ite (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s t : ℝ) :
    sweepLoopChamferDeriv r D lam s t = (1 / period) •
      (if sweepParam t ≤ 1 / 2 then sweepBranch1 r D lam s (sweepParam t)
        else if sweepParam t ≤ 1 / 2 + lam / 2 then sweepBranch2 r D lam s
        else if sweepParam t ≤ 1 - lam / 2 then sweepBranch3 r D lam s
        else sweepBranch4 r D lam s) := by
  simp only [sweepLoopChamferDeriv, sweepBranch1, sweepBranch2, sweepBranch3, sweepBranch4]

/-- **The loop derivative of the raw loop is bounded by `doubleBlurLam`.** -/
lemma doubleBlur_chamferDeriv_bound {lam L R Tw : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hL : ∀ x : ℝ, ‖deriv r x‖ ≤ L) (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (hTw : 0 ≤ Tw)
    (s : ℝ) (hW : |sweepW' D s| ≤ Tw) (t : ℝ) :
    ‖sweepLoopChamferDeriv r D lam s t‖ ≤ doubleBlurLam lam L R Tw := by
  have hp : (0 : ℝ) < period := period_pos
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (r 0)) (hR 0)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg (deriv r 0)) (hL 0)
  have h1' : 0 ≤ 2 * Tw * L / period :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTw) hL0) hp.le
  have h2 : 0 ≤ 4 * R / (lam * period) :=
    div_nonneg (mul_nonneg (by norm_num) hR0) (mul_pos h0 hp).le
  have h3 : 0 ≤ 4 * R / period := div_nonneg (mul_nonneg (by norm_num) hR0) hp.le
  rw [sweepLoopChamferDeriv_eq_ite]
  simp only [smul_ite]
  split_ifs with hA hB hC
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch1 r D lam s (sweepParam t)‖
        ≤ (1 / period) * (2 * Tw * L) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch1_norm_le h0 h1 hL hTw s hW _)
            (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (2 * Tw * L) = 2 * Tw * L / period := by ring
          rw [he]
          linarith [h1', h2, h3]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch2 r D lam s‖ ≤ (1 / period) * (4 * R / lam) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch2_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R / lam) = 4 * R / (lam * period) := by ring
          rw [he]
          linarith [h1', h2, h3]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch3 r D lam s‖ ≤ (1 / period) * (4 * R) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch3_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R) = 4 * R / period := by ring
          rw [he]
          linarith [h1', h2, h3]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch4 r D lam s‖ ≤ (1 / period) * (4 * R / lam) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch4_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R / lam) = 4 * R / (lam * period) := by ring
          rw [he]
          linarith [h1', h2, h3]

/-- The arc branch of `chamferVel` is `1 / period` times the first branch value. -/
lemma chamferVelArc_eq_smul (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s t : ℝ) :
    chamferVelArc r D lam s t = (1 / period) • sweepBranch1 r D lam s (sweepParam t) := by
  simp only [chamferVelArc, sweepBranch1, velocity, smul_smul]
  congr 1
  ring

/-- The first-chamfer branch of `chamferVel` is `1 / period` times the second branch value. -/
lemma chamferVelChamfer₁_eq_smul (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s t : ℝ) :
    chamferVelChamfer₁ r D lam s t = (1 / period) • sweepBranch2 r D lam s := by
  simp only [chamferVelChamfer₁, sweepBranch2, smul_smul]
  congr 1
  ring

/-- The chord branch of `chamferVel` is `1 / period` times the third branch value. -/
lemma chamferVelChord_eq_smul (r : ℝ → Space) {d : BandArcData} (D : SweepData d) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1 / 2) (s t : ℝ) :
    chamferVelChord r D lam s t = (1 / period) • sweepBranch3 r D lam s := by
  have hd : (1 / 2 : ℝ) - lam ≠ 0 := by linarith
  simp only [chamferVelChord, sweepBranch3, smul_smul]
  congr 1
  rw [show (1 : ℝ) - 2 * lam = 2 * (1 / 2 - lam) by ring]
  field_simp

/-- The second-chamfer branch of `chamferVel` is `1 / period` times the fourth branch value. -/
lemma chamferVelChamfer₂_eq_smul (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam s t : ℝ) :
    chamferVelChamfer₂ r D lam s t = (1 / period) • sweepBranch4 r D lam s := by
  simp only [chamferVelChamfer₂, sweepBranch4, smul_smul]
  congr 1
  ring

/-- **The chamfered loop velocity is bounded by `doubleBlurLam`.** -/
lemma doubleBlur_chamferVel_bound {lam L R Tw : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hL : ∀ x : ℝ, ‖deriv r x‖ ≤ L) (hR : ∀ x : ℝ, ‖r x‖ ≤ R) (hTw : 0 ≤ Tw)
    (s : ℝ) (hW : |sweepW' D s| ≤ Tw) (t : ℝ) :
    ‖chamferVel r D lam s t‖ ≤ doubleBlurLam lam L R Tw := by
  have hp : (0 : ℝ) < period := period_pos
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (r 0)) (hR 0)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg (deriv r 0)) (hL 0)
  have hb1 : 0 ≤ 2 * Tw * L / period :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTw) hL0) hp.le
  have hb2 : 0 ≤ 4 * R / (lam * period) :=
    div_nonneg (mul_nonneg (by norm_num) hR0) (mul_pos h0 hp).le
  have hb3 : 0 ≤ 4 * R / period := div_nonneg (mul_nonneg (by norm_num) hR0) hp.le
  rw [chamferVel_eq_ite]
  split_ifs with hA hB hC
  · rw [chamferVelArc_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch1 r D lam s (sweepParam t)‖
        ≤ (1 / period) * (2 * Tw * L) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch1_norm_le h0 h1 hL hTw s hW _)
            (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (2 * Tw * L) = 2 * Tw * L / period := by ring
          rw [he]
          linarith [hb1, hb2, hb3]
  · rw [chamferVelChamfer₁_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch2 r D lam s‖ ≤ (1 / period) * (4 * R / lam) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch2_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R / lam) = 4 * R / (lam * period) := by ring
          rw [he]
          linarith [hb1, hb2, hb3]
  · rw [chamferVelChord_eq_smul r D h0 h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch3 r D lam s‖ ≤ (1 / period) * (4 * R) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch3_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R) = 4 * R / period := by ring
          rw [he]
          linarith [hb1, hb2, hb3]
  · rw [chamferVelChamfer₂_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
    calc (1 / period) * ‖sweepBranch4 r D lam s‖ ≤ (1 / period) * (4 * R / lam) :=
          mul_le_mul_of_nonneg_left (doubleBlur_sweepBranch4_norm_le h0 h1 hR s) (by positivity)
      _ ≤ doubleBlurLam lam L R Tw := by
          rw [doubleBlurLam]
          have he : (1 / period) * (4 * R / lam) = 4 * R / (lam * period) := by ring
          rw [he]
          linarith [hb1, hb2, hb3]

/-- **The raw loop is `doubleBlurLam`-Lipschitz in the loop parameter.** -/
lemma doubleBlur_loop_lipschitz {lam L R Tw : ℝ} (hr : ContDiff ℝ 1 r) (h0 : 0 < lam)
    (h1 : lam < 1 / 2) (s : ℝ) (hderiv : ∀ t : ℝ,
      ‖sweepLoopChamferDeriv r D lam s t‖ ≤ doubleBlurLam lam L R Tw) (a b : ℝ) :
    ‖sweepLoopChamfer r D lam s a - sweepLoopChamfer r D lam s b‖
      ≤ doubleBlurLam lam L R Tw * |a - b| := by
  rw [sweepLoopChamfer_ftc hr D h0 h1 s b a]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (C := doubleBlurLam lam L R Tw) (fun t _ => hderiv t)

/-! ## Differentiation under the outer integral -/

/-- The measure of `uIoc` is finite. -/
lemma doubleBlur_volume_Ioc_lt_top (c d : ℝ) : (volume : Measure ℝ) (Set.Ioc c d) < ⊤ := by
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

/-- Interval integrability from an a.e. strong measurability and a pointwise bound. -/
lemma doubleBlur_intervalIntegrable_of_bound {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    {C : ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Set.uIoc (-1 : ℝ) 1)))
    (hb : ∀ u : ℝ, ‖g u‖ ≤ C) : IntervalIntegrable g volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  exact MeasureTheory.IntegrableOn.of_bound (s := Set.uIoc (-1 : ℝ) 1)
    (doubleBlur_volume_Ioc_lt_top (min (-1) 1) (max (-1) 1)) hg C
    (Filter.Eventually.of_forall hb)
/-! ## Measurability of the composed singly blurred slice -/

/-- The singly blurred slice, composed with an affine map of the sweep parameter, is measurable. -/
lemma doubleBlur_aestronglyMeasurable_sweepSmoothT {r : ℝ → Space} (hr : Continuous r)
    {d : BandArcData} (D : SweepData d) (lam δ a b s : ℝ) :
    AEStronglyMeasurable (fun v : ℝ => sweepSmoothT r D lam δ (a - b * v) s)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
  have hjoint : Measurable (fun q : ℝ × ℝ =>
      sweepBump q.2 • sweepLoopChamfer r D lam (a - b * q.1) (s - δ * q.2)) := by
    have h1 : Measurable (fun q : ℝ × ℝ => ((a - b * q.1, s - δ * q.2) : ℝ × ℝ)) :=
      Measurable.prod (measurable_const.sub (measurable_const.mul measurable_fst))
        (measurable_const.sub (measurable_const.mul measurable_snd))
    exact (continuous_sweepBump.measurable.comp measurable_snd).smul
      ((sweepLoopChamfer_measurable D hr lam).comp h1)
  have h2 : StronglyMeasurable (fun v : ℝ => ∫ u : ℝ, sweepBump u •
      sweepLoopChamfer r D lam (a - b * v) (s - δ * u)
      ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
    hjoint.stronglyMeasurable.integral_prod_right
  refine (h2.aestronglyMeasurable.restrict).congr ?_
  filter_upwards with v
  rw [sweepSmoothT, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-! ## Differentiation under the outer integral -/

/-- **The derivative of the doubly blurred slice in the loop parameter.**  This is the analytic
content of `Work.Drive.sweepFam_double_blur_deriv`, stated with explicit data. -/
theorem doubleBlur_sweepFam_hasDerivAt {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ siglo sighi Λ M : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0)
    (h0 : 0 < lam) (h1 : lam < 1 / 2) (hl : 0 < siglo) (hh : sighi < 1) (hΛ : 0 ≤ Λ)
    (hbound : ∀ sig ∈ Set.Icc siglo sighi, ∀ t : ℝ, ‖chamferVel r D lam sig t‖ ≤ Λ)
    (hlip : ∀ sig ∈ Set.Icc siglo sighi, ∀ a b : ℝ,
      ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖ ≤ Λ * |a - b|)
    (hM : ∀ sig : ℝ, ∀ y : ℝ, ‖sweepLoopChamfer r D lam sig y‖ ≤ M)
    {sig s : ℝ} (hwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1, sig - δ₂ * v ∈ Set.Icc siglo sighi) :
    HasDerivAt (fun t : ℝ => sweepFam r D lam δ₁ δ₂ sig t)
      (∫ v in (-1 : ℝ)..1, sweepBump v •
        (∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam (sig - δ₂ * v) (s - δ₁ * u))) s := by
  have hv : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  -- the Lipschitz bound of a slice in its second argument
  have hLipS : ∀ σ ∈ Set.Icc siglo sighi, LipschitzWith (Real.toNNReal Λ)
      (fun t : ℝ => sweepSmoothT r D lam δ₁ σ t) := by
    intro σ hσ
    have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ => sweepSmoothT r D lam δ₁ σ x)
        (∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam σ (t - δ₁ * u)) t :=
      fun t => wideEnd_hasDerivAt_sweepSmoothT hr D hδ₁ h0 h1 hl hh hΛ hbound hlip hσ
    have hbnd : ∀ t : ℝ,
        ‖∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam σ (t - δ₁ * u)‖ ≤ Λ := by
      intro t
      have hI : IntervalIntegrable
          (fun u : ℝ => sweepBump u * ‖chamferVel r D lam σ (t - δ₁ * u)‖) volume (-1) 1 := by
        refine wideEnd_intervalIntegrable_of_bound (C := Λ)
          (continuous_sweepBump.measurable.mul ?_) (fun u => ?_)
        · exact (wideEnd_measurable_chamferVel hv D lam σ).norm.comp
            (measurable_const.sub (measurable_const.mul measurable_id))
        · rw [Real.norm_of_nonneg (mul_nonneg (sweepBump_nonneg u) (norm_nonneg _))]
          calc sweepBump u * ‖chamferVel r D lam σ (t - δ₁ * u)‖ ≤ 1 * Λ :=
                mul_le_mul (doubleBlur_sweepBump_le_one u) (hbound σ hσ _) (norm_nonneg _)
                  zero_le_one
            _ = Λ := one_mul _
      have hconst : IntervalIntegrable (fun u : ℝ => sweepBump u * Λ) volume (-1) 1 :=
        (continuous_sweepBump.mul_const Λ).intervalIntegrable _ _
      calc ‖∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam σ (t - δ₁ * u)‖
          ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u • chamferVel r D lam σ (t - δ₁ * u)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
        _ = ∫ u in (-1 : ℝ)..1, sweepBump u * ‖chamferVel r D lam σ (t - δ₁ * u)‖ := by
            refine intervalIntegral.integral_congr (fun u _ => ?_)
            rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * Λ :=
            intervalIntegral.integral_mono_on (by norm_num) hI hconst
              (fun u _ => mul_le_mul_of_nonneg_left (hbound σ hσ _) (sweepBump_nonneg u))
        _ = Λ := by rw [intervalIntegral.integral_mul_const, sweepBump_integral, one_mul]
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    have hcv : ‖sweepSmoothT r D lam δ₁ σ y - sweepSmoothT r D lam δ₁ σ x‖ ≤ Λ * |x - y| := by
      have h0' := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := fun t : ℝ => sweepSmoothT r D lam δ₁ σ t) (s := Set.univ) (C := Λ)
        (fun t _ => (hderiv t).differentiableAt)
        (fun t _ => by rw [(hderiv t).deriv]; exact hbnd t) convex_univ
        (Set.mem_univ x) (Set.mem_univ y)
      rw [Real.norm_eq_abs, abs_sub_comm] at h0'
      exact h0'
    rw [Real.dist_eq, dist_eq_norm, norm_sub_rev, Real.coe_toNNReal Λ hΛ]
    exact hcv
  -- measurability of the derivative side
  have hF'meas : AEStronglyMeasurable
      (fun v : ℝ => sweepBump v • ∫ u in (-1 : ℝ)..1,
        sweepBump u • chamferVel r D lam (sig - δ₂ * v) (s - δ₁ * u))
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    have hjoint : Measurable (fun q : ℝ × ℝ =>
        sweepBump q.2 • chamferVel r D lam (sig - δ₂ * q.1) (s - δ₁ * q.2)) := by
      have h1 : Measurable (fun q : ℝ × ℝ => ((sig - δ₂ * q.1, s - δ₁ * q.2) : ℝ × ℝ)) :=
        Measurable.prod (measurable_const.sub (measurable_const.mul measurable_fst))
          (measurable_const.sub (measurable_const.mul measurable_snd))
      exact (continuous_sweepBump.measurable.comp measurable_snd).smul
        ((wideEnd_measurable_chamferVel_joint hr.continuous hv D lam).comp h1)
    have h2 : StronglyMeasurable (fun v : ℝ => ∫ u : ℝ, sweepBump u •
        chamferVel r D lam (sig - δ₂ * v) (s - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
      hjoint.stronglyMeasurable.integral_prod_right
    have h3 : AEStronglyMeasurable (fun v : ℝ => sweepBump v • ∫ u : ℝ, sweepBump u •
        chamferVel r D lam (sig - δ₂ * v) (s - δ₁ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
        (volume.restrict (Set.uIoc (-1 : ℝ) 1)) :=
      continuous_sweepBump.aestronglyMeasurable.smul (h2.aestronglyMeasurable.restrict)
    refine h3.congr ?_
    filter_upwards with v
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (a := (-1 : ℝ)) (b := 1) (μ := (volume : Measure ℝ)) (E := Space)
    (F := fun t v => sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) t)
    (F' := fun v => sweepBump v •
      ∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam (sig - δ₂ * v) (s - δ₁ * u))
    (bound := fun v => ‖sweepBump v‖ * Λ) (x₀ := s) (s := Set.univ)
    Filter.univ_mem ?_ ?_ hF'meas ?_ ?_ ?_).2
  · -- measurability of the integrand
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact continuous_sweepBump.aestronglyMeasurable.smul
      (doubleBlur_aestronglyMeasurable_sweepSmoothT hr.continuous D lam δ₁ sig δ₂ x)
  · -- integrability of the slice
    refine doubleBlur_intervalIntegrable_of_bound (C := 2 * M)
      (continuous_sweepBump.aestronglyMeasurable.smul
        (doubleBlur_aestronglyMeasurable_sweepSmoothT hr.continuous D lam δ₁ sig δ₂ s))
      (fun v => ?_)
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    calc sweepBump v * ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) s‖ ≤ 1 * (2 * M) :=
          mul_le_mul (doubleBlur_sweepBump_le_one v)
            (doubleBlur_sweepSmoothT_norm_le lam (sig - δ₂ * v) (fun y => hM _ y) δ₁ s)
            (norm_nonneg _) zero_le_one
      _ = 2 * M := one_mul _
  · -- the Lipschitz bound of the integrand in the differentiation variable
    refine Filter.Eventually.of_forall (fun v hvv => ?_)
    have hvIcc : v ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hvv
      exact Set.Ioc_subset_Icc_self hvv
    have hσ : sig - δ₂ * v ∈ Set.Icc siglo sighi := hwin v hvIcc
    refine LipschitzOnWith.of_dist_le_mul (fun x _ y _ => ?_)
    have h1 : ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) x
        - sweepSmoothT r D lam δ₁ (sig - δ₂ * v) y‖ ≤ Λ * |x - y| := by
      have h0' := (lipschitzOnWith_iff_dist_le_mul.mp
        ((hLipS (sig - δ₂ * v) hσ).lipschitzOnWith (s := Set.univ)))
        x (Set.mem_univ x) y (Set.mem_univ y)
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal Λ hΛ] at h0'
      exact h0'
    have hgoal : (↑(Real.nnabs (‖sweepBump v‖ * Λ)) : ℝ) * dist x y
        = sweepBump v * Λ * |x - y| := by
      rw [Real.coe_nnabs, Real.norm_of_nonneg (sweepBump_nonneg v), Real.dist_eq,
        abs_of_nonneg (mul_nonneg (sweepBump_nonneg v) hΛ)]
    rw [hgoal, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (sweepBump_nonneg v)]
    calc sweepBump v * ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) x
          - sweepSmoothT r D lam δ₁ (sig - δ₂ * v) y‖
        ≤ sweepBump v * (Λ * |x - y|) := mul_le_mul_of_nonneg_left h1 (sweepBump_nonneg v)
      _ = sweepBump v * Λ * |x - y| := by ring
  · -- integrability of the dominating function
    exact (continuous_sweepBump.norm.mul_const Λ).intervalIntegrable _ _
  · -- the a.e. derivative
    refine Filter.Eventually.of_forall (fun v hvv => ?_)
    have hvIcc : v ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hvv
      exact Set.Ioc_subset_Icc_self hvv
    exact (wideEnd_hasDerivAt_sweepSmoothT hr D hδ₁ h0 h1 hl hh hΛ hbound hlip
      (hwin v hvIcc)).const_smul (sweepBump v)

/-! ## The target -/

theorem sweepFam_double_blur_deriv {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ σ t : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) (hδ₁ : δ₁ ≠ 0)
    (hδ₂ : 0 < δ₂) (hσlo : 0 < σ - δ₂) (hσhi : σ + δ₂ < 1) :
    HasDerivAt (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ u)
      (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
        (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u •
          Work.Drive.chamferVel r D lam (σ - δ₂ * v) (t - δ₁ * u))) t := by
  obtain ⟨L, hL0, hL⟩ := wideEnd_knot_bounded (hr.smooth.continuous_deriv (by simp))
    (doubleBlur_velocity_periodic hr)
  obtain ⟨R, hR0, hR⟩ := wideEnd_knot_bounded hr.continuous hr.periodic
  obtain ⟨Tw₀, hTw₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (σ - δ₂) (σ + δ₂)) (sweepLoopChamfer_sweepW'_continuous D).continuousOn
  set Tw : ℝ := max Tw₀ 0 with hTwdef
  have hTw : 0 ≤ Tw := le_max_right _ _
  have hW : ∀ sig ∈ Set.Icc (σ - δ₂) (σ + δ₂), |sweepW' D sig| ≤ Tw := by
    intro sig hsig
    have h := hTw₀ sig hsig
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  refine doubleBlur_sweepFam_hasDerivAt (M := R) hr D hδ₁ (ne_of_gt hδ₂) hlam0 hlam1 hσlo hσhi
    (doubleBlurLam_nonneg hlam0 hL0 hR0 hTw) ?_ ?_ ?_ ?_
  · exact fun sig hsig t => doubleBlur_chamferVel_bound hlam0 hlam1 hL hR hTw sig (hW sig hsig) t
  · exact fun sig hsig a b => doubleBlur_loop_lipschitz
      ((hr.smooth.of_le (by simp)).of_le one_le_coe_top) hlam0 hlam1
      sig (fun t => doubleBlur_chamferDeriv_bound hlam0 hlam1 hL hR hTw sig (hW sig hsig) t) a b
  · exact fun sig y => sweepLoopChamfer_norm_le hR hlam0 hlam1 sig y
  · intro v hv
    rw [Set.mem_Icc] at hv ⊢
    constructor
    · nlinarith [hv.2, hδ₂]
    · nlinarith [hv.1, hδ₂]

end Work.Drive
