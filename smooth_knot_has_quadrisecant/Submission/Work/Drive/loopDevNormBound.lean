import Mathlib
import Submission.Work.Drive.needleProfileDefs
import Submission.Work.Drive.dev_taylor_le

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-! ## Helper lemmas for the deviation bound -/

/-- `clampI` fixes the points of the unit interval. -/
lemma loopDevNormBound_clampI_eq {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    clampI s = (⟨s, h0, h1⟩ : unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 s) = s
  exact le_antisymm (le_trans (min_le_right _ _) (max_le h0 le_rfl))
    (le_min h1 (le_max_right _ _))

/-- `clampI` of a nonpositive real is `0`. -/
lemma loopDevNormBound_clampI_eq_zero {s : ℝ} (h : s ≤ 0) :
    clampI s = (0 : unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 s) = 0
  have hmax : max 0 s = (0 : ℝ) := le_antisymm (max_le le_rfl h) (le_max_left _ _)
  rw [hmax]
  exact le_antisymm (min_le_right _ _) (le_min zero_le_one le_rfl)

/-- `clampI` of a real `≥ 1` is `1`. -/
lemma loopDevNormBound_clampI_eq_one {s : ℝ} (h : 1 ≤ s) :
    clampI s = (1 : unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 s) = 1
  have hmax : max 0 s = s :=
    le_antisymm (max_le (le_trans zero_le_one h) le_rfl) (le_max_right _ _)
  rw [hmax]
  exact le_antisymm (min_le_left _ _) (le_min le_rfl h)

/-- The width of the retained arc is nonnegative for every real sweep parameter. -/
lemma loopDevNormBound_sweepW'_nonneg {d : BandArcData} (D : SweepData d) (sg : ℝ) :
    0 ≤ sweepW' D sg := by
  rcases lt_trichotomy sg 0 with h | h | h
  · have hcl : clampI sg = (0 : unitInterval) := loopDevNormBound_clampI_eq_zero h.le
    rw [show sweepW' D sg = sweepW D (clampI sg) from rfl, hcl, sweepW_zero]
  · rw [h]
    have hcl : clampI (0 : ℝ) = (0 : unitInterval) :=
      loopDevNormBound_clampI_eq_zero le_rfl
    rw [show sweepW' D (0 : ℝ) = sweepW D (clampI (0 : ℝ)) from rfl, hcl, sweepW_zero]
  · rcases lt_or_ge sg 1 with h1 | h1
    · have hcl : clampI sg = (⟨sg, h.le, h1.le⟩ : unitInterval) :=
        loopDevNormBound_clampI_eq h.le h1.le
      rw [show sweepW' D sg = sweepW D (clampI sg) from rfl, hcl]
      exact (sweepW_pos_lt D ⟨sg, h.le, h1.le⟩ ⟨h, h1⟩).1.le
    · have hcl : clampI sg = (1 : unitInterval) := loopDevNormBound_clampI_eq_one h1
      rw [show sweepW' D sg = sweepW D (clampI sg) from rfl, hcl, sweepW_one]
      exact period_pos.le

/-- The deviation vanishes when the retained arc degenerates. -/
lemma loopDevNormBound_loopDev_eq_zero {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {sg : ℝ} (h : sweepW' D sg = 0) (ξ : ℝ) : loopDev r D sg ξ = 0 := by
  have htb : tbR D sg = taR D sg := by
    have h' : tbR D sg - taR D sg = 0 := h
    linarith
  have hcoef : (1 - ξ) • r (taR D sg) + ξ • r (taR D sg) = r (taR D sg) := by
    rw [← add_smul, sub_add_cancel, one_smul]
  rw [loopDev, h, mul_zero, add_zero, htb, hcoef, sub_self]

theorem loopDevNormBound {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ ξ : ℝ), 0 ≤ ξ → ξ ≤ 1 →
      ‖Work.Drive.loopDev r D σ ξ‖ ≤ C * (Work.Drive.sweepW' D σ) ^ 2 := by
  obtain ⟨Ct, W₀, hCt, hW₀, hTay⟩ := dev_taylor_le hr 2 le_rfl
  obtain ⟨B₀, hB₀, hB₀b⟩ := exists_bound_iteratedDeriv_knot hr 0
  obtain ⟨B₂, hB₂, hB₂b⟩ := exists_bound_iteratedDeriv_knot hr 2
  refine ⟨Ct * W₀ + B₂ / 2 + 2 * B₀ / W₀ ^ 2 + 1, ?_, ?_⟩
  · have h1 : 0 < Ct * W₀ := mul_pos hCt hW₀
    have h2 : 0 ≤ B₂ / 2 := div_nonneg hB₂ (by norm_num)
    have h3 : 0 ≤ 2 * B₀ / W₀ ^ 2 := div_nonneg (by linarith) (sq_nonneg W₀)
    linarith
  · intro σ ξ hξ0 hξ1
    have hWnn : 0 ≤ sweepW' D σ := loopDevNormBound_sweepW'_nonneg D σ
    have hdev : loopDev r D σ ξ = dev r D σ ξ := rfl
    rcases eq_or_lt_of_le hWnn with hWz | hWp
    · have hzero : loopDev r D σ ξ = 0 := loopDevNormBound_loopDev_eq_zero D hWz.symm ξ
      rw [hzero, ← hWz]
      simp
    · rcases lt_or_ge (sweepW' D σ) W₀ with hlt | hge
      · have hle : sweepW' D σ ≤ W₀ := hlt.le
        have hT := hTay D (show sweepW' D σ ∈ Set.Ioc (0 : ℝ) W₀ from ⟨hWp, hle⟩) ξ
          ⟨hξ0, hξ1⟩
        have hsum : (∑ k ∈ Finset.Icc 2 2,
              ((∑ m ∈ Finset.range (k - 1), ξ ^ m) * (sweepW' D σ) ^ k / (k.factorial : ℝ)) •
                iteratedDeriv k r (taR D σ))
            = ((sweepW' D σ) ^ 2 / 2) • iteratedDeriv 2 r (taR D σ) := by
          rw [Finset.Icc_self, Finset.sum_singleton]
          norm_num
        rw [hsum] at hT
        set X : Space :=
          (ξ * (1 - ξ)) • (((sweepW' D σ) ^ 2 / 2) • iteratedDeriv 2 r (taR D σ)) with hX
        have hT' : ‖dev r D σ ξ + X‖ ≤ Ct * (sweepW' D σ) ^ 3 := by
          rw [hX]
          simpa using hT
        have hxi0 : 0 ≤ ξ * (1 - ξ) := mul_nonneg hξ0 (by linarith)
        have hxi1 : ξ * (1 - ξ) ≤ 1 := by nlinarith
        have hXb : ‖X‖ ≤ (sweepW' D σ) ^ 2 / 2 * B₂ := by
          rw [hX, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxi0,
            abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
          have hp : 0 ≤ (sweepW' D σ) ^ 2 / 2 * ‖iteratedDeriv 2 r (taR D σ)‖ :=
            mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (norm_nonneg _)
          calc ξ * (1 - ξ) * ((sweepW' D σ) ^ 2 / 2 * ‖iteratedDeriv 2 r (taR D σ)‖)
              ≤ 1 * ((sweepW' D σ) ^ 2 / 2 * ‖iteratedDeriv 2 r (taR D σ)‖) :=
                mul_le_mul_of_nonneg_right hxi1 hp
            _ ≤ 1 * ((sweepW' D σ) ^ 2 / 2 * B₂) := by
                refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
                exact mul_le_mul_of_nonneg_left (hB₂b _) (div_nonneg (sq_nonneg _) (by norm_num))
            _ = (sweepW' D σ) ^ 2 / 2 * B₂ := by ring
        have hstep : ‖loopDev r D σ ξ‖ ≤ Ct * (sweepW' D σ) ^ 3 + (sweepW' D σ) ^ 2 / 2 * B₂ := by
          have hXeq : loopDev r D σ ξ = (dev r D σ ξ + X) - X := by
            rw [hdev]; abel
          rw [hXeq]
          exact le_trans (norm_sub_le _ _) (add_le_add hT' hXb)
        have hfin : Ct * (sweepW' D σ) ^ 3 + (sweepW' D σ) ^ 2 / 2 * B₂
            ≤ (Ct * W₀ + B₂ / 2 + 2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2 := by
          have hw2 : 0 ≤ (sweepW' D σ) ^ 2 := sq_nonneg _
          have h3 : Ct * (sweepW' D σ) ^ 3 ≤ Ct * W₀ * (sweepW' D σ) ^ 2 := by
            calc Ct * (sweepW' D σ) ^ 3 = Ct * sweepW' D σ * (sweepW' D σ) ^ 2 := by ring
              _ ≤ Ct * W₀ * (sweepW' D σ) ^ 2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hCt.le) hw2
          have h4 : (sweepW' D σ) ^ 2 / 2 * B₂ = B₂ / 2 * (sweepW' D σ) ^ 2 := by ring
          rw [h4]
          have h5 : (Ct * W₀ + B₂ / 2 + 2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2
              = Ct * W₀ * (sweepW' D σ) ^ 2 + B₂ / 2 * (sweepW' D σ) ^ 2
                + (2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2 := by ring
          rw [h5]
          have h6 : 0 ≤ (2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2 := by
            refine mul_nonneg ?_ hw2
            have : 0 ≤ 2 * B₀ / W₀ ^ 2 := div_nonneg (by linarith) (sq_nonneg W₀)
            linarith
          linarith
        exact le_trans hstep hfin
      · have hcrude : ‖loopDev r D σ ξ‖ ≤ 2 * B₀ := by
          rw [loopDev]
          have ha : ‖r (taR D σ + ξ * sweepW' D σ)‖ ≤ B₀ := hB₀b _
          have hb : ‖r (taR D σ)‖ ≤ B₀ := hB₀b _
          have hc : ‖r (tbR D σ)‖ ≤ B₀ := hB₀b _
          have hsm : ‖(1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)‖ ≤ (1 - ξ) * B₀ + ξ * B₀ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg hξ0]
            exact add_le_add (mul_le_mul_of_nonneg_left hb (by linarith))
              (mul_le_mul_of_nonneg_left hc hξ0)
          calc ‖r (taR D σ + ξ * sweepW' D σ) - ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ))‖
              ≤ ‖r (taR D σ + ξ * sweepW' D σ)‖
                + ‖(1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)‖ := norm_sub_le _ _
            _ ≤ B₀ + ((1 - ξ) * B₀ + ξ * B₀) := add_le_add ha hsm
            _ = 2 * B₀ := by ring
        have hbig : 2 * B₀ ≤
            (Ct * W₀ + B₂ / 2 + 2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2 := by
          have hW2 : 0 < W₀ ^ 2 := pow_pos hW₀ 2
          have hcoef : 0 ≤ 2 * B₀ / W₀ ^ 2 := div_nonneg (by linarith) hW2.le
          have hsq : W₀ ^ 2 ≤ (sweepW' D σ) ^ 2 := by nlinarith [hge, hW₀, hWp]
          have h1 : 2 * B₀ / W₀ ^ 2 * W₀ ^ 2 = 2 * B₀ := by
            rw [div_mul_cancel₀ _ (ne_of_gt hW2)]
          calc 2 * B₀ = 2 * B₀ / W₀ ^ 2 * W₀ ^ 2 := h1.symm
            _ ≤ 2 * B₀ / W₀ ^ 2 * (sweepW' D σ) ^ 2 := mul_le_mul_of_nonneg_left hsq hcoef
            _ ≤ (Ct * W₀ + B₂ / 2 + 2 * B₀ / W₀ ^ 2 + 1) * (sweepW' D σ) ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                have h2 : 0 ≤ B₂ / 2 := div_nonneg hB₂ (by norm_num)
                have h3 : 0 ≤ Ct * W₀ := (mul_pos hCt hW₀).le
                linarith
        exact le_trans hcrude hbig

end Work.Drive
