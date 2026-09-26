import Mathlib
import Submission.Work.Drive.sweepFamWideTolDefs
import Submission.Work.Drive.chamferVelBranch
import Submission.Work.Drive.sweepFam_contDiff_periodic
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.spatial_le_slope_mul_dist
import Submission.Work.Drive.wideendRawPos
import Submission.Work.Drive.wideMatchRel
import Submission.Work.Drive.wideSig_tau_lipschitz
import Submission.Work.Drive.wideSig_sigma_modulus
import Submission.Work.Drive.sweepTopTools
import Submission.Work.Drive.sweepFam_double_blur_deriv
import Submission.Work.Drive.sweepLoopProfile_uniformCont_loop
import Submission.Work.Drive.widePhaseForm

/-!
# The wide-end estimate of the chord sweep, with a tolerance function

Target: `Work.Drive.sweepFam_wideEnd_estimate_tol`.  For a smooth knot `r` and a band-arc datum
`D` there is a tolerance function `tol` (positive below `1`, with infimum `0` at `1`) such that at
every sweep parameter `σ₀ < 1` and for every `ε₁ > tol σ₀` the doubly smoothed chord sweep
`Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀`, composed with a suitable increasing `period`-shifting
reparametrisation `Θ`, is `ε₁`-close to `r (· + c)` in `C¹`.

The proof has two halves.

* **Crude half.**  For *any* parameters the slice stays in the ball of radius `M₀ = sup ‖r‖` and
  its velocity is bounded by the Lipschitz constant `Λ` of the (raw) chamfered loop; hence with
  `Θ := id` the error is at most `C₀ = 2 M₀ + Λ + M₁`, uniformly in `σ₀` and in the parameters.
* **Fine half.**  Near `σ = 1` (more precisely when `d = period - sweepW' D σ₀` is small) the slice
  is `C¹`-close to the knot after reparametrisation; this is `Work.Drive.wideendFine` below.

The tolerance is `tol σ = K * (period - sweepW' D σ)` with `K` large enough that the two halves
patch: if `K * d ≥ C₀` the crude estimate applies, and otherwise `d` is so small that the fine
estimate applies with error `< K * d`.
-/

namespace Work.Drive

set_option maxHeartbeats 4000000
open LeanEval.KnotTheory.Quadrisecant
open MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## The clamped lifts and the width of the retained arc -/

lemma clampI_eq_zero {x : ℝ} (h : x ≤ 0) : clampI x = (0 : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = 0
  rw [max_eq_left h, min_eq_right zero_le_one]

lemma clampI_eq_one {x : ℝ} (h : 1 ≤ x) : clampI x = (1 : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = 1
  rw [max_eq_right (le_trans zero_le_one h), min_eq_left h]

lemma clampI_eq_self {x : ℝ} (h : x ∈ Set.Icc (0 : ℝ) 1) :
    clampI x = (⟨x, h⟩ : ↑unitInterval) := by
  apply Subtype.ext
  show min 1 (max 0 x) = x
  rw [max_eq_right h.1, min_eq_right h.2]

lemma sweepW'_eq_zero_of_nonpos {d : BandArcData} (D : SweepData d) {sig : ℝ} (h : sig ≤ 0) :
    sweepW' D sig = 0 := by
  have h1 : clampI sig = (0 : ↑unitInterval) := clampI_eq_zero h
  have h2 : taR D sig = D.ta 0 := by simp only [taR, h1]
  have h3 : tbR D sig = D.tb 0 := by simp only [tbR, h1]
  simp only [sweepW', h2, h3, ← D.left_eq, sub_self]

lemma sweepW'_eq_period_of_one_le {d : BandArcData} (D : SweepData d) {sig : ℝ} (h : 1 ≤ sig) :
    sweepW' D sig = period := by
  have h1 : clampI sig = (1 : ↑unitInterval) := clampI_eq_one h
  have h2 : taR D sig = D.ta 1 := by simp only [taR, h1]
  have h3 : tbR D sig = D.tb 1 := by simp only [tbR, h1]
  rw [sweepW', h2, h3, D.right_eq]
  ring

lemma sweepW'_nonneg_le {d : BandArcData} (D : SweepData d) (sig : ℝ) :
    0 ≤ sweepW' D sig ∧ sweepW' D sig ≤ period := by
  by_cases h0 : sig ≤ 0
  · rw [sweepW'_eq_zero_of_nonpos D h0]; exact ⟨le_rfl, period_pos.le⟩
  rw [not_le] at h0
  by_cases h1 : sig < 1
  · have hmem : sig ∈ Set.Ioo (0:ℝ) 1 := ⟨h0, h1⟩
    have hle : sig ∈ Set.Icc (0:ℝ) 1 := ⟨h0.le, h1.le⟩
    have hw : sweepW' D sig = sweepW D ⟨sig, hle⟩ := by
      simp only [sweepW', sweepW, taR, tbR, clampI_eq_self hle]
    rw [hw]
    exact ⟨(sweepW_pos_lt D ⟨sig, hle⟩ hmem).1.le, (sweepW_pos_lt D ⟨sig, hle⟩ hmem).2.le⟩
  · rw [not_lt] at h1
    rw [sweepW'_eq_period_of_one_le D h1]; exact ⟨period_pos.le, le_rfl⟩

lemma sweepW'_lt_period {d : BandArcData} (D : SweepData d) {sig : ℝ} (h : sig < 1) :
    sweepW' D sig < period := by
  by_cases h0 : sig ≤ 0
  · rw [sweepW'_eq_zero_of_nonpos D h0]; exact period_pos
  rw [not_le] at h0
  have hmem : sig ∈ Set.Ioo (0:ℝ) 1 := ⟨h0, h⟩
  have hle : sig ∈ Set.Icc (0:ℝ) 1 := ⟨h0.le, h.le⟩
  have hw : sweepW' D sig = sweepW D ⟨sig, hle⟩ := by
    simp only [sweepW', sweepW, taR, tbR, clampI_eq_self hle]
  rw [hw]
  exact (sweepW_pos_lt D ⟨sig, hle⟩ hmem).2

lemma taR_continuous {d : BandArcData} (D : SweepData d) : Continuous (taR D) :=
  D.cont_ta.comp (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

lemma tbR_continuous {d : BandArcData} (D : SweepData d) : Continuous (tbR D) :=
  D.cont_tb.comp (Continuous.subtype_mk (continuous_const.min (continuous_const.max continuous_id)) _)

lemma sweepW'_continuous {d : BandArcData} (D : SweepData d) : Continuous (sweepW' D) :=
  (tbR_continuous D).sub (taR_continuous D)

/-! ## Lipschitz bounds -/

/-- The knot is Lipschitz with the velocity bound. -/
lemma r_lipschitz {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) (x y : ℝ) : ‖r x - r y‖ ≤ M₁ * |x - y| := by
  have key : ∀ a b : ℝ, a ≤ b → ‖r b - r a‖ ≤ M₁ * |b - a| := by
    intro a b hab
    have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
    have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ r t := fun t _ =>
      (hr.differentiable (by simp)).differentiableAt
    have hderiv : ∀ t ∈ Set.Icc a b, ‖deriv r t‖ ≤ M₁ := fun t _ => by
      simpa only [velocity] using hM₁ t
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv hconv
      (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  rcases lt_or_ge x y with hxy | hxy
  · have h := key x y hxy.le
    rwa [norm_sub_rev, abs_sub_comm]
  · exact key y x hxy

/-- The deviation of the chord of the retained arc from the arc itself. -/
lemma sweepChord'_sub_sweepArc'_norm_le {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig ξ : ℝ)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    ‖sweepChord' r D sig ξ - sweepArc' r D sig ξ‖ ≤ 2 * M₁ * (ξ * (1 - ξ)) * sweepW' D sig := by
  have hw0 : 0 ≤ sweepW' D sig := (sweepW'_nonneg_le D sig).1
  have h1 : ‖r (taR D sig) - r (taR D sig + ξ * sweepW' D sig)‖ ≤ M₁ * (ξ * sweepW' D sig) := by
    have habs : |taR D sig - (taR D sig + ξ * sweepW' D sig)| = ξ * sweepW' D sig := by
      rw [show taR D sig - (taR D sig + ξ * sweepW' D sig) = -(ξ * sweepW' D sig) by ring,
        abs_neg, abs_of_nonneg (mul_nonneg hξ0 hw0)]
    simpa only [habs] using r_lipschitz hr hM₁ (taR D sig) (taR D sig + ξ * sweepW' D sig)
  have h2 : ‖r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig)‖
      ≤ M₁ * ((1 - ξ) * sweepW' D sig) := by
    have htb : tbR D sig = taR D sig + sweepW' D sig := by rw [sweepW']; ring
    have habs : |tbR D sig - (taR D sig + ξ * sweepW' D sig)| = (1 - ξ) * sweepW' D sig := by
      rw [show tbR D sig - (taR D sig + ξ * sweepW' D sig) = (1 - ξ) * sweepW' D sig by
        rw [htb]; ring, abs_of_nonneg (mul_nonneg (by linarith) hw0)]
    simpa only [habs] using r_lipschitz hr hM₁ (tbR D sig) (taR D sig + ξ * sweepW' D sig)
  have hsplit : sweepChord' r D sig ξ - sweepArc' r D sig ξ
      = (1 - ξ) • (r (taR D sig) - r (taR D sig + ξ * sweepW' D sig))
        + ξ • (r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig)) := by
    simp only [sweepChord', sweepArc']
    module
  rw [hsplit]
  have hsmul1 : ‖(1 - ξ) • (r (taR D sig) - r (taR D sig + ξ * sweepW' D sig))‖
      = (1 - ξ) * ‖r (taR D sig) - r (taR D sig + ξ * sweepW' D sig)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ξ)]
  have hsmul2 : ‖ξ • (r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig))‖
      = ξ * ‖r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
  calc ‖(1 - ξ) • (r (taR D sig) - r (taR D sig + ξ * sweepW' D sig))
          + ξ • (r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig))‖
      ≤ (1 - ξ) * ‖r (taR D sig) - r (taR D sig + ξ * sweepW' D sig)‖
        + ξ * ‖r (tbR D sig) - r (taR D sig + ξ * sweepW' D sig)‖ := by
        rw [← hsmul1, ← hsmul2]
        exact norm_add_le _ _
    _ ≤ (1 - ξ) * (M₁ * (ξ * sweepW' D sig)) + ξ * (M₁ * ((1 - ξ) * sweepW' D sig)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith))
          (mul_le_mul_of_nonneg_left h2 hξ0)
    _ = 2 * M₁ * (ξ * (1 - ξ)) * sweepW' D sig := by ring

/-! ## The Lipschitz constant of the raw loop -/

/-- **The profile loop is Lipschitz in the profile variable.** -/
lemma sweepLoopProfile_lipschitz_u {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig : ℝ)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) {a b : ℝ}
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a ≤ b) :
    ‖sweepLoopProfile r D lam sig b - sweepLoopProfile r D lam sig a‖
      ≤ 12 * M₁ * period * (b - a) := by
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hw := sweepW'_nonneg_le D sig
  have hP : 0 < period := period_pos
  have hba : 0 ≤ b - a := by linarith
  have hβ0 : 0 ≤ 2 * M₁ * lam * (1 - lam) * period := by
    have : 0 ≤ 1 - lam := by linarith
    positivity
  have hα0 : 0 ≤ 2 * M₁ * period * (b - a) := by positivity
  -- the arc variation
  have harc : ∀ x x' : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ x' → x' ≤ 1 → |x - x'| ≤ 2 * (b - a) →
      ‖sweepArc' r D sig x' - sweepArc' r D sig x‖ ≤ 2 * M₁ * period * (b - a) := by
    intro x x' _ _ _ _ hxx
    have hlift : |(taR D sig + x' * sweepW' D sig) - (taR D sig + x * sweepW' D sig)|
        ≤ 2 * (b - a) * period := by
      rw [show (taR D sig + x' * sweepW' D sig) - (taR D sig + x * sweepW' D sig)
          = (x' - x) * sweepW' D sig by ring, abs_mul]
      calc |x' - x| * |sweepW' D sig| ≤ (2 * (b - a)) * period := by
            refine mul_le_mul (by simpa only [abs_sub_comm] using hxx) ?_ (abs_nonneg _)
              (by linarith : (0:ℝ) ≤ 2 * (b - a))
            rw [abs_of_nonneg hw.1]
            exact hw.2
        _ = 2 * (b - a) * period := by ring
    have h := r_lipschitz hr hM₁ (taR D sig + x' * sweepW' D sig)
      (taR D sig + x * sweepW' D sig)
    have h' : ‖r (taR D sig + x' * sweepW' D sig) - r (taR D sig + x * sweepW' D sig)‖
        ≤ 2 * M₁ * period * (b - a) := by
      have h2 : ‖r (taR D sig + x' * sweepW' D sig) - r (taR D sig + x * sweepW' D sig)‖
          ≤ M₁ * |taR D sig + x' * sweepW' D sig - (taR D sig + x * sweepW' D sig)| := h
      have h3 := mul_le_mul_of_nonneg_left hlift hM₁0
      have h4 : M₁ * (2 * (b - a) * period) = 2 * M₁ * period * (b - a) := by ring
      linarith [h2, h3, h4]
    show ‖r (taR D sig + x' * sweepW' D sig) - r (taR D sig + x * sweepW' D sig)‖ ≤ _
    exact h' 
  -- the two chord deviations
  have hbeta : ‖sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam)‖
      ≤ 2 * M₁ * lam * (1 - lam) * period := by
    have hdev := sweepChord'_sub_sweepArc'_norm_le hr hM₁ D sig (1 - lam)
      (by linarith) (by linarith)
    rw [show (1:ℝ) - (1 - lam) = lam by ring] at hdev
    have hfac : (0:ℝ) ≤ 2 * M₁ * ((1 - lam) * lam) := by
      have : 0 ≤ 1 - lam := by linarith
      positivity
    refine hdev.trans ?_
    calc 2 * M₁ * ((1 - lam) * lam) * sweepW' D sig
        ≤ 2 * M₁ * ((1 - lam) * lam) * period := mul_le_mul_of_nonneg_left hw.2 hfac
      _ = 2 * M₁ * lam * (1 - lam) * period := by ring
  have hbeta' : ‖sweepChord' r D sig lam - sweepArc' r D sig lam‖
      ≤ 2 * M₁ * lam * (1 - lam) * period := by
    have hdev := sweepChord'_sub_sweepArc'_norm_le hr hM₁ D sig lam
      (le_of_lt h0) (by linarith)
    have hfac : (0:ℝ) ≤ 2 * M₁ * (lam * (1 - lam)) := by
      have : 0 ≤ 1 - lam := by linarith
      positivity
    refine hdev.trans ?_
    calc 2 * M₁ * (lam * (1 - lam)) * sweepW' D sig
        ≤ 2 * M₁ * (lam * (1 - lam)) * period := mul_le_mul_of_nonneg_left hw.2 hfac
      _ = 2 * M₁ * lam * (1 - lam) * period := by ring
  have hchord : 2 * ‖r (tbR D sig) - r (taR D sig)‖ * (b - a) ≤ 2 * M₁ * period * (b - a) := by
    have hlen : ‖r (tbR D sig) - r (taR D sig)‖ ≤ M₁ * period := by
      have htb : |tbR D sig - taR D sig| = sweepW' D sig := by
        have h1 : tbR D sig - taR D sig = sweepW' D sig := rfl
        rw [h1, abs_of_nonneg hw.1]
      have h := r_lipschitz hr hM₁ (tbR D sig) (taR D sig)
      rw [htb] at h
      exact h.trans (mul_le_mul_of_nonneg_left hw.2 hM₁0)
    nlinarith [hlen, hba]
  have hmain := sweepLoopProfile_diff_le (σ := sig)
    (α := 2 * M₁ * period * (b - a)) (β := 2 * M₁ * lam * (1 - lam) * period)
    D hα0 hβ0 h0 h4 ha hb hab harc hbeta hbeta' hchord
  have hmin : 2 * min 1 (2 * (b - a) / lam) * (2 * M₁ * lam * (1 - lam) * period)
      ≤ 8 * M₁ * period * (b - a) := by
    rcases le_or_gt (2 * (b - a) / lam) 1 with hle | hgt
    · rw [min_eq_right hle]
      have hkey : 2 * (2 * (b - a) / lam) * (2 * M₁ * lam * (1 - lam) * period)
          = 8 * M₁ * period * (b - a) * (1 - lam) := by field_simp; ring
      rw [hkey]
      have hfac : (0:ℝ) ≤ 8 * M₁ * period * (b - a) := by positivity
      calc 8 * M₁ * period * (b - a) * (1 - lam)
          ≤ 8 * M₁ * period * (b - a) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) - lam ≤ 1) hfac
        _ = 8 * M₁ * period * (b - a) := by ring
    · rw [min_eq_left hgt.le]
      have hlam_le : lam ≤ 2 * (b - a) := by
        rw [lt_div_iff₀ h0] at hgt
        linarith
      have hnorm : 2 * 1 * (2 * M₁ * lam * (1 - lam) * period)
          = 4 * M₁ * period * (lam * (1 - lam)) := by ring
      rw [hnorm]
      have hkey2 : lam * (1 - lam) ≤ 2 * (b - a) := by
        have h3 := mul_le_mul_of_nonneg_left (show (1:ℝ) - lam ≤ 1 by linarith) h0.le
        linarith
      calc 4 * M₁ * period * (lam * (1 - lam))
          ≤ 4 * M₁ * period * (2 * (b - a)) :=
            mul_le_mul_of_nonneg_left hkey2 (by positivity)
        _ = 8 * M₁ * period * (b - a) := by ring
  nlinarith [hmain, hmin]

/-- **The profile loop is Lipschitz on `[0,1]`, in the circular sense.** -/
lemma sweepLoopProfile_circular_le {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig : ℝ)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) {u u' : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hu' : u' ∈ Set.Icc (0:ℝ) 1) (h : u ≤ u') :
    ‖sweepLoopProfile r D lam sig u' - sweepLoopProfile r D lam sig u‖
      ≤ 12 * M₁ * period * (u' - u) :=
  sweepLoopProfile_lipschitz_u hr hM₁ D sig h0 h4 hu hu' h

/-- **The profile loop as a closed curve**: the circular Lipschitz bound across the seam. -/
lemma sweepLoopProfile_circular_ge {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig : ℝ)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) {u u' : ℝ}
    (hu : u ∈ Set.Icc (0:ℝ) 1) (hu' : u' ∈ Set.Icc (0:ℝ) 1) (h : u' ≤ u) :
    ‖sweepLoopProfile r D lam sig u' - sweepLoopProfile r D lam sig u‖
      ≤ 12 * M₁ * period * (u' + 1 - u) := by
  have h1 : lam < 1 := by linarith
  have h0' : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1' : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hbase : sweepLoopProfile r D lam sig 0 = sweepArc' r D sig lam :=
    sweepLoopProfile_zero r D lam sig
  have hbase' : sweepLoopProfile r D lam sig 1 = sweepArc' r D sig lam :=
    sweepLoopProfile_one D h0 h1 sig
  have hle1 : ‖sweepLoopProfile r D lam sig u' - sweepLoopProfile r D lam sig 0‖
      ≤ 12 * M₁ * period * (u' - 0) :=
    sweepLoopProfile_circular_le hr hM₁ D sig h0 h4 h0' hu' hu'.1
  have hle2 : ‖sweepLoopProfile r D lam sig 1 - sweepLoopProfile r D lam sig u‖
      ≤ 12 * M₁ * period * (1 - u) :=
    sweepLoopProfile_circular_le hr hM₁ D sig h0 h4 hu h1' hu.2
  have hdecomp : sweepLoopProfile r D lam sig u' - sweepLoopProfile r D lam sig u
      = (sweepLoopProfile r D lam sig u' - sweepLoopProfile r D lam sig 0)
        + (sweepLoopProfile r D lam sig 1 - sweepLoopProfile r D lam sig u) := by
    rw [hbase, hbase']
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [sub_zero] at hle1
  linarith

/-- **The raw chamfered loop is Lipschitz in the loop parameter**, uniformly in the sweep
parameter and in the chamfer fraction. -/
lemma sweepLoopChamfer_lipschitz {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig : ℝ)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (x y : ℝ) :
    ‖sweepLoopChamfer r D lam sig y - sweepLoopChamfer r D lam sig x‖
      ≤ 12 * M₁ * |y - x| := by
  have hP : 0 < period := period_pos
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have h1 : lam < 1 := by linarith
  have hmem : ∀ z : ℝ, sweepParam z ∈ Set.Icc (0:ℝ) 1 := fun z =>
    ⟨(sweepParam_mem z).1, (sweepParam_mem z).2.le⟩
  have hbridge : ∀ z : ℝ,
      sweepLoopChamfer r D lam sig z = sweepLoopProfile r D lam sig (sweepParam z) :=
    fun z => sweepLoopChamfer_eq_profile r D h0 h1 sig z
  -- the key estimate for `a ≤ b`
  have key : ∀ a b : ℝ, a ≤ b →
      ‖sweepLoopChamfer r D lam sig b - sweepLoopChamfer r D lam sig a‖
        ≤ 12 * M₁ * (b - a) := by
    intro a b hab
    rw [hbridge a, hbridge b]
    have hfl : ⌊a / period⌋ ≤ ⌊b / period⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right hab hP.le)
    have harith : (b - a) / period
        = (sweepParam b - sweepParam a) + ((⌊b / period⌋ : ℤ) - ⌊a / period⌋ : ℝ) := by
      simp only [sweepParam]
      push_cast
      ring
    have hknon : (0:ℝ) ≤ ((⌊b / period⌋ : ℤ) - ⌊a / period⌋ : ℝ) := by
      have h' : (0:ℤ) ≤ ⌊b / period⌋ - ⌊a / period⌋ := sub_nonneg.mpr hfl
      exact_mod_cast h'
    rcases le_total (sweepParam a) (sweepParam b) with huv | huv
    · have h := sweepLoopProfile_circular_le hr hM₁ D sig h0 h4 (hmem a) (hmem b) huv
      have hle : sweepParam b - sweepParam a ≤ (b - a) / period := by
        rw [harith]; linarith
      calc ‖sweepLoopProfile r D lam sig (sweepParam b)
              - sweepLoopProfile r D lam sig (sweepParam a)‖
          ≤ 12 * M₁ * period * (sweepParam b - sweepParam a) := h
        _ ≤ 12 * M₁ * period * ((b - a) / period) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 12 * M₁ * (b - a) := by
            field_simp [ne_of_gt hP]
    · by_cases hkeq : ⌊a / period⌋ = ⌊b / period⌋
      · -- equal floors: then `u_b = u_a` and the difference is zero
        have hzero : ((⌊b / period⌋ : ℤ) : ℝ) - ((⌊a / period⌋ : ℤ) : ℝ) = 0 := by
          rw [← hkeq]; simp
        have harith' : (b - a) / period = sweepParam b - sweepParam a := by
          rw [harith, hzero]; ring
        have h0' : 0 ≤ sweepParam b - sweepParam a := by rw [← harith']; positivity
        have hEq : sweepParam b = sweepParam a := by linarith
        rw [hEq, sub_self, norm_zero]
        positivity
      · -- different floors: the circular bound applies with the extra period
        have hlt : ⌊a / period⌋ < ⌊b / period⌋ := lt_of_le_of_ne hfl hkeq
        have hk1 : (1:ℝ) ≤ ((⌊b / period⌋ : ℤ) : ℝ) - ((⌊a / period⌋ : ℤ) : ℝ) := by
          have h' : (1:ℤ) ≤ ⌊b / period⌋ - ⌊a / period⌋ := by omega
          have h'' : ((1:ℤ) : ℝ) ≤ ((⌊b / period⌋ - ⌊a / period⌋ : ℤ) : ℝ) := by
            exact_mod_cast h'
          push_cast at h''
          exact h''
        have h := sweepLoopProfile_circular_ge hr hM₁ D sig h0 h4 (hmem a) (hmem b) huv
        have hle : sweepParam b + 1 - sweepParam a ≤ (b - a) / period := by
          rw [harith]
          push_cast
          linarith
        calc ‖sweepLoopProfile r D lam sig (sweepParam b)
                - sweepLoopProfile r D lam sig (sweepParam a)‖
            ≤ 12 * M₁ * period * (sweepParam b + 1 - sweepParam a) := h
          _ ≤ 12 * M₁ * period * ((b - a) / period) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ = 12 * M₁ * (b - a) := by
              field_simp [ne_of_gt hP]
  rcases lt_or_ge x y with hxy | hxy
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x)]
    exact key x y hxy.le
  · rw [abs_of_nonpos (by linarith : y - x ≤ 0), norm_sub_rev,
      show -(y - x) = x - y by ring]
    exact key y x hxy

/-! ## Norm bounds for the raw loop and the smoothed slice -/

/-- **Every point of the raw loop lies in the ball of radius `M₀`.** -/
lemma sweepLoopChamfer_norm_le' {r : ℝ → Space} {M₀ : ℝ} (hM₀ : ∀ t : ℝ, ‖r t‖ ≤ M₀)
    {d : BandArcData} (D : SweepData d) {lam sig τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ‖sweepLoopChamfer r D lam sig τ‖ ≤ M₀ := by
  have hball : ∀ a b : Space, ‖a‖ ≤ M₀ → ‖b‖ ≤ M₀ → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 →
      ‖(1 - ξ) • a + ξ • b‖ ≤ M₀ := by
    intro a b ha hb ξ hξ0 hξ1
    calc ‖(1 - ξ) • a + ξ • b‖
        ≤ ‖(1 - ξ) • a‖ + ‖ξ • b‖ := norm_add_le _ _
      _ = (1 - ξ) * ‖a‖ + ξ * ‖b‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ξ), abs_of_nonneg hξ0]
      _ ≤ (1 - ξ) * M₀ + ξ * M₀ :=
          add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
            (mul_le_mul_of_nonneg_left hb hξ0)
      _ = M₀ := by ring
  have harc : ∀ ξ : ℝ, ‖sweepArc' r D sig ξ‖ ≤ M₀ := by
    intro ξ; simp only [sweepArc']; exact hM₀ _
  have hchordpt : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ‖sweepChord' r D sig ξ‖ ≤ M₀ := by
    intro ξ hξ0 hξ1
    simp only [sweepChord']
    exact hball (r (taR D sig)) (r (tbR D sig)) (hM₀ _) (hM₀ _) ξ hξ0 hξ1
  have hmem := sweepParam_mem τ
  simp only [sweepLoopChamfer]
  split_ifs with h h2 h3
  · simp only [sweepArc']
    exact hM₀ _
  · refine hball (sweepArc' r D sig (1 - lam)) (sweepChord' r D sig (1 - lam))
      (harc _) (hchordpt _ (by linarith) (by linarith))
      ((2 * sweepParam τ - 1) / lam) ?_ ?_
    · rw [div_nonneg_iff]
      exact Or.inl ⟨by linarith [not_le.mp h], h0.le⟩
    · rw [div_le_one h0]
      linarith
  · have ht0 : 0 ≤ (sweepParam τ - (1 / 2 + lam / 2)) / (1 / 2 - lam) :=
      div_nonneg (by linarith [not_le.mp h2]) (by linarith)
    have ht1 : (sweepParam τ - (1 / 2 + lam / 2)) / (1 / 2 - lam) ≤ 1 := by
      rw [div_le_one (by linarith : (0:ℝ) < 1 / 2 - lam)]
      linarith [h3]
    refine hchordpt _ ?_ ?_
    · nlinarith [ht0, ht1, h0, h1]
    · nlinarith [ht0, ht1, h0, h1]
  · refine hball (sweepChord' r D sig lam) (sweepArc' r D sig lam)
      (hchordpt _ (by linarith) (by linarith)) (harc _)
      ((sweepParam τ - (1 - lam / 2)) / (lam / 2)) ?_ ?_
    · rw [div_nonneg_iff]
      exact Or.inl ⟨by linarith [not_le.mp h3], by linarith⟩
    · rw [div_le_one (by linarith : (0:ℝ) < lam / 2)]
      linarith [hmem.2]

/-- The raw loop is continuous in the loop parameter. -/
lemma sweepLoopChamfer_continuous {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d) (sig : ℝ)
    {lam : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) :
    Continuous (fun τ : ℝ => sweepLoopChamfer r D lam sig τ) := by
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hpos : (0:ℝ) < (12 * M₁ + 1) * 2 := by linarith
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / ((12 * M₁ + 1) * 2), by positivity, fun a ha => ?_⟩
  rw [Real.dist_eq] at ha
  rw [dist_eq_norm, norm_sub_rev]
  have h := sweepLoopChamfer_lipschitz hr hM₁ D sig h0 h4 a b
  have h2 : |b - a| ≤ ε / ((12 * M₁ + 1) * 2) := by rw [abs_sub_comm]; exact le_of_lt ha
  calc ‖sweepLoopChamfer r D lam sig b - sweepLoopChamfer r D lam sig a‖
      ≤ 12 * M₁ * |b - a| := h
    _ ≤ (12 * M₁ + 1) * |b - a| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        linarith
    _ ≤ (12 * M₁ + 1) * (ε / ((12 * M₁ + 1) * 2)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- **The smoothed slice lies in the ball of radius `M₀`.** -/
lemma sweepFam_norm_le {r : ℝ → Space} {M₀ M₁ : ℝ} (hM₀ : ∀ t : ℝ, ‖r t‖ ≤ M₀)
    (hr : ContDiff ℝ ⊤ r) (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁)
    {d : BandArcData} (D : SweepData d) {lam δ₁ δ₂ sig τ : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (h4 : lam ≤ 1 / 4) :
    ‖sweepFam r D lam δ₁ δ₂ sig τ‖ ≤ 2 * M₀ := by
  have hinner : ∀ s : ℝ, ‖sweepSmoothT r D lam δ₁ s τ‖ ≤ M₀ := by
    intro s
    have hcont : Continuous (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam s (τ - δ₁ * u)) :=
      sweepBump_continuous.smul ((sweepLoopChamfer_continuous hr hM₁ D s h0 h4).comp
        (continuous_const.sub (continuous_const.mul continuous_id)))
    simp only [sweepSmoothT]
    calc ‖∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam s (τ - δ₁ * u)‖
        ≤ ∫ u in (-1 : ℝ)..1, ‖sweepBump u • sweepLoopChamfer r D lam s (τ - δ₁ * u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * M₀ := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            (hcont.norm.intervalIntegrable _ _)
            ((sweepBump_continuous.mul continuous_const).intervalIntegrable _ _) ?_
          intro u _
          rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
          exact mul_le_mul_of_nonneg_left (sweepLoopChamfer_norm_le' hM₀ D h0 h1)
            (sweepBump_nonneg u)
      _ = M₀ := by rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  simp only [sweepFam]
  calc ‖∫ v in (-1 : ℝ)..1, sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ‖
      ≤ M₀ * |(1 : ℝ) - (-1)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (C := M₀) (fun v _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg v)]
        calc sweepBump v * ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ‖ ≤ 1 * M₀ :=
              mul_le_mul (doubleBlur_sweepBump_le_one v) (hinner _) (norm_nonneg _) zero_le_one
          _ = M₀ := one_mul M₀
    _ = 2 * M₀ := by ring

/-- **The singly smoothed slice is Lipschitz in the loop parameter.** -/
lemma sweepSmoothT_lipschitz {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₁ : ℝ}
    (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁) {d : BandArcData} (D : SweepData d)
    {lam δ₁ sig : ℝ} (h0 : 0 < lam) (h4 : lam ≤ 1 / 4) (τ τ' : ℝ) :
    ‖sweepSmoothT r D lam δ₁ sig τ - sweepSmoothT r D lam δ₁ sig τ'‖ ≤ 12 * M₁ * |τ - τ'| := by
  have hrawL : ∀ (x y : ℝ),
      ‖sweepLoopChamfer r D lam sig x - sweepLoopChamfer r D lam sig y‖ ≤ 12 * M₁ * |x - y| :=
    fun x y => sweepLoopChamfer_lipschitz (M₁ := M₁) (D := D) (sig := sig) (lam := lam)
      hr hM₁ h0 h4 y x
  have hrawc : Continuous (fun x : ℝ => sweepLoopChamfer r D lam sig x) :=
    sweepLoopChamfer_continuous (M₁ := M₁) (D := D) (sig := sig) (lam := lam) hr hM₁ h0 h4
  have harg1 : Continuous (fun u : ℝ => τ - δ₁ * u) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have harg2 : Continuous (fun u : ℝ => τ' - δ₁ * u) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hcont1 : Continuous (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam sig (τ - δ₁ * u)) :=
    sweepBump_continuous.smul (hrawc.comp harg1)
  have hcont2 : Continuous (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam sig (τ' - δ₁ * u)) :=
    sweepBump_continuous.smul (hrawc.comp harg2)
  have hcont3 : Continuous (fun u : ℝ => sweepBump u •
      (sweepLoopChamfer r D lam sig (τ - δ₁ * u)
        - sweepLoopChamfer r D lam sig (τ' - δ₁ * u))) :=
    sweepBump_continuous.smul ((hrawc.comp harg1).sub (hrawc.comp harg2))
  have hsub : sweepSmoothT r D lam δ₁ sig τ - sweepSmoothT r D lam δ₁ sig τ'
      = ∫ u in (-1 : ℝ)..1, sweepBump u •
          (sweepLoopChamfer r D lam sig (τ - δ₁ * u)
            - sweepLoopChamfer r D lam sig (τ' - δ₁ * u)) := by
    rw [show sweepSmoothT r D lam δ₁ sig τ
        = ∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam sig (τ - δ₁ * u) from rfl,
      show sweepSmoothT r D lam δ₁ sig τ'
        = ∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam sig (τ' - δ₁ * u) from rfl,
      ← intervalIntegral.integral_sub (hcont1.intervalIntegrable (-1) 1)
        (hcont2.intervalIntegrable (-1) 1)]
    exact intervalIntegral.integral_congr (fun u _ => by rw [smul_sub])
  rw [hsub]
  calc ‖∫ u in (-1 : ℝ)..1, sweepBump u •
          (sweepLoopChamfer r D lam sig (τ - δ₁ * u) - sweepLoopChamfer r D lam sig (τ' - δ₁ * u))‖
      ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * (12 * M₁ * |τ - τ'|) := by
        refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans ?_
        refine intervalIntegral.integral_mono_on (by norm_num)
          (hcont3.norm.intervalIntegrable _ _)
          ((sweepBump_continuous.mul continuous_const).intervalIntegrable _ _) ?_
        intro u _
        rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg u)]
        refine mul_le_mul_of_nonneg_left ?_ (sweepBump_nonneg u)
        have h := hrawL (τ - δ₁ * u) (τ' - δ₁ * u)
        rwa [show (τ - δ₁ * u) - (τ' - δ₁ * u) = τ - τ' by ring] at h
    _ = 12 * M₁ * |τ - τ'| := by
        rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]

/-- **The smoothed slice is Lipschitz in the loop parameter** (the raw loop's constant). -/
lemma sweepFam_lipschitz {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₀ M₁ : ℝ}
    (hM₀ : ∀ t : ℝ, ‖r t‖ ≤ M₀) (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁)
    {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ sig : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (h4 : lam ≤ 1 / 4) (τ τ' : ℝ) :
    ‖sweepFam r D lam δ₁ δ₂ sig τ - sweepFam r D lam δ₁ δ₂ sig τ'‖ ≤ 24 * M₁ * |τ - τ'| := by
  have hbd : ∀ τ₀ : ℝ, ∀ v : ℝ,
      ‖sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ₀‖ ≤ 2 * M₀ := by
    intro τ₀ v
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg v)]
    calc sweepBump v * ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ₀‖ ≤ 1 * (2 * M₀) := by
          refine mul_le_mul (doubleBlur_sweepBump_le_one v) ?_ (norm_nonneg _) zero_le_one
          exact doubleBlur_sweepSmoothT_norm_le (lam := lam) (sig := sig - δ₂ * v)
            (fun y => sweepLoopChamfer_norm_le' hM₀ D h0 h1) δ₁ τ₀
      _ = 2 * M₀ := one_mul _
  have hint1 : IntervalIntegrable
      (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ) volume (-1) 1 :=
    doubleBlur_intervalIntegrable_of_bound
      (continuous_sweepBump.aestronglyMeasurable.smul
        (doubleBlur_aestronglyMeasurable_sweepSmoothT hr.continuous D lam δ₁ sig δ₂ τ)) (hbd τ)
  have hint2 : IntervalIntegrable
      (fun v : ℝ => sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ') volume (-1) 1 :=
    doubleBlur_intervalIntegrable_of_bound
      (continuous_sweepBump.aestronglyMeasurable.smul
        (doubleBlur_aestronglyMeasurable_sweepSmoothT hr.continuous D lam δ₁ sig δ₂ τ')) (hbd τ')
  have hsub : sweepFam r D lam δ₁ δ₂ sig τ - sweepFam r D lam δ₁ δ₂ sig τ'
      = ∫ v in (-1 : ℝ)..1, sweepBump v •
          (sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ
            - sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ') := by
    rw [show sweepFam r D lam δ₁ δ₂ sig τ
        = ∫ v in (-1 : ℝ)..1, sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ from rfl,
      show sweepFam r D lam δ₁ δ₂ sig τ'
        = ∫ v in (-1 : ℝ)..1, sweepBump v • sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ' from rfl,
      ← intervalIntegral.integral_sub hint1 hint2]
    exact intervalIntegral.integral_congr (fun v _ => by rw [smul_sub])
  rw [hsub]
  calc ‖∫ v in (-1 : ℝ)..1, sweepBump v •
          (sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ
            - sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ')‖
      ≤ (12 * M₁ * |τ - τ'|) * |(1 : ℝ) - (-1)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const
          (C := 12 * M₁ * |τ - τ'|) (fun v _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sweepBump_nonneg v)]
        calc sweepBump v * ‖sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ
              - sweepSmoothT r D lam δ₁ (sig - δ₂ * v) τ'‖
            ≤ 1 * (12 * M₁ * |τ - τ'|) :=
              mul_le_mul (doubleBlur_sweepBump_le_one v)
                (sweepSmoothT_lipschitz hr hM₁ D h0 h4 τ τ') (norm_nonneg _) zero_le_one
          _ = 12 * M₁ * |τ - τ'| := one_mul _
    _ = 24 * M₁ * |τ - τ'| := by norm_num; ring

set_option maxHeartbeats 2000000 in

/-- **The derivative of the smoothed slice is bounded by the raw loop's Lipschitz constant.** -/
lemma sweepFam_deriv_norm_le {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) {M₀ M₁ : ℝ}
    (hM₀ : ∀ t : ℝ, ‖r t‖ ≤ M₀) (hM₁ : ∀ t, ‖velocity r t‖ ≤ M₁)
    {d : BandArcData} (D : SweepData d)
    {lam δ₁ δ₂ sig : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (h4 : lam ≤ 1 / 4)
    (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (t : ℝ) :
    ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t‖ ≤ 24 * M₁ := by
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hK : (0:ℝ) ≤ 24 * M₁ := by positivity
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) :=
    (sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ hδ₁ hδ₂).2.2 sig
  have hdiff : HasFDerivAt (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u)
      (fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t) t :=
    ((hsm.differentiable (by simp)) t).hasFDerivAt
  have hlip : LipschitzWith (Real.toNNReal (24 * M₁))
      (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal _ hK]
    exact sweepFam_lipschitz hr hM₀ hM₁ D h0 h1 h4 x y
  have hnorm : ‖fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t‖ ≤ Real.toNNReal (24 * M₁) :=
    hdiff.le_of_lipschitz hlip
  have hderiv : HasDerivAt (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u)
      (fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t 1) t := hdiff.hasDerivAt
  calc ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t‖
      = ‖fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t 1‖ := by
        rw [hderiv.deriv]
    _ ≤ ‖fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t‖ * ‖(1:ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ sig u) t‖ := by norm_num
    _ ≤ Real.toNNReal (24 * M₁) := hnorm
    _ = 24 * M₁ := Real.coe_toNNReal _ hK

/-! ## The phase transfer -/

/-- **The phase transfer.**  If a curve `Φ` has an analytic `period`-shifting phase `ψ` with
`deriv ψ > 0` such that `Φ` is `ε/2`-close to `r ∘ ψ` and its derivative is `ε/2`-close,
*relatively to `deriv ψ`*, to `deriv ψ • velocity r (ψ ·)`, then composing `Φ` with the inverse of
`ψ` produces the two closeness clauses with `c = 0`. -/
lemma reparamOfPhase {r Φ : ℝ → Space} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hshift : ∀ t : ℝ, ψ (t + period) = ψ t + period) (hpos : ∀ t : ℝ, 0 < deriv ψ t)
    {ε : ℝ} (hε : 0 < ε)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (h1 : ∀ t : ℝ, ‖Φ t - r (ψ t)‖ ≤ ε / 2)
    (h2 : ∀ t : ℝ, ‖deriv Φ t - deriv ψ t • velocity r (ψ t)‖ ≤ (ε / 2) * deriv ψ t) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧ (∀ t : ℝ, 0 < deriv Θ t) ∧
      (∀ t : ℝ, ‖Φ (Θ t) - r t‖ < ε) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => Φ (Θ u)) t - velocity r t‖ < ε) := by
  obtain ⟨Θ, hsm, hposΘ, hshiftΘ, -, hright, hderiv⟩ :=
    exists_contDiff_inverse_of_shift period_pos hψ hpos hshift
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨Θ, hsm, hshiftΘ, hposΘ, ?_, ?_⟩
  · intro t
    have h := h1 (Θ t)
    rw [hright t] at h
    linarith
  · intro t
    have hd1 : DifferentiableAt ℝ Φ (Θ t) := (hΦ.differentiable hne) (Θ t)
    have hd2 : DifferentiableAt ℝ Θ t := (hsm.differentiable hne) t
    have hchain : deriv (fun u : ℝ => Φ (Θ u)) t = deriv Θ t • deriv Φ (Θ t) :=
      deriv.scomp t hd1 hd2
    have h2' := h2 (Θ t)
    rw [hright t] at h2'
    have hkey : deriv Θ t • (deriv Φ (Θ t) - deriv ψ (Θ t) • velocity r t)
        = deriv Θ t • deriv Φ (Θ t) - velocity r t := by
      rw [smul_sub, hderiv t, smul_smul, inv_mul_cancel₀ (ne_of_gt (hpos (Θ t))), one_smul]
    calc ‖deriv (fun u : ℝ => Φ (Θ u)) t - velocity r t‖
        = ‖deriv Θ t • (deriv Φ (Θ t) - deriv ψ (Θ t) • velocity r t)‖ := by
            rw [hchain, ← hkey]
      _ = deriv Θ t * ‖deriv Φ (Θ t) - deriv ψ (Θ t) • velocity r t‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hposΘ t))]
      _ ≤ deriv Θ t * ((ε / 2) * deriv ψ (Θ t)) :=
            mul_le_mul_of_nonneg_left h2' (le_of_lt (hposΘ t))
      _ = ε / 2 := by
            rw [hderiv t]
            field_simp
            exact div_self (ne_of_gt (hpos (Θ t)))
      _ < ε := by linarith


/-! ## Numeric bounds of the knot -/

/-- **Numeric bounds of a smooth knot**: a bound on the curve, a bound on the speed and a
Lipschitz constant for the velocity. -/
lemma exists_knot_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ M₀ M₁ M₂ : ℝ, 0 < M₀ ∧ 0 < M₁ ∧ 0 < M₂ ∧
      (∀ t : ℝ, ‖r t‖ ≤ M₀) ∧ (∀ t : ℝ, ‖velocity r t‖ ≤ M₁) ∧
      (∀ x y : ℝ, ‖velocity r x - velocity r y‖ ≤ M₂ * |x - y|) := by
  obtain ⟨m, M₁, M₂, hm, hM₁, hM₂, -, hM₁b, hM₂b⟩ := exists_knot_c2_bounds hr
  refine ⟨‖r 0‖ + M₁ * period + 1, M₁, M₂, by have := period_pos; positivity, hM₁, hM₂, ?_,
    hM₁b, fun x y => by rw [abs_sub_comm]; exact hM₂b x y⟩
  intro t
  obtain ⟨n, hn⟩ := exists_zsmul_add_mem_Ico t
  have hshift : r (t + n • period) = r t := hr.periodic.zsmul n t
  have hdecomp : r (t + n • period) = r 0 + (r (t + n • period) - r 0) := by abel
  have hbound : ‖r (t + n • period) - r 0‖ ≤ M₁ * period := by
    have h1 := norm_sub_le_of_velocity_bound_mul (f := r) (hr.smooth.differentiable (by simp))
      hM₁b (t + n • period) 0
    rw [sub_zero] at h1
    have h2 : |t + n • period| ≤ period := by
      rw [abs_of_nonneg (by linarith [hn.1])]; exact hn.2.le
    linarith [mul_le_mul_of_nonneg_left h2 hM₁.le]
  rw [← hshift, hdecomp]
  calc ‖r 0 + (r (t + n • period) - r 0)‖
      ≤ ‖r 0‖ + ‖r (t + n • period) - r 0‖ := norm_add_le _ _
    _ ≤ ‖r 0‖ + M₁ * period := by linarith
    _ ≤ ‖r 0‖ + M₁ * period + 1 := by linarith

/-! ## The crude estimate -/

/-- **The crude estimate.**  For *every* sweep parameter the doubly smoothed slice, composed with
the identity reparametrisation, is `C¹`-close to the knot, with an error bounded uniformly by
`max (2 * M₀) (13 * M₁)`. -/
lemma crudeEstimate {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {M₀ M₁ : ℝ} (hM₀ : ∀ t : ℝ, ‖r t‖ ≤ M₀)
    (hM₁ : ∀ t : ℝ, ‖velocity r t‖ ≤ M₁)
    (σ₀ : ℝ) {ε₁ L : ℝ} (hL : 0 < L) (hε : max (3 * M₀) (25 * M₁) < ε₁) :
    ∃ (lam δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
      0 < lam ∧ lam ≤ L ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
      (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
      (∀ t : ℝ, 0 < deriv Θ t) ∧
      (∀ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
        - velocity r (t + c)‖ < ε₁) := by
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0)
  have hM₁0 : (0 : ℝ) ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hL4 : (0 : ℝ) < min L (1 / 4) := lt_min hL (by norm_num)
  have hL1 : (0 : ℝ) < min L 1 := lt_min hL (by norm_num)
  refine ⟨min L (1 / 4) / 2, min L 1 / 2, min L 1 / 2, 0, id, ?_, ?_, ?_, ?_, ?_, ?_,
    contDiff_id, ?_, ?_, ?_, ?_⟩
  · positivity
  · have h : min L (1 / 4) / 2 ≤ min L (1 / 4) := by linarith
    exact le_trans h (min_le_left _ _)
  · positivity
  · have h : min L 1 / 2 ≤ min L 1 := by linarith
    exact le_trans h (min_le_left _ _)
  · positivity
  · have h : min L 1 / 2 ≤ min L 1 := by linarith
    exact le_trans h (min_le_left _ _)
  · intro t; simp
  · intro t; simp
  · intro t
    have h0 : 0 < min L (1 / 4) / 2 := by positivity
    have h1 : min L (1 / 4) / 2 < 1 := by
      have h : min L (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have h4 : min L (1 / 4) / 2 ≤ 1 / 4 := by
      have h : min L (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have h := sweepFam_norm_le (r := r) (M₀ := M₀) (M₁ := M₁) hM₀ hr.smooth hM₁ D h0 h1 h4
      (δ₁ := min L 1 / 2) (δ₂ := min L 1 / 2) (sig := σ₀) (τ := t)
    have h2 : ‖r t‖ ≤ M₀ := hM₀ t
    have : ‖sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2) (min L 1 / 2) σ₀ t - r t‖
        ≤ 3 * M₀ := by
      calc ‖sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2) (min L 1 / 2) σ₀ t - r t‖
          ≤ ‖sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2) (min L 1 / 2) σ₀ t‖ + ‖r t‖ :=
            norm_sub_le _ _
        _ ≤ 2 * M₀ + M₀ := add_le_add h h2
        _ = 3 * M₀ := by ring
    simp only [id_eq, add_zero]
    exact lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left _ _) hε)
  · intro t
    have h0 : 0 < min L (1 / 4) / 2 := by positivity
    have h1' : min L (1 / 4) / 2 < 1 := by
      have h : min L (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have h4 : min L (1 / 4) / 2 ≤ 1 / 4 := by
      have h : min L (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
    have hδ₁ : (min L 1 / 2 : ℝ) ≠ 0 := by positivity
    have hδ₂ : (min L 1 / 2 : ℝ) ≠ 0 := by positivity
    have h := sweepFam_deriv_norm_le (r := r) (M₀ := M₀) (M₁ := M₁) hr.smooth hM₀ hM₁ D
      (δ₁ := min L 1 / 2) (δ₂ := min L 1 / 2) (sig := σ₀) h0 h1' h4 hδ₁ hδ₂ t
    have h2 : ‖velocity r t‖ ≤ M₁ := hM₁ t
    have : ‖deriv (fun u : ℝ => sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2)
        (min L 1 / 2) σ₀ u) t - velocity r t‖ ≤ 25 * M₁ := by
      calc ‖deriv (fun u : ℝ => sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2)
            (min L 1 / 2) σ₀ u) t - velocity r t‖
          ≤ ‖deriv (fun u : ℝ => sweepFam r D (min L (1 / 4) / 2) (min L 1 / 2)
              (min L 1 / 2) σ₀ u) t‖ + ‖velocity r t‖ := norm_sub_le _ _
        _ ≤ 24 * M₁ + M₁ := add_le_add h h2
        _ = 25 * M₁ := by ring
    simp only [id_eq, add_zero]
    exact lt_of_le_of_lt this (lt_of_le_of_lt (le_max_right _ _) hε)

theorem sweepFam_wideEnd_estimate_tol {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∃ tol : ℝ → ℝ,
      (∀ σ : ℝ, σ < 1 → 0 < tol σ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ σ₀ : ℝ, 1 / 2 < σ₀ ∧ σ₀ < 1 ∧ tol σ₀ < ε) ∧
      (∀ σ₀ : ℝ, σ₀ < 1 → ∀ ε₁ : ℝ, tol σ₀ < ε₁ → ∀ L : ℝ, 0 < L →
        ∃ (lam δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ),
         0 < lam ∧ lam ≤ L ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
         ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
         (∀ t : ℝ, Θ (t + LeanEval.KnotTheory.Quadrisecant.period)
           = Θ t + LeanEval.KnotTheory.Quadrisecant.period) ∧
         (∀ t : ℝ, 0 < deriv Θ t) ∧
         (∀ t : ℝ, ‖Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
         (∀ t : ℝ, ‖deriv (fun u : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
           - LeanEval.KnotTheory.Quadrisecant.velocity r (t + c)‖ < ε₁)) := by
  obtain ⟨M₀, M₁, M₂, hM₀0, hM₁0, hM₂0, hM₀, hM₁, hM₂⟩ := exists_knot_bounds hr
  obtain ⟨Cv, hCv0, hval0⟩ := wideendRawPos (r := r) (M₁ := M₁) (M₂ := M₂) hr D hM₁ hM₂
  have hval : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ ≤ 1 →
      ‖sweepLoopChamfer r D lam' σ τ - r (wideSig D lam' σ τ)‖
        ≤ Cv * (lam' * period + (period - sweepW' D σ)) ^ 2 := by
    intro lam' σ τ h1 h2 h3 h4
    exact hval0 σ lam' τ h1 h2 h4
  have hvel : ∀ (lam' σ τ : ℝ), 0 < lam' → lam' ≤ 1 / 4 → 0 < σ → σ < 1 →
      ‖chamferVel r D lam' σ τ - wideRho (sweepW' D σ) (period - sweepW' D σ) lam' (sweepParam τ) •
        velocity r (wideSig D lam' σ τ)‖
        ≤ M₂ * (1 + period) * (lam' + (period - sweepW' D σ)) *
          wideRho (sweepW' D σ) (period - sweepW' D σ) lam' (sweepParam τ) := by
    intro lam' σ τ h1 h2 h3 h4
    exact wideMatchRel hr hM₂0.le hM₂ D σ lam' τ h3 h4 h1 h2
  set C₀ : ℝ := max (3 * M₀) (25 * M₁) with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  set K : ℝ := 24 * (M₂ + 1) * (1 + period) + 36 * (Cv + 1) * C₀ + C₀ / period + 1 with hK
  have hA0 : (0 : ℝ) ≤ 24 * (M₂ + 1) * (1 + period) := by have := period_pos; nlinarith
  have hB0 : (0 : ℝ) ≤ 36 * (Cv + 1) * C₀ := by nlinarith
  have hD0 : (0 : ℝ) ≤ C₀ / period := div_nonneg hC₀0 period_pos.le
  have hKpos : 0 < K := by rw [hK]; linarith
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hKa : 24 * (M₂ + 1) * (1 + period) ≤ K := by rw [hK]; linarith
  have hKb : 36 * (Cv + 1) * C₀ ≤ K := by rw [hK]; linarith
  have hKc : C₀ / period < K := by rw [hK]; linarith
  refine ⟨fun σ => K * (period - sweepW' D σ), ?_, ?_, ?_⟩
  · -- positivity of the tolerance
    intro σ hσ
    exact mul_pos hKpos (sub_pos.mpr (sweepW'_lt_period D hσ))
  · -- the tolerance has infimum zero at `σ = 1`
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp (sweepW'_continuous D) 1 (ε / K)
      (div_pos hε hKpos)
    have hW1 : sweepW' D 1 = period := sweepW'_eq_period_of_one_le D le_rfl
    set σc : ℝ := 1 - min δ (1 / 2) / 2 with hσc
    have hmin0 : 0 < min δ (1 / 2) := lt_min hδ0 (by norm_num)
    have hminle : min δ (1 / 2) ≤ δ := min_le_left _ _
    have hminle2 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    refine ⟨σc, ?_, ?_, ?_⟩
    · rw [hσc]; linarith
    · rw [hσc]; linarith
    · have habs : dist σc 1 < δ := by
        rw [Real.dist_eq, hσc]
        have h1 : |1 - min δ (1 / 2) / 2 - 1| = min δ (1 / 2) / 2 := by
          rw [show (1 - min δ (1 / 2) / 2 - 1) = -(min δ (1 / 2) / 2) by ring, abs_neg,
            abs_of_nonneg (by positivity)]
        rw [h1]; linarith
      have hδσ : |sweepW' D σc - period| < ε / K := by
        have h := hδ σc habs
        rwa [Real.dist_eq, hW1] at h
      have hWle : sweepW' D σc ≤ period := (sweepW'_nonneg_le D σc).2
      have hdiff : period - sweepW' D σc < ε / K := by
        have h1 : period - sweepW' D σc = |sweepW' D σc - period| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith [hδσ]
      calc K * (period - sweepW' D σc) < K * (ε / K) := mul_lt_mul_of_pos_left hdiff hKpos
        _ = ε := by field_simp
  · -- the two regimes
    intro σ₀ hσ₀1 ε₁ hε₁ L hL
    simp only at hε₁
    by_cases hcase : C₀ < ε₁
    · exact crudeEstimate (M₀ := M₀) (M₁ := M₁) hr D hM₀ hM₁ σ₀ hL hcase
    · push_neg at hcase
      have hd0 : 0 < period - sweepW' D σ₀ := sub_pos.mpr (sweepW'_lt_period D hσ₀1)
      have hKd : K * (period - sweepW' D σ₀) < C₀ := lt_of_lt_of_le hε₁ hcase
      have hε₁0 : 0 < ε₁ := lt_of_lt_of_le (mul_pos hKpos hd0) hε₁.le
      have hσ₀0 : 0 < σ₀ := by
        by_contra hcon
        push_neg at hcon
        have hz : sweepW' D σ₀ = 0 := sweepW'_eq_zero_of_nonpos D hcon
        have hKp : K * period < C₀ := by
          have h := hKd; rw [hz] at h; simpa using h
        have hCk : C₀ < K * period := (div_lt_iff₀ period_pos).mp hKc
        linarith
      have hprod : K ^ 2 * (period - sweepW' D σ₀) ^ 2 < C₀ * ε₁ := by
        have hk0 : 0 < K * (period - sweepW' D σ₀) := mul_pos hKpos hd0
        have h1 : (K * (period - sweepW' D σ₀)) * (K * (period - sweepW' D σ₀)) < C₀ * ε₁ :=
          mul_lt_mul hKd hε₁.le hk0 hC₀0
        have h2 : (K * (period - sweepW' D σ₀)) * (K * (period - sweepW' D σ₀))
            = K ^ 2 * (period - sweepW' D σ₀) ^ 2 := by ring
        linarith [h1, h2]
      set lam : ℝ := min (min L (1 / 4)) ((period - sweepW' D σ₀) / period) / 2 with hlam
      have hlam0 : 0 < lam := by
        have h : 0 < min (min L (1 / 4)) ((period - sweepW' D σ₀) / period) :=
          lt_min (lt_min hL (by norm_num)) (div_pos hd0 period_pos)
        rw [hlam]; linarith
      have hlamL : lam ≤ L := by
        rw [hlam]
        have h1 : min (min L (1 / 4)) ((period - sweepW' D σ₀) / period) ≤ min L (1 / 4) :=
          min_le_left _ _
        have h2 : min L (1 / 4) ≤ L := min_le_left _ _
        linarith
      have hlam4 : lam ≤ 1 / 4 := by
        rw [hlam]
        have h1 : min (min L (1 / 4)) ((period - sweepW' D σ₀) / period) ≤ min L (1 / 4) :=
          min_le_left _ _
        have h2 : min L (1 / 4) ≤ 1 / 4 := min_le_right _ _
        linarith
      have hlamp : lam * period ≤ (period - sweepW' D σ₀) / 2 := by
        have h1 : lam ≤ ((period - sweepW' D σ₀) / period) / 2 := by
          rw [hlam]
          have := min_le_right (min L (1 / 4)) ((period - sweepW' D σ₀) / period)
          linarith
        have h2 := mul_le_mul_of_nonneg_right h1 period_pos.le
        have hpne : period ≠ 0 := ne_of_gt period_pos
        have h3 : ((period - sweepW' D σ₀) / period) / 2 * period = (period - sweepW' D σ₀) / 2 := by
          field_simp
        linarith [h2, h3]
      have hKsq : 36 * (Cv + 1) * C₀ ≤ K ^ 2 := by nlinarith [hKb, hK1]
      have hCv1 : (0 : ℝ) ≤ Cv + 1 := by linarith
      have hvalε : 16 * (Cv + 1) * (lam * period + (period - sweepW' D σ₀)) ^ 2 ≤ ε₁ := by
        have hmain : 36 * (Cv + 1) * (period - sweepW' D σ₀) ^ 2 ≤ ε₁ := by
          have hc : (0:ℝ) < 36 * (Cv + 1) := by linarith
          have h1 : 36 * (Cv + 1) * (K ^ 2 * (period - sweepW' D σ₀) ^ 2)
              < 36 * (Cv + 1) * (C₀ * ε₁) := mul_lt_mul_of_pos_left hprod hc
          have h2 : (36 * (Cv + 1) * C₀) * ε₁ ≤ K ^ 2 * ε₁ :=
            mul_le_mul_of_nonneg_right hKsq hε₁0.le
          have h3 : 36 * (Cv + 1) * (K ^ 2 * (period - sweepW' D σ₀) ^ 2)
              = K ^ 2 * (36 * (Cv + 1) * (period - sweepW' D σ₀) ^ 2) := by ring
          have h4 : 36 * (Cv + 1) * (C₀ * ε₁) = (36 * (Cv + 1) * C₀) * ε₁ := by ring
          have h5 : K ^ 2 * (36 * (Cv + 1) * (period - sweepW' D σ₀) ^ 2) < K ^ 2 * ε₁ := by
            linarith [h1, h2, h3, h4]
          have hK2 : (0:ℝ) < K ^ 2 := by positivity
          by_contra hc2
          push_neg at hc2
          nlinarith [h5, hc2, hK2]
        have hs1 : lam * period + (period - sweepW' D σ₀)
            ≤ 3 / 2 * (period - sweepW' D σ₀) := by linarith [hlamp]
        have hs2 : 0 ≤ lam * period + (period - sweepW' D σ₀) := by
          have hlp : 0 ≤ lam * period := mul_nonneg hlam0.le period_pos.le
          linarith [hd0]
        have hstep : (lam * period + (period - sweepW' D σ₀)) ^ 2
            ≤ 9 * (period - sweepW' D σ₀) ^ 2 / 4 := by nlinarith [hs1, hs2, hd0]
        have heq : 16 * (Cv + 1) * (9 * (period - sweepW' D σ₀) ^ 2 / 4)
            = 36 * (Cv + 1) * (period - sweepW' D σ₀) ^ 2 := by ring
        have h4 := mul_le_mul_of_nonneg_left hstep (by linarith : (0:ℝ) ≤ 16 * (Cv + 1))
        linarith [h4, heq, hmain]
      have hvelε : 16 * (M₂ + 1) * (1 + period) * (lam + (period - sweepW' D σ₀)) ≤ ε₁ := by
        have hpos : (0:ℝ) ≤ 16 * (M₂ + 1) * (1 + period) := by
          have := period_pos; nlinarith
        have hp1 : (1:ℝ) ≤ period := by rw [period]; linarith [Real.pi_gt_three]
        have hl : lam ≤ lam * period := by nlinarith [hlam0, hp1]
        have h1 : lam + (period - sweepW' D σ₀) ≤ 3 * (period - sweepW' D σ₀) / 2 := by
          linarith [hl, hlamp]
        have h3 : 16 * (M₂ + 1) * (1 + period) * (3 * (period - sweepW' D σ₀) / 2)
            = 24 * (M₂ + 1) * (1 + period) * (period - sweepW' D σ₀) := by ring
        have h2 : 24 * (M₂ + 1) * (1 + period) * (period - sweepW' D σ₀)
            ≤ K * (period - sweepW' D σ₀) := by nlinarith [hKa, hd0]
        have h4 := mul_le_mul_of_nonneg_left h1 hpos
        linarith [h4, h3, h2, hKd]
      have hphase : ∃ (δ₁ δ₂ : ℝ) (ψ : ℝ → ℝ),
          0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
          (∀ t : ℝ, ψ (t + period) = ψ t + period) ∧
          (∀ t : ℝ, 0 < deriv ψ t) ∧
          (∀ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ₀ t - r (ψ t)‖ ≤ ε₁ / 2) ∧
          (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) t
            - deriv ψ t • velocity r (ψ t)‖ ≤ (ε₁ / 2) * deriv ψ t) :=
        widePhaseForm hr D hM₁ hM₂0.le hM₂ hCv0.le hσ₀0 hσ₀1 (wideSig_tau_lipschitz D)
          (wideSig_sigma_modulus D σ₀) hval hvel hε₁0 hL hlam0 hlamL hlam4 hvalε hvelε
      obtain ⟨δ₁, δ₂, ψ, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hψsm, hψsh, hψpos, hψ1, hψ2⟩ := hphase
      obtain ⟨Θ, hΘsm, hΘsh, hΘpos, hΘ1, hΘ2⟩ :=
        reparamOfPhase (r := r) (Φ := fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u)
          hψsm hψsh hψpos hε₁0
          ((sweepFam_contDiff_periodic hr.continuous D lam δ₁ δ₂ (ne_of_gt hδ₁0)
            (ne_of_gt hδ₂0)).2.2 σ₀) hψ1 hψ2
      exact ⟨lam, δ₁, δ₂, 0, Θ, hlam0, hlamL, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hΘsm, hΘsh, hΘpos,
        fun t => by simpa using hΘ1 t, fun t => by simpa using hΘ2 t⟩

end Work.Drive
