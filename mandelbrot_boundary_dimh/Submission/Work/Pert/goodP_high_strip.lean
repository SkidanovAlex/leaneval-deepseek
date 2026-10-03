import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.cover_half_centered
import Submission.Work.Interfaces.FatouNarrow

/-!
# PERT · `Work.Pert.goodP_high_strip`

The far half-strip `{|Re w| ≤ 1, Y₀ ≤ |Im w|}` lies in `Φ '' (Qm ξ₁ α)`; hence it is in the
maximal domain at **level 0**: `GoodP f Df τ Φ (Qm ξ₁ α) w`.

The hypotheses control the Fatou coordinate `Φ` of `F` by

* `hder` : `‖Φ' - 1‖ ≤ C₂ / R` on every ball of radius `R ≥ R₁` inside the gate;
* `hdev` : `‖Φ (-1 + iY) - (-1 + iY)‖ ≤ K + C₂ (2 log (|Y| + 3) + 2)` for `|Y| ≥ ξ₁ + 3R₁ + 2`.

With `A := K + C₂ (2 log (Y₀ + 3) + 2)`, `hY₀big` reads `4A + 4R₁ + 8 ≤ Y₀ - ξ₁`.  Writing
`y := |Im w| ≥ Y₀`:

1. `hdev` at the threshold height gives `A ≥ 2 C₂ log ((Y₀+3)/(ξ₁+3R₁+5))` (the norm is `≥ 0`),
   whence `8 C₂ log ((y+3)/(Y₀+3)) ≤ y - Y₀` (`log_gain`): the logarithmic growth of the
   deviation is beaten by the linear growth of the height.
2. The mean value inequality on the segment from the anchor `a = -1 + i Im w` (where `hdev`
   applies) to `w` gives `‖Φ w - w‖ ≤ A + 1`.
3. Hence `4 (A + 1) + 2 max R₁ (2C₂) + 1 < y - ξ₁`, which produces a radius `R` with
   `ball w R ⊆ Qm ξ₁ α`, `‖Φ' - 1‖ ≤ 1/2` on that ball and `‖Φ w - w‖ < R/2`.
4. `Work.Pert.cover_half_centered` (Rouché + mean value inequality) then gives `ζ ∈ ball w R`
   with `Φ ζ = w`, and `ball w R ⊆ Qm ξ₁ α`.
-/

namespace Work.Pert

open MandelDim Complex Set Metric
open scoped Topology

noncomputable section

/-- The gate `Qm ξ₁ α` is open. -/
theorem isOpen_Qm' (ξ₁ : ℝ) (α : ℂ) : IsOpen (Qm ξ₁ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Qm ξ₁ α =
      {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} := by
    ext z
    simp [Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **Sharp disc criterion for the gate.**  If `|Im (1/α)| ≤ Re (1/α)` then the closed disc of
radius `r` around `c` lies in `Qm ξ₁ α` as soon as `2 r + |Re c| + ξ₁ < |Im c|`. -/
lemma closedBall_subset_Qm_of_lt {ξ₁ : ℝ} {α : ℂ} (hαim : |(1 / α).im| ≤ (1 / α).re)
    {c : ℂ} {r : ℝ} (h : 2 * r + |c.re| + ξ₁ < |c.im|) :
    Metric.closedBall c r ⊆ Qm ξ₁ α := by
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_eq_norm] at hζ
  have hre : |ζ.re - c.re| ≤ r := by
    have h1 := Complex.abs_re_le_norm (ζ - c)
    rw [Complex.sub_re] at h1
    exact le_trans h1 hζ
  have him : |ζ.im - c.im| ≤ r := by
    have h1 := Complex.abs_im_le_norm (ζ - c)
    rw [Complex.sub_im] at h1
    exact le_trans h1 hζ
  have hzre_le : ζ.re ≤ |c.re| + r := by
    have h1 : ζ.re - c.re ≤ r := (abs_le.mp hre).2
    linarith [le_abs_self c.re]
  have hzre_ge : -(|c.re| + r) ≤ ζ.re := by
    have h1 : -r ≤ ζ.re - c.re := (abs_le.mp hre).1
    linarith [neg_abs_le c.re]
  have hzim : |c.im| - r ≤ |ζ.im| := by
    have h2 : |c.im| - |ζ.im| ≤ |c.im - ζ.im| := abs_sub_abs_le_abs_sub c.im ζ.im
    have h3 : |c.im - ζ.im| ≤ r := by rw [abs_sub_comm]; exact him
    linarith
  have hQm : ζ ∈ Qm ξ₁ α ↔
      (-|(ζ - ((ξ₁ : ℂ) - 1 / α)).im| < (ζ - ((ξ₁ : ℂ) - 1 / α)).re ∧
        (ζ - (-(ξ₁ : ℂ))).re < |(ζ - (-(ξ₁ : ℂ))).im|) := by
    simp [Qm, MandelDim.Qreg]
  rw [hQm]
  constructor
  · have h4 : (ζ - ((ξ₁ : ℂ) - 1 / α)).re = ζ.re - ξ₁ + (1 / α).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; ring
    have h5 : (ζ - ((ξ₁ : ℂ) - 1 / α)).im = ζ.im + (1 / α).im := by
      simp only [Complex.sub_im, Complex.ofReal_im]; ring
    have h6 : |ζ.im + (1 / α).im| ≥ |ζ.im| - |(1 / α).im| := by
      have hh := abs_sub_abs_le_abs_sub ζ.im (-(1 / α).im)
      simpa using hh
    rw [h4, h5]
    linarith
  · have h7 : (ζ - (-(ξ₁ : ℂ))).re = ζ.re + ξ₁ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
    have h8 : (ζ - (-(ξ₁ : ℂ))).im = ζ.im := by
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; ring
    rw [h7, h8]
    linarith

/-- **The logarithmic gain.**  If `A ≥ 2 C₂ log ((Y₀+3)/(ξ₁+3R₁+5))` (which follows from the
deviation control at the threshold height `ξ₁ + 3R₁ + 2`, since the deviation is `≥ 0`) and
`4A + 4R₁ + 8 ≤ Y₀ - ξ₁`, then for `y ≥ Y₀`
`8 C₂ log ((y+3)/(Y₀+3)) ≤ y - Y₀`. -/
lemma log_gain {C₂ R₁ ξ₁ A Y₀ y : ℝ}
    (hC₂ : 0 ≤ C₂) (hR₁ : 0 < R₁) (hξ : 0 < ξ₁) (hA0 : 0 ≤ A)
    (hA : 2 * C₂ * Real.log ((Y₀ + 3) / (ξ₁ + 3 * R₁ + 5)) ≤ A)
    (hγbig : 4 * A + 4 * R₁ + 8 ≤ Y₀ - ξ₁)
    (hY : Y₀ ≤ y) :
    8 * C₂ * Real.log ((y + 3) / (Y₀ + 3)) ≤ y - Y₀ := by
  set w' : ℝ := ξ₁ + 3 * R₁ + 5 with hw'
  set u₀ : ℝ := Y₀ + 3 with hu₀
  set τ : ℝ := y - Y₀ with hτ
  have hw'pos : 0 < w' := by rw [hw']; linarith
  have hu₀pos : 0 < u₀ := by rw [hu₀]; linarith
  have hw'lt : w' < u₀ := by rw [hu₀, hw']; linarith
  have hΨpos : 0 < Real.log (u₀ / w') := by
    apply Real.log_pos; rw [one_lt_div hw'pos]; exact hw'lt
  have hΨne : Real.log (u₀ / w') ≠ 0 := ne_of_gt hΨpos
  have hA' : 2 * C₂ * Real.log (u₀ / w') ≤ A := by rw [hu₀, hw']; exact hA
  have h8 : 8 * C₂ * Real.log (u₀ / w') ≤ Y₀ - ξ₁ - 4 * R₁ - 8 := by
    have h0 : 4 * (2 * C₂ * Real.log (u₀ / w')) ≤ 4 * A := by linarith
    linarith
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hlog1 : Real.log ((y + 3) / (Y₀ + 3)) ≤ τ / u₀ := by
    have h1 : (y + 3) / (Y₀ + 3) = 1 + τ / u₀ := by
      have hden : (Y₀ + 3) = u₀ := hu₀.symm
      rw [hden, show y + 3 = u₀ + τ by rw [hτ, hu₀]; ring, add_div,
        div_self (ne_of_gt hu₀pos)]
    rw [h1]
    have h2 : 0 < 1 + τ / u₀ := by
      have h3 : 0 ≤ τ / u₀ := div_nonneg hτ0 hu₀pos.le
      linarith
    have h3 := Real.log_le_sub_one_of_pos h2
    linarith
  have hratio : (Y₀ - ξ₁ - 4 * R₁ - 8) / u₀ ≤ Real.log (u₀ / w') := by
    have h1 : (Y₀ - ξ₁ - 4 * R₁ - 8) / u₀ = 1 - (ξ₁ + 4 * R₁ + 11) / u₀ := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (ne_of_gt hu₀pos), hu₀]
      ring
    have h2 : 1 - (ξ₁ + 4 * R₁ + 11) / u₀ ≤ 1 - w' / u₀ := by
      have h3 : w' ≤ ξ₁ + 4 * R₁ + 11 := by rw [hw']; linarith
      have h4 : w' / u₀ ≤ (ξ₁ + 4 * R₁ + 11) / u₀ :=
        div_le_div_of_nonneg_right h3 hu₀pos.le
      linarith
    have h5 : 1 - w' / u₀ ≤ Real.log (u₀ / w') := by
      have hq : 0 < w' / u₀ := div_pos hw'pos hu₀pos
      have h6 : Real.log (w' / u₀) ≤ w' / u₀ - 1 := Real.log_le_sub_one_of_pos hq
      have h7 : Real.log (u₀ / w') = - Real.log (w' / u₀) := by
        rw [← Real.log_inv, inv_div]
      rw [h7]; linarith
    linarith
  have hmain : 8 * C₂ * Real.log ((y + 3) / (Y₀ + 3)) ≤ τ := by
    have hstep1 : 8 * C₂ * Real.log ((y + 3) / (Y₀ + 3)) ≤ 8 * C₂ * (τ / u₀) :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have hstep2 : 8 * C₂ * (τ / u₀)
        = (8 * C₂ * Real.log (u₀ / w')) * (τ / u₀) / Real.log (u₀ / w') := by
      field_simp
    have hstep3 : (8 * C₂ * Real.log (u₀ / w')) * (τ / u₀) / Real.log (u₀ / w')
        ≤ (Y₀ - ξ₁ - 4 * R₁ - 8) * (τ / u₀) / Real.log (u₀ / w') := by
      apply div_le_div_of_nonneg_right _ hΨpos.le
      exact mul_le_mul_of_nonneg_right h8 (div_nonneg hτ0 hu₀pos.le)
    have hstep4 : (Y₀ - ξ₁ - 4 * R₁ - 8) * (τ / u₀) / Real.log (u₀ / w')
        = ((Y₀ - ξ₁ - 4 * R₁ - 8) / u₀) * τ / Real.log (u₀ / w') := by
      ring
    have hstep5 : ((Y₀ - ξ₁ - 4 * R₁ - 8) / u₀) * τ / Real.log (u₀ / w')
        ≤ Real.log (u₀ / w') * τ / Real.log (u₀ / w') := by
      apply div_le_div_of_nonneg_right _ hΨpos.le
      exact mul_le_mul_of_nonneg_right hratio hτ0
    have hstep6 : Real.log (u₀ / w') * τ / Real.log (u₀ / w') = τ := by
      field_simp
    linarith [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6]
  rw [hτ] at hmain
  exact hmain

theorem goodP_high_strip {f F τ Φ : ℂ → ℂ} {α : ℂ} {Df L : Set ℂ}
    {rr ξ₁ M K C₂ R₁ Y₀ : ℝ}
    (hM : 8 ≤ M) (hR₁ : 0 < R₁) (hMR₁ : 16 * R₁ ≤ M) (hξ : 0 < ξ₁) (hξM : ξ₁ < M)
    (hα : 5 * M / 4 + 2 + ξ₁ < (1 / α).re)
    (hαim : |(1 / α).im| ≤ (1 / α).re)
    (hC₂R₁ : C₂ ≤ R₁)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm ξ₁ α))
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₁ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm ξ₁ α →
      ‖deriv Φ z - 1‖ ≤ C₂ / R)
    (hdev : ∀ Y : ℝ, ξ₁ + 3 * R₁ + 2 ≤ |Y| →
      ‖Φ (((-1 : ℝ) : ℂ) + (Y : ℂ) * Complex.I) - (((-1 : ℝ) : ℂ) + (Y : ℂ) * Complex.I)‖
        ≤ K + C₂ * (2 * Real.log (|Y| + 3) + 2))
    (hY₀ : ξ₁ + 3 * R₁ + 2 ≤ Y₀)
    (hY₀big : 4 * (K + C₂ * (2 * Real.log (Y₀ + 3) + 2)) + 4 * R₁ + 8 ≤ Y₀ - ξ₁)
    (hAbel : ∀ z ∈ Work.Pert.Qm ξ₁ α, f (τ z) = τ (F z))
    (hτQ : ∀ z ∈ Work.Pert.Qm ξ₁ α, τ z ∈ Metric.closedBall (0 : ℂ) rr)
    (hLrr : Metric.closedBall (0 : ℂ) rr ⊆ L) (hLDf : L ⊆ Df)
    {w : ℂ} (hre : |w.re| ≤ 1) (him : Y₀ ≤ |w.im|) :
    Work.Pert.GoodP f Df τ Φ (Work.Pert.Qm ξ₁ α) w := by
  have hQopen : IsOpen (Qm ξ₁ α) := isOpen_Qm' ξ₁ α
  have hballQ : ∀ {c : ℂ} {r : ℝ}, 2 * r + |c.re| + ξ₁ < |c.im| →
      Metric.closedBall c r ⊆ Qm ξ₁ α := fun h => closedBall_subset_Qm_of_lt hαim h
  -- ## 0.  `C₂ ≥ 0`, from `hder` at a point where the gate contains a disc of radius `R₁`
  have hY₀pos : 0 < Y₀ := by linarith
  have hC₂ : 0 ≤ C₂ := by
    have hd := hder (((-1 : ℝ) : ℂ) + (Y₀ : ℂ) * Complex.I) R₁ le_rfl (by
      refine fun ζ hζ => hballQ ?_ (Metric.ball_subset_closedBall hζ)
      have h1 : (((-1 : ℝ) : ℂ) + (Y₀ : ℂ) * Complex.I).re = -1 := by simp
      have h2 : (((-1 : ℝ) : ℂ) + (Y₀ : ℂ) * Complex.I).im = Y₀ := by simp
      rw [h1, h2, abs_neg, abs_one, abs_of_pos hY₀pos]
      linarith)
    have h0 : 0 ≤ C₂ / R₁ := le_trans (norm_nonneg _) hd
    rcases div_nonneg_iff.mp h0 with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 (not_le.mpr hR₁)
  -- ## 1.  the constant `A`, its positivity and its lower bound
  set A : ℝ := K + C₂ * (2 * Real.log (Y₀ + 3) + 2) with hAdef
  have hbig : 4 * A + 4 * R₁ + 8 ≤ Y₀ - ξ₁ := hY₀big
  have hA0 : 0 ≤ A := by
    have h5 := hdev (ξ₁ + 3 * R₁ + 2) (by rw [abs_of_nonneg (by linarith)])
    have h6 : |ξ₁ + 3 * R₁ + 2| + 3 = ξ₁ + 3 * R₁ + 5 := by
      rw [abs_of_nonneg (by linarith)]
      ring
    have h7 : 0 ≤ K + C₂ * (2 * Real.log (ξ₁ + 3 * R₁ + 5) + 2) := by
      have h8 := le_trans (norm_nonneg _) h5
      rwa [h6] at h8
    have h9 : Real.log (ξ₁ + 3 * R₁ + 5) ≤ Real.log (Y₀ + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h10 : C₂ * (2 * Real.log (ξ₁ + 3 * R₁ + 5) + 2) ≤
        C₂ * (2 * Real.log (Y₀ + 3) + 2) := by
      apply mul_le_mul_of_nonneg_left _ hC₂
      linarith
    rw [hAdef]
    linarith
  have hA_lb : 2 * C₂ * Real.log ((Y₀ + 3) / (ξ₁ + 3 * R₁ + 5)) ≤ A := by
    have hK : -(C₂ * (2 * Real.log (ξ₁ + 3 * R₁ + 5) + 2)) ≤ K := by
      have h5 := hdev (ξ₁ + 3 * R₁ + 2) (by rw [abs_of_nonneg (by linarith)])
      have h6 : |ξ₁ + 3 * R₁ + 2| + 3 = ξ₁ + 3 * R₁ + 5 := by
        rw [abs_of_nonneg (by linarith)]
        ring
      have h7 : 0 ≤ K + C₂ * (2 * Real.log (ξ₁ + 3 * R₁ + 5) + 2) := by
        have h8 := le_trans (norm_nonneg _) h5
        rwa [h6] at h8
      linarith
    have hlog : Real.log ((Y₀ + 3) / (ξ₁ + 3 * R₁ + 5)) =
        Real.log (Y₀ + 3) - Real.log (ξ₁ + 3 * R₁ + 5) :=
      Real.log_div (by linarith) (by linarith)
    rw [hlog, hAdef]
    nlinarith [hK]
  have hΨpos : 0 < Real.log ((Y₀ + 3) / (ξ₁ + 3 * R₁ + 5)) := by
    apply Real.log_pos
    rw [one_lt_div (by linarith)]
    linarith
  -- ## 2.  the height `y = |Im w|` and the main arithmetic
  set y : ℝ := |w.im| with hy
  have hyY : Y₀ ≤ y := by rw [hy]; exact him
  have hy5 : ξ₁ + 3 * R₁ + 2 ≤ y := le_trans hY₀ hyY
  have hyγ : 4 * R₁ + 8 ≤ y - ξ₁ := by
    have h1 : 4 * R₁ + 8 ≤ Y₀ - ξ₁ := by linarith
    linarith
  have hSmain : 4 * (K + C₂ * (2 * Real.log (y + 3) + 2) + 1) + 2 * max R₁ (2 * C₂) + 3
      < y - ξ₁ := by
    have hlog := log_gain hC₂ hR₁ hξ hA0 hA_lb hbig hyY
    have hAy : K + C₂ * (2 * Real.log (y + 3) + 2) =
        A + 2 * C₂ * Real.log ((y + 3) / (Y₀ + 3)) := by
      have hlog2 : Real.log ((y + 3) / (Y₀ + 3)) = Real.log (y + 3) - Real.log (Y₀ + 3) :=
        Real.log_div (by linarith) (by linarith)
      rw [hlog2, hAdef]
      ring
    have hmax : 2 * max R₁ (2 * C₂) ≤ 4 * R₁ := by
      have h1 : max R₁ (2 * C₂) ≤ 2 * R₁ := max_le (by linarith) (by linarith)
      linarith
    nlinarith [hlog, hAy, hmax, hbig]
  -- ## 3.  the anchor, the segment and the deviation bound at `w`
  set a : ℂ := ((-1 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I with ha
  have hdev_a : ‖Φ a - a‖ ≤ K + C₂ * (2 * Real.log (y + 3) + 2) := by
    have h1 := hdev w.im (by rw [← hy]; exact hy5)
    rwa [← ha, ← hy] at h1
  have hseg : ∀ p ∈ segment ℝ w a, |p.re| ≤ 1 ∧ p.im = w.im := by
    intro p hp
    rw [segment_eq_image ℝ w a] at hp
    obtain ⟨θ, hθ, rfl⟩ := hp
    obtain ⟨hθ0, hθ1⟩ := hθ
    constructor
    · have h1 : ((1 - θ) • w + θ • a).re = (1 - θ) * w.re + θ * (-1) := by
        simp [ha, Complex.add_re, Complex.mul_re]
      rw [h1]
      have h2 : |(1 - θ) * w.re| ≤ (1 - θ) := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
        nlinarith [abs_le.mp hre]
      have h3 : |θ * (-1)| ≤ θ := by
        rw [abs_mul, abs_neg, abs_one, mul_one, abs_of_nonneg hθ0]
      calc |(1 - θ) * w.re + θ * (-1)| ≤ |(1 - θ) * w.re| + |θ * (-1)| := abs_add_le _ _
        _ ≤ (1 - θ) + θ := add_le_add h2 h3
        _ = 1 := by ring
    · have h1 : ((1 - θ) • w + θ • a).im = (1 - θ) * w.im + θ * w.im := by
        simp [ha, Complex.add_im, Complex.mul_im]
      rw [h1]
      ring
  have htrans : ‖Φ w - w‖ ≤ K + C₂ * (2 * Real.log (y + 3) + 2) + 1 := by
    set ρ : ℝ := (y - ξ₁ - 2) / 2 with hρ
    have hρpos : 0 < ρ := by rw [hρ]; linarith
    have hρR₁ : R₁ ≤ ρ := by rw [hρ]; linarith
    have hsegQ : ∀ p ∈ segment ℝ w a, Metric.ball p ρ ⊆ Qm ξ₁ α := by
      intro p hp
      refine fun u hu => hballQ ?_ (Metric.ball_subset_closedBall hu)
      obtain ⟨hp1, hp2⟩ := hseg p hp
      rw [hp2, hρ]
      have h2 : 2 * ((y - ξ₁ - 2) / 2) = y - ξ₁ - 2 := by ring
      rw [h2]
      linarith
    have hdiff' : ∀ x ∈ segment ℝ w a, DifferentiableAt ℂ (fun u : ℂ => Φ u - u) x := by
      intro x hx
      have hxQ : x ∈ Qm ξ₁ α := hsegQ x hx (Metric.mem_ball_self hρpos)
      exact (hΦ.1.differentiableAt (hQopen.mem_nhds hxQ)).sub differentiableAt_id
    have hbound' : ∀ x ∈ segment ℝ w a, ‖deriv (fun u : ℂ => Φ u - u) x‖ ≤ C₂ / ρ := by
      intro x hx
      have hxQ : x ∈ Qm ξ₁ α := hsegQ x hx (Metric.mem_ball_self hρpos)
      have h1 : deriv (fun u : ℂ => Φ u - u) x = deriv Φ x - 1 := by
        rw [show (fun u : ℂ => Φ u - u) = Φ - id from rfl,
          deriv_sub (hΦ.1.differentiableAt (hQopen.mem_nhds hxQ)) differentiableAt_id,
          deriv_id]
      rw [h1]
      exact hder x ρ hρR₁ (hsegQ x hx)
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff' hbound'
      (convex_segment w a) (left_mem_segment ℝ w a) (right_mem_segment ℝ w a)
    have hfa : (fun u : ℂ => Φ u - u) a - (fun u : ℂ => Φ u - u) w
        = (Φ a - a) - (Φ w - w) := by ring
    rw [hfa] at hmvt
    have haw : ‖a - w‖ ≤ 2 := by
      have h1 : a - w = (((-1 - w.re : ℝ)) : ℂ) := by
        rw [ha]
        apply Complex.ext <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le] at hre ⊢
      constructor <;> linarith
    have hδ : C₂ / ρ * ‖a - w‖ ≤ 1 := by
      have h1 : C₂ / ρ * ‖a - w‖ ≤ C₂ / ρ * 2 :=
        mul_le_mul_of_nonneg_left haw (div_nonneg hC₂ hρpos.le)
      have h2 : C₂ / ρ * 2 = 2 * C₂ / ρ := by ring
      rw [h2] at h1
      have h3 : 2 * C₂ / ρ ≤ 1 := by
        rw [div_le_one hρpos]
        rw [hρ] at *
        linarith
      linarith
    have htri : ‖Φ w - w‖ ≤ ‖Φ a - a‖ + ‖(Φ w - w) - (Φ a - a)‖ := by
      have he : Φ w - w = (Φ a - a) + ((Φ w - w) - (Φ a - a)) := by ring
      calc ‖Φ w - w‖ = ‖(Φ a - a) + ((Φ w - w) - (Φ a - a))‖ := congrArg norm he
        _ ≤ ‖Φ a - a‖ + ‖(Φ w - w) - (Φ a - a)‖ := norm_add_le _ _
    have h4 : ‖(Φ w - w) - (Φ a - a)‖ ≤ 1 := by
      have := hmvt
      rw [norm_sub_rev] at this
      linarith
    linarith [hdev_a, htri, h4]
  -- ## 4.  the covering radius and the Rouché covering
  have hAy0 : 0 ≤ K + C₂ * (2 * Real.log (y + 3) + 2) := by
    have h1 : Real.log (Y₀ + 3) ≤ Real.log (y + 3) := Real.log_le_log (by linarith) (by linarith)
    have h2 : C₂ * (2 * Real.log (Y₀ + 3) + 2) ≤ C₂ * (2 * Real.log (y + 3) + 2) := by
      apply mul_le_mul_of_nonneg_left _ hC₂
      linarith
    have h3 : K + C₂ * (2 * Real.log (Y₀ + 3) + 2) = A := hAdef.symm
    linarith
  set S : ℝ := K + C₂ * (2 * Real.log (y + 3) + 2) + 1 with hSdef
  have hSpos : 1 ≤ S := by rw [hSdef]; linarith
  have hSkey : 4 * S + 2 * max R₁ (2 * C₂) + 3 < y - ξ₁ := by rw [hSdef]; exact hSmain
  set Rm : ℝ := (y - ξ₁ - 2 * max R₁ (2 * C₂) - 2) / 2 with hRm
  have h2S : 2 * S < Rm := by rw [hRm]; linarith
  set R : ℝ := (Rm + 2 * S) / 2 with hRdef
  have hRgt : 2 * S < R := by rw [hRdef]; linarith
  have hRle : R ≤ Rm := by rw [hRdef]; linarith
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith : 0 < 2 * S) (le_of_lt hRgt)
  have h2R : 2 * R + 2 * max R₁ (2 * C₂) + 2 ≤ y - ξ₁ := by
    have h3 : 2 * R ≤ 2 * Rm := by linarith
    rw [hRm] at h3
    linarith
  have hR'max : 0 ≤ 2 * max R₁ (2 * C₂) := by
    have := le_max_left R₁ (2 * C₂)
    linarith
  have hclosed : Metric.closedBall w R ⊆ Qm ξ₁ α := by
    refine fun ζ hζ => hballQ ?_ hζ
    rw [← hy]
    have h6 : 2 * R ≤ y - ξ₁ - 2 := by linarith
    linarith [abs_le.mp hre]
  have hdiff : ∀ ζ ∈ Metric.closedBall w R, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt (hQopen.mem_nhds (hclosed hζ))
  have hderiv : ∀ ζ ∈ Metric.closedBall w R, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    have hb : Metric.ball ζ (max R₁ (2 * C₂)) ⊆ Qm ξ₁ α := by
      refine fun u hu => hballQ ?_ (Metric.ball_subset_closedBall hu)
      have h1 : |ζ.re - w.re| ≤ R := by
        have h1 := Complex.abs_re_le_norm (ζ - w)
        rw [Complex.sub_re] at h1
        rw [Metric.mem_closedBall, dist_eq_norm] at hζ
        exact le_trans h1 hζ
      have h2 : |ζ.im - w.im| ≤ R := by
        have h1 := Complex.abs_im_le_norm (ζ - w)
        rw [Complex.sub_im] at h1
        rw [Metric.mem_closedBall, dist_eq_norm] at hζ
        exact le_trans h1 hζ
      have h3 : |ζ.re| ≤ 1 + R := by
        have h4 : |ζ.re| ≤ |ζ.re - w.re| + |w.re| := by
          have he : ζ.re = (ζ.re - w.re) + w.re := by ring
          calc |ζ.re| = |(ζ.re - w.re) + w.re| := congrArg abs he
            _ ≤ |ζ.re - w.re| + |w.re| := abs_add_le _ _
        linarith [abs_le.mp hre]
      have h5 : y - R ≤ |ζ.im| := by
        have h6 : |w.im| - |ζ.im| ≤ |ζ.im - w.im| := by
          have h := abs_sub_abs_le_abs_sub w.im ζ.im
          rwa [abs_sub_comm w.im ζ.im] at h
        rw [hy]
        linarith
      linarith [h2R, h1, h3, h5]
    have hC2R' : C₂ / (max R₁ (2 * C₂)) ≤ 1 / 2 := by
      have hpos : 0 < max R₁ (2 * C₂) := lt_of_lt_of_le hR₁ (le_max_left _ _)
      rw [div_le_iff₀ hpos]
      have h2 : 2 * C₂ ≤ max R₁ (2 * C₂) := le_max_right _ _
      linarith
    calc ‖deriv Φ ζ - 1‖ ≤ C₂ / (max R₁ (2 * C₂)) :=
          hder ζ (max R₁ (2 * C₂)) (le_max_left _ _) hb
      _ ≤ 1 / 2 := hC2R'
  have hcover := cover_half_centered (Φ := Φ) (z₀ := w) (r := R) hRpos hdiff hderiv
  have hwmem : w ∈ Metric.ball (Φ w) (R / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    rw [hSdef] at htrans
    linarith
  obtain ⟨ζ, hζ, hζΦ⟩ := hcover hwmem
  exact ⟨0, ⟨ζ, hclosed hζ, by simp [hζΦ]⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

end

end Work.Pert
