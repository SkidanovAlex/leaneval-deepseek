import Mathlib
import Submission.Work.FatouL1.wideStripDefs
import Submission.Work.FatouL1.ballSubsetQreg
import Submission.Work.FatouWindow.fatouDerivSetup
import Submission.Work.FatouCH.fatouDerivEstimate
import Submission.Work.FatouWindow.ExistsClean
import Submission.Work.Fatou.Qreg.InjGeom

/-!
# FATOU-L1: `Φ'` is bounded on the strip `{x₀ - 1 < Re z < x₀ + 3}`

For a near-translation `F` on Shishikura's region `Q = Qreg b₁ b₂` (`‖F z - (z+1)‖ ≤ 1/32`,
`‖F' z - 1‖ ≤ 1/32`) with `L¹` derivative defect (`NearTranslationL1`) and a vertical line
`x₀` with `b₁.re + 1 < x₀`, `x₀ + 3 < b₂.re`, the derivative of any Fatou coordinate `Φ` of `F`
on `Q` is **bounded** on the strip `x₀ - 1 < Re z < x₀ + 3`.

Two facts are combined.

* **Far away** (`|Im z|` large): `Q` contains a ball of radius `R₁` around `z` because the two
  cones defining `Q` open up at speed `|Im|` (`Work.FatouL1.ballSubsetQreg`).  Lemma A.2.4(i) of
  Shishikura (`MandelDim.FatouDerivEstimate`, proved in `Work.FatouCH.fatouDerivEstimate`) then
  gives `‖Φ' z - 1/(F z - z)‖ ≤ C₂/R₁`, and `‖1/(F z - z)‖ ≤ 32/31` since
  `‖(F z - z) - 1‖ ≤ 1/32`.  (In fact the whole proof uses only `NearTranslationOn`, not the
  `L¹` line-integral bound of `NearTranslationL1`; the statement keeps the narrower hypothesis
  because that is the form in which the consumers feed it in.)
* **Near the axis** (`|Im z| ≤ T`): the part of the strip with `|Im| ≤ T` is compact and is
  contained in the open set `Q`, where `Φ` is holomorphic; hence `deriv Φ` is continuous there
  and bounded by compactness.

The unbounded directions of `Q` are thus the only ones that matter, and they are controlled by
A.2.4(i).  No effectiveness in the constants is claimed (and none is available: `R₁ = 100`).
-/

namespace Work.FatouWindow

open Work.FatouL1

open Set Metric
open scoped _root_.Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-! ## The derivative bound -/

/-- **`Φ'` is bounded on the strip `(x₀-1, x₀+3)`** for every Fatou coordinate `Φ` of a
near-translation `F` on `Qreg b₁ b₂`. -/
theorem deriv_bounded_of_isFatouCoordOn {Φ : ℂ → ℂ}
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∃ B : ℝ, ∀ z : ℂ, x₀ - 1 < z.re → z.re < x₀ + 3 → ‖deriv Φ z‖ ≤ B := by
  obtain ⟨R₁, C₁, C₂, hR₁, hC₁, hC₂, hEst⟩ := Work.FatouCH.fatouDerivEstimate
  obtain ⟨K, hK0, hKball⟩ := ballSubsetQreg (b₁ := b₁) (b₂ := b₂) (x₀ := x₀) h₁ h₂
  set T : ℝ := 2 * R₁ + K with hT
  -- ### Far away: A.2.4(i) on a ball of radius `R₁`
  have hfar : ∀ z : ℂ, x₀ - 1 < z.re → z.re < x₀ + 3 → T ≤ |z.im| →
      ‖deriv Φ z‖ ≤ C₂ / R₁ + 32 / 31 := by
    intro z hz1 hz2 hzim
    have hball : Metric.ball z R₁ ⊆ MandelDim.Qreg b₁ b₂ :=
      hKball z hz1 hz2 R₁ (by rw [← hT]; exact hzim)
    have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := hball (Metric.mem_ball_self hR₁)
    have hΦd : DifferentiableOn ℂ Φ (Metric.ball z R₁) := hΦ.1.mono hball
    have hinj : Set.InjOn Φ (Metric.ball z R₁) := hΦ.2.1.mono hball
    have hv : DifferentiableOn ℂ (fun w : ℂ => F w - w) (Metric.ball z R₁) :=
      (hF.1.1.mono hball).sub (differentiableOn_id)
    have hv1 : ∀ w ∈ Metric.ball z R₁, ‖(F w - w) - 1‖ < 1 / 4 := by
      intro w hw
      have h1 : ‖F w - (w + 1)‖ ≤ 1 / 32 := (hF.1.2 w (hball hw)).1
      have heq : F w - (w + 1) = (F w - w) - 1 := by ring
      rw [heq] at h1
      linarith
    have hAbel : ∀ w ∈ Metric.ball z R₁, w + (F w - w) ∈ Metric.ball z R₁ →
        Φ (w + (F w - w)) = Φ w + 1 := by
      intro w hw hw'
      have hwQ : w ∈ MandelDim.Qreg b₁ b₂ := hball hw
      have hFwQ : F w ∈ MandelDim.Qreg b₁ b₂ := by
        rw [show w + (F w - w) = F w from by ring] at hw'
        exact hball hw'
      rw [show w + (F w - w) = F w from by ring]
      exact hΦ.2.2 w hwQ hFwQ
    have hmain := (hEst Φ (fun w : ℂ => F w - w) z R₁ le_rfl hΦd hinj hv hv1 hAbel).2
    have hvz : ‖1 / (F z - z)‖ ≤ 32 / 31 := by
      have h1 : ‖F z - (z + 1)‖ ≤ 1 / 32 := (hF.1.2 z hzQ).1
      have heq : F z - (z + 1) = (F z - z) - 1 := by ring
      rw [heq] at h1
      have hnorm : (31 / 32 : ℝ) ≤ ‖F z - z‖ := by
        have h2 := (abs_le.mp (abs_norm_sub_norm_le (F z - z) (1 : ℂ))).1
        rw [norm_one] at h2
        linarith
      rw [norm_div, norm_one, one_div]
      have hle : ‖F z - z‖⁻¹ ≤ ((31 : ℝ) / 32)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hnorm
      rwa [show ((31 : ℝ) / 32)⁻¹ = 32 / 31 by norm_num] at hle
    have hsplit : deriv Φ z = (deriv Φ z - 1 / (F z - z)) + 1 / (F z - z) := by ring
    calc ‖deriv Φ z‖ = ‖(deriv Φ z - 1 / (F z - z)) + 1 / (F z - z)‖ :=
          congrArg (fun w : ℂ => ‖w‖) hsplit
      _ ≤ ‖deriv Φ z - 1 / (F z - z)‖ + ‖1 / (F z - z)‖ := norm_add_le _ _
      _ ≤ C₂ / R₁ + 32 / 31 := add_le_add hmain hvz
  -- ### Near the axis: `deriv Φ` is continuous on the open set `Qreg`
  set Kc : Set ℂ := {z : ℂ | x₀ - 1 ≤ z.re} ∩ {z : ℂ | z.re ≤ x₀ + 3} ∩
    {z : ℂ | |z.im| ≤ T} with hKc
  have hKc_closed : IsClosed Kc := by
    rw [hKc]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  have hKc_bounded : Bornology.IsBounded Kc := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := |x₀ - 1| + |x₀ + 3| + T + 1)).subset ?_
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
    have hz1' : x₀ - 1 ≤ z.re := hz1
    have hz2' : z.re ≤ x₀ + 3 := hz2
    have hz3' : |z.im| ≤ T := hz3
    clear hz1 hz2 hz3
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |x₀ - 1| + |x₀ + 3| := by
      rw [abs_le]
      constructor
      · have h1 := neg_abs_le (x₀ - 1)
        have h2 := abs_nonneg (x₀ + 3)
        linarith
      · have h1 := le_abs_self (x₀ + 3)
        have h2 := abs_nonneg (x₀ - 1)
        linarith
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ (|x₀ - 1| + |x₀ + 3|) + T := by linarith
      _ ≤ |x₀ - 1| + |x₀ + 3| + T + 1 := by linarith
  have hKc_compact : IsCompact Kc :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKc_closed, hKc_bounded⟩
  have hKc_sub : Kc ⊆ MandelDim.Qreg b₁ b₂ := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
    have hz1' : x₀ - 1 ≤ z.re := hz1
    have hz2' : z.re ≤ x₀ + 3 := hz2
    have h := mem_Qreg_of_re (b₁ := b₁) (b₂ := b₂) (x := z.re) (y := z.im)
      (fun a ha => by have hh := h₁ a ha; linarith)
      (fun b hb => by have hh := h₂ b hb; linarith)
    rwa [Complex.re_add_im] at h
  have hderiv_cont : ContinuousOn (deriv Φ) (MandelDim.Qreg b₁ b₂) :=
    ((hΦ.1.analyticOnNhd (Work.Fatou.Qreg.isOpen_Qreg b₁ b₂)).deriv).continuousOn
  obtain ⟨Bnear, hBnear⟩ :=
    hKc_compact.exists_bound_of_continuousOn (hderiv_cont.mono hKc_sub)
  refine ⟨max (C₂ / R₁ + 32 / 31) Bnear, ?_⟩
  intro z hz1 hz2
  by_cases h : T ≤ |z.im|
  · exact le_trans (hfar z hz1 hz2 h) (le_max_left _ _)
  · have hzK : z ∈ Kc := by
      rw [hKc]
      exact ⟨⟨le_of_lt hz1, le_of_lt hz2⟩, le_of_lt (not_le.mp h)⟩
    exact le_trans (hBnear z hzK) (le_max_right _ _)

/-- **FATOU-L1**: the derivative of the Fatou coordinate of a near-translation `F` on
`Qreg b₁ b₂` is bounded on the vertical strip `{x₀ - 1 < Re z < x₀ + 3}` (which lies in
`Qreg b₁ b₂` by `h₁`, `h₂`). -/
theorem fatouDerivBoundedStrip {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) ∧
      ∃ B : ℝ, ∀ z : ℂ, x₀ - 1 < z.re → z.re < x₀ + 3 → ‖deriv Φ z‖ ≤ B := by
  obtain ⟨Φ, hΦ⟩ := fatouCoordExistsClean b₁ b₂ F hadm hF
  exact ⟨Φ, hΦ, deriv_bounded_of_isFatouCoordOn hF h₁ h₂ hΦ⟩

/-- The same bound for the **canonical** Fatou coordinate `Work.FatouWindow.fatouCoord` used by the
rest of the `FatouL1` development (so that consumers need not re-run the existence argument). -/
theorem fatouCoord_deriv_bounded_strip
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ B : ℝ, ∀ z : ℂ, x₀ - 1 < z.re → z.re < x₀ + 3 →
      ‖deriv (fatouCoord hadm hF) z‖ ≤ B :=
  deriv_bounded_of_isFatouCoordOn hF h₁ h₂ (fatouCoord_spec hadm hF)

end

end Work.FatouWindow
