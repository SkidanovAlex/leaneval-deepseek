import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.StripOfCoordHelpers
import Submission.Work.Pert.Pin.strip_high_pin
import Submission.Work.Pert.Pin.strip_band_pin
import Submission.Work.Pert.Pin.log_le_sqrt
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Pin

/-!
# `Work.Pert.Pin.strip_of_pin_v2`

The vertical-strip coverage for the pinned perturbed Fatou coordinate (Shishikura A.4,
`Dφ_strip`): given the gauge `Φm (Xc d (-M)) = -M` at scale `M`, the whole strip
`{|Re w| ≤ 1, |Im w| ≥ y₁}` lies in the maximal domain `DphiP`.

The proof is the assembly of two independently proved height bands:

* `Work.Pert.Pin.strip_band_pin` — the band `y₁ ≤ |Im w| ≤ √M` (the walk from the deep point
  `w - n ∈ Dstrip` plus the trap against the datum's walk, with the trap radius `≲ 1/√M`);
* `Work.Pert.Pin.strip_high_pin` — the half-strip `Ξ + C (1 + log M) ≤ |Im w|` (the Rouché
  covering at `w`, level 0);

glued by `Work.Pert.Pin.log_mul_add_le_sqrt`, which gives `Ξ + C (1 + log M) ≤ √M` for `M ≥ Ms`.
-/

open MandelDim

theorem strip_of_pin_v2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 0 < Ξ)
    {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀)
    {y₁ : ℝ} (hy₁ : d.η₀ < y₁) :
    ∃ Ms : ℝ, 0 < Ms ∧ ∀ M : ℝ, Ms ≤ M →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.closedBall (0 : ℂ) rr ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) →
        ∀ Φm : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α) →
          Work.Pert.Xc d (((-M : ℝ)) : ℂ) ∈ Work.Pert.Qm Ξ α →
          Φm (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) →
          ∀ w : ℂ, y₁ ≤ |w.im| → |w.re| ≤ 1 →
            w ∈ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ α) := by
  obtain ⟨Ch, hChpos, Mh, hMhpos, hHigh⟩ :=
    Work.Pert.Pin.strip_high_pin d hF hd Ξ hΞ hrr hrrD hy₁
  obtain ⟨Mb, hMbpos, hBand⟩ :=
    Work.Pert.Pin.strip_band_pin d hF hd Ξ hΞ hrr hrrD hy₁
  obtain ⟨Ml, hMlpos, hglue⟩ := Work.Pert.Pin.log_le_sqrt_glue Ξ Ch hΞ hChpos.le
  refine ⟨max (max Mh Mb) (max Ml 1), by positivity, ?_⟩
  intro M hM
  have hMh : Mh ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMb : Mb ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMl : Ml ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  obtain ⟨Lh, hLhc, hLhD, hLhrr, δh, hδh, hH⟩ := hHigh M hMh
  obtain ⟨Lb, hLbc, hLbD, hLbrr, δb, hδb, hB⟩ := hBand M hMb
  refine ⟨Lh ∪ Lb, hLhc.union hLbc, Set.union_subset hLhD hLbD,
    hLhrr.trans Set.subset_union_left, min δh δb, lt_min hδh hδb, ?_⟩
  intro f Df u σ α hNear hf0 hInF1 hα hud hub hform hnorm hτQ hQAdm hNT Φm hΦm hp1 hp2
    w hw1 hw2
  have hkey : Ξ + Ch * (1 + Real.log M) ≤ Real.sqrt M := hglue M hMl
  have hNearH : MandelDim.NearOn f₀ f Df Lh δh :=
    Work.Pert.nearOn_mono' hNear Set.subset_union_left (min_le_left _ _)
  have hNearB : MandelDim.NearOn f₀ f Df Lb δb :=
    Work.Pert.nearOn_mono' hNear Set.subset_union_right (min_le_right _ _)
  by_cases hcase : |w.im| ≤ Real.sqrt M
  · exact hB f Df u σ α hNearB hf0 hInF1 hα hud hub hform hnorm hτQ hQAdm hNT Φm hΦm
      hp1 hp2 w hw1 hw2 hcase
  · push_neg at hcase
    exact hH f Df u σ α hNearH hf0 hInF1 hα hud hub hform hnorm hτQ hQAdm hNT Φm hΦm
      hp1 hp2 w (by linarith only [hkey, hcase]) hw2

end Work.Pert.Pin
