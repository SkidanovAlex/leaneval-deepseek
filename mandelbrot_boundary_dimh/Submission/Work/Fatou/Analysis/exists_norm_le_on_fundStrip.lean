import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.DevH.devH_deriv
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Fatou.Qreg.InjGeom
import Submission.Work.Fatou.Surface.devH_fundStrip

/-!
# Local boundedness of a Fatou coordinate on the fundamental strip

`Work.Fatou.Surface.devH_fundStrip` exhibits the fundamental strip
`fundStrip F (Qreg b₁ b₂) x₀` as the image under the unfolding map
`devH x₀ F` of the unit strip `{0 ≤ Re ζ < 1}`, and `devH` is within `1/32` of
the translation `ζ ↦ x₀ + ζ` there. Consequently the points of the fundamental strip
with `|Im s| ≤ M` are the images of the compact box
`{0 ≤ Re ζ ≤ 1, |Im ζ| ≤ M + 1/32}`, whose image under `devH` is a compact subset of the
*open* set `Qreg b₁ b₂` (`Work.Fatou.devH_mem_Qreg`). Since a Fatou coordinate is
differentiable, hence continuous, on `Qreg`, it is bounded there.

This is the ingredient used (in step 3 of `Work.Fatou.Analysis.fatouUniqueOfConstructed`) to
control the representative of a point of the vertical strip `{0 ≤ Re w ≤ 1}` as `|Im w| → ∞`.
-/

namespace Work.Fatou.Analysis

open MandelDim Set Metric Complex
open scoped Topology

/-- The box `0 ≤ Re ζ ≤ 1`, `|Im ζ| ≤ M + 1/32` is compact. -/
lemma isCompact_fundBox (M : ℝ) :
    IsCompact {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 ∧ |ζ.im| ≤ M + 1 / 32} := by
  set K : Set ℂ := {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 ∧ |ζ.im| ≤ M + 1 / 32} with hK
  have hclosed : IsClosed K := by
    have h1 : IsClosed {ζ : ℂ | (0 : ℝ) ≤ ζ.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {ζ : ℂ | ζ.re ≤ (1 : ℝ)} :=
      isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {ζ : ℂ | |ζ.im| ≤ M + 1 / 32} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have heq : K = {ζ : ℂ | (0 : ℝ) ≤ ζ.re} ∩ {ζ : ℂ | ζ.re ≤ (1 : ℝ)} ∩
        {ζ : ℂ | |ζ.im| ≤ M + 1 / 32} := by
      rw [hK]
      ext ζ
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
    exact (h1.inter h2).inter h3
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |M + 1 / 32|)).subset ?_
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hre : |ζ.re| ≤ 1 := by rw [abs_of_nonneg hζ.1]; exact hζ.2.1
    calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
      _ ≤ 1 + |M + 1 / 32| := by
          have := hζ.2.2
          have := le_abs_self (M + 1 / 32)
          linarith
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

/-- On the box `Re ζ ≤ 1`, the unfolding map `devH` moves the imaginary part by at most `1/32`
(it is an interpolation between the identity and `F`, and a near-translation moves `Im` by at
most `1/32`). -/
lemma abs_im_devH_sub_le {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : QAdm b₁ b₂)
    (hNT : NearTranslationOn F (Qreg b₁ b₂)) {ζ : ℂ} (hζ : ζ.re ≤ 1) :
    |(Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F ζ).im - ζ.im| ≤ 1 / 32 := by
  rcases le_or_gt ζ.re (1 / 8) with h | h
  · rw [Work.Fatou.devH_of_le_one_eighth h]
    simp
  · have hsub := Work.Fatou.devH_sub_le hadm hNT h.le (by linarith)
    have := Work.Fatou.abs_im_sub_le hsub
    simpa using this

theorem exists_norm_le_on_fundStrip {b₁ b₂ : Option ℂ} {F Φ₀ : ℂ → ℂ}
    (hadm : MandelDim.QAdm b₁ b₂) (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hΦ₀ : MandelDim.IsFatouCoordOn F Φ₀ (MandelDim.Qreg b₁ b₂)) (M : ℝ) :
    ∃ B : ℝ, ∀ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂),
      |s.im| ≤ M → ‖Φ₀ s‖ ≤ B := by
  set x₀ : ℝ := Work.Fatou.xOf b₁ b₂ with hx₀
  set K : Set ℂ := {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1 ∧ |ζ.im| ≤ M + 1 / 32} with hK
  -- `devH x₀ F` is continuous and `K` is compact, so its image is compact ...
  have hC1 : ContDiff ℝ 1 (Work.Fatou.devH x₀ F) := by
    have := (Work.Fatou.DevH.devH_deriv hadm hNT).2.1
    rwa [← hx₀] at this
  have hcont : Continuous (Work.Fatou.devH x₀ F) := hC1.continuous
  -- ... and it lies in the open set `Qreg b₁ b₂`
  have hKsub : K ⊆ {ζ : ℂ | -(1 / 8) < ζ.re ∧ ζ.re < 9 / 8} := by
    intro ζ hζ
    exact ⟨by linarith [hζ.1], by linarith [hζ.2.1]⟩
  have hLsub : Work.Fatou.devH x₀ F '' K ⊆ Qreg b₁ b₂ := by
    rintro s ⟨ζ, hζ, rfl⟩
    have hmem := Work.Fatou.devH_mem_Qreg hadm hNT (Work.Fatou.mem_Sigma.mpr (hKsub hζ))
    rwa [← hx₀] at hmem
  have hLc : IsCompact (Work.Fatou.devH x₀ F '' K) :=
    (isCompact_fundBox M).image hcont
  -- `Φ₀` is continuous on `Qreg`, hence on the compact set `devH x₀ F '' K`
  have hcontOn : ContinuousOn Φ₀ (Work.Fatou.devH x₀ F '' K) := by
    intro s hs
    exact ((hΦ₀.1 s (hLsub hs)).differentiableAt (Work.Fatou.Qreg.isOpen_Qreg b₁ b₂ |>.mem_nhds (hLsub hs))
      ).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hLc.exists_bound_of_continuousOn hcontOn
  refine ⟨B, ?_⟩
  intro s hs hsM
  apply hB
  -- every such `s` is the image of a point of the box `K`
  obtain ⟨ζ, hζ0, hζ1, hζeq⟩ :=
    (Work.Fatou.Surface.devH_fundStrip hadm hNT).2.1 s hs
  refine ⟨ζ, ⟨hζ0, le_of_lt hζ1, ?_⟩, hζeq⟩
  -- `devH` moves the imaginary part by at most `1/32`, and `Re ζ < 1`
  have him : |ζ.im - s.im| ≤ 1 / 32 := by
    have h := abs_im_devH_sub_le hadm hNT (ζ := ζ) (le_of_lt hζ1)
    rw [← hx₀] at h
    rw [hζeq] at h
    rwa [abs_sub_comm] at h
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 := (abs_le.mp him).1
    have h2 := (abs_le.mp hsM).1
    linarith
  · have h1 := (abs_le.mp him).2
    have h2 := (abs_le.mp hsM).2
    linarith

end Work.Fatou.Analysis
