import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.geom
import Submission.Work.FatouL1.strip_in_Qreg

/-!
# FATOU-L1: the wide strip and its elementary properties

Definitions and elementary consequences of the hypotheses of `Work.FatouL1.cocycleCorrectionWide`.
This module is sorry-free and is imported by `cocycleCorrectionWide` (and by children working on
the analytic core).
-/

open MandelDim Set Metric
open scoped Topology

namespace Work.FatouL1

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}


/-- The **wide strip** `W = {x₀ - 1/8 < Re z < x₀ + 17/8}` (width `9/4`). -/
def wStrip (x₀ : ℝ) : Set ℂ := {z : ℂ | x₀ - 1 / 8 < z.re ∧ z.re < x₀ + 17 / 8}

lemma mem_wStrip {z : ℂ} : z ∈ wStrip x₀ ↔ x₀ - 1 / 8 < z.re ∧ z.re < x₀ + 17 / 8 := Iff.rfl

/-- The **wide overlap** `A = W ∩ F⁻¹ W`. -/
def wOverlap (F : ℂ → ℂ) (x₀ : ℝ) : Set ℂ := {z | z ∈ wStrip x₀ ∧ F z ∈ wStrip x₀}

lemma mem_wOverlap {z : ℂ} : z ∈ wOverlap F x₀ ↔ z ∈ wStrip x₀ ∧ F z ∈ wStrip x₀ := Iff.rfl

lemma wStrip_isOpen (x₀ : ℝ) : IsOpen (wStrip x₀) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma wStrip_convex (x₀ : ℝ) : Convex ℝ (wStrip x₀) := by
  have h : wStrip x₀ = Complex.reLm ⁻¹' Set.Ioo (x₀ - 1 / 8) (x₀ + 17 / 8) := by
    ext z; simp [wStrip]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.reLm

/-- **Every vertical line of the wide strip lies in `Qreg b₁ b₂`.**  This is where the hypotheses
`h₁`, `h₂` (and `QAdm`) are used: `x₀` sits at least `1` to the right of `b₁` and at least `3` to the
left of `b₂`, so every `x` in `(x₀ - 1/8, x₀ + 17/8)` is strictly between them. -/
theorem wide_lines_in_Qreg
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∀ x ∈ Set.Ioo (x₀ - 1 / 8) (x₀ + 17 / 8), ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
  intro x hx y
  refine mem_Qreg_of_re ?_ ?_
  · intro a ha
    have h := h₁ a ha
    have h' := hx.1
    linarith
  · intro b hb
    have h := h₂ b hb
    have h' := hx.2
    linarith

/-- The wide strip is contained in `Qreg b₁ b₂`. -/
theorem wideStrip_subset_Qreg
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    wStrip x₀ ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  have h := wide_lines_in_Qreg h₁ h₂ z.re hz z.im
  simpa using h

/-- `F` is holomorphic on the wide strip. -/
lemma wF_differentiableOn (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    DifferentiableOn ℂ F (wStrip x₀) :=
  hF.1.1.mono (wideStrip_subset_Qreg h₁ h₂)

/-- The pointwise bound `‖F z - (z + 1)‖ ≤ 1/32` on the wide strip. -/
lemma wF_sub_one (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {z : ℂ}
    (hz : z ∈ wStrip x₀) : ‖F z - (z + 1)‖ ≤ 1 / 32 :=
  (hF.1.2 z (wideStrip_subset_Qreg h₁ h₂ hz)).1

/-- The pointwise bound `‖deriv F z - 1‖ ≤ 1/32` on the wide strip. -/
lemma wF_deriv_sub_one (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {z : ℂ}
    (hz : z ∈ wStrip x₀) : ‖deriv F z - 1‖ ≤ 1 / 32 :=
  (hF.1.2 z (wideStrip_subset_Qreg h₁ h₂ hz)).2

/-- `deriv F` does not vanish on the wide strip. -/
lemma wF_deriv_ne_zero (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {z : ℂ}
    (hz : z ∈ wStrip x₀) : deriv F z ≠ 0 := by
  intro h
  have hb := wF_deriv_sub_one hF h₁ h₂ hz
  rw [h] at hb
  norm_num at hb

/-- **`F` is injective on the wide strip.**  Both `z` and `w` and the segment between them lie in
`Qreg b₁ b₂` (the strip is convex), where `‖F' - 1‖ ≤ 1/32`; the mean value inequality applied to
`F - id` gives `‖(F z - z) - (F w - w)‖ ≤ (1/32)‖z - w‖`, so `F z = F w` forces `z = w`. -/
theorem wF_injOn (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    Set.InjOn F (wStrip x₀) := by
  have hdiff : DifferentiableOn ℂ F (wStrip x₀) := wF_differentiableOn hF h₁ h₂
  have hopen : IsOpen (wStrip x₀) := wStrip_isOpen (x₀ := x₀)
  have hconv : Convex ℝ (wStrip x₀) := wStrip_convex (x₀ := x₀)
  have hderiv : ∀ u ∈ wStrip x₀,
      derivWithin (fun u : ℂ => F u - u) (wStrip x₀) u = deriv F u - 1 := by
    intro u hu
    have hu_nhds : wStrip x₀ ∈ 𝓝 u := hopen.mem_nhds hu
    have hdF : DifferentiableAt ℂ F u := (hdiff u hu).differentiableAt hu_nhds
    rw [derivWithin_of_mem_nhds hu_nhds]
    rw [show (fun u : ℂ => F u - u) = F - id from rfl]
    simpa using deriv_sub (f := F) (g := id) (x := u) hdF (differentiableAt_id)
  intro z hz w hw hzw
  have hmvt : ‖(F w - w) - (F z - z)‖ ≤ (1 / 32) * ‖w - z‖ := by
    refine Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℂ) (G := ℂ)
      (f := fun u : ℂ => F u - u) (s := wStrip x₀) (x := z) (y := w) (C := 1 / 32)
      ?_ ?_ hconv hz hw
    · exact hdiff.sub (differentiableOn_id)
    · intro u hu
      rw [hderiv u hu]
      exact wF_deriv_sub_one hF h₁ h₂ hu
  have hconn : (F w - w) - (F z - z) = z - w := by rw [hzw]; ring
  rw [hconn] at hmvt
  have hzero : ‖z - w‖ = 0 := by
    have hs : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
    nlinarith [hmvt, norm_nonneg (z - w), hs]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end

end Work.FatouL1
