import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.geom
import Submission.Work.FatouL1.strip_in_Qreg
import Submission.Work.FatouL1.cauchyLineBound

/-!
# FATOU-L1: `‖F' - 1‖ ≤ 1/150` on the wide strip

The statement `NearTranslationL1` controls `F' - 1` only in `L¹` along the vertical lines of
`Qreg b₁ b₂` (`∫⁻ y, ‖F' (x + iy) - 1‖ ≤ 1/64`).  The wide strip
`W = {x₀ - 1/8 < Re z < x₀ + 17/8}` of `cocycleCorrectionWide`/`localAbelWide` sits strictly
inside the *slightly larger* strip `(x₀ - 1, x₀ + 3) × ℝ`, and the hypotheses `h₁`, `h₂` put
every vertical line of that larger strip inside `Qreg b₁ b₂`.  Cauchy's formula on the strip
(`cauchyLineBound`, with the `L¹` mass on the two boundary lines replaced by Cauchy's estimate)
then upgrades the `L¹` bound to a *pointwise* bound:

  `‖F' z - 1‖ ≤ (1/64)/(2π) · (1/(z.re - (x₀ - 1)) + 1/(x₀ + 3 - z.re))`.

For `z` in the wide strip both denominators exceed `7/8`, so the right-hand side is at most
`(1/128π)·(16/7) = 1/(56π) < 1/150` — that is `work.FatouL1.wideDerivSmall`, the quantitative
input of the cocycle correction (`NOTES_cocycleCorrectionWide.md`: `‖F' - 1‖ ≤ 0.006` there).

The mean value estimate only needs `‖F' - 1‖ ≤ 1/32` on the wider strip as the boundedness
hypothesis `M` of `cauchyLineBound`; the `1/64` enters through the `L¹` bound on the lines.
-/

open MandelDim Set MeasureTheory
open scoped Topology

namespace Work.FatouL1

noncomputable section

-- `hadm` is part of the requested statement but not needed by the proof.
set_option linter.unusedVariables false

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The vertical line through `x` (with `x₀ - 1 < x < x₀ + 3`) lies in `Qreg b₁ b₂`: `h₁` gives
`a.re < x₀ - 1 < x` for every `a ∈ b₁` and `h₂` gives `x < x₀ + 3 < b.re` for every `b ∈ b₂`. -/
lemma mem_openStrip_Qreg (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {x : ℝ} (hx : x₀ - 1 < x) (hx' : x < x₀ + 3) (y : ℝ) :
    ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
  mem_Qreg_of_re (fun a ha => by have := h₁ a ha; linarith)
    (fun b hb => by have := h₂ b hb; linarith)

/-- **`F' - 1` is small on the wide strip.**  The `L¹` bound `∫⁻ y, ‖F' (x+iy) - 1‖ ≤ 1/64` on
every vertical line of `(x₀ - 1, x₀ + 3)` (which `h₁`, `h₂` put inside `Qreg b₁ b₂`) and the
pointwise bound `‖F' - 1‖ ≤ 1/32` on the same strip, fed into Cauchy's formula on the strip
(`cauchyLineBound`), give `‖F' z - 1‖ ≤ 1/(56π) < 1/150` for every `z` of the wide strip
`x₀ - 1/8 < Re z < x₀ + 17/8`. -/
theorem wideDerivSmall {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∀ z : ℂ, x₀ - 1 / 8 < z.re → z.re < x₀ + 17 / 8 → ‖deriv F z - 1‖ ≤ 1 / 150 := by
  intro z hz₁ hz₂
  -- The strip `(x₀ - 1, x₀ + 3) × ℝ` on which Cauchy's formula is applied.
  have hsub : {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} ⊆ MandelDim.Qreg b₁ b₂ := by
    intro w hw
    have h := mem_openStrip_Qreg (b₁ := b₁) (b₂ := b₂) h₁ h₂ hw.1 hw.2 w.im
    simpa using h
  have hopen : IsOpen {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hdiff : DifferentiableOn ℂ F {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} := hF.1.1.mono hsub
  -- `F' - 1` is holomorphic on the open strip (`F` is holomorphic there, hence so is `F'`).
  have hhol : DifferentiableOn ℂ (fun w : ℂ => deriv F w - 1)
      {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} :=
    (hdiff.deriv hopen).sub (differentiableOn_const 1)
  -- Boundedness hypothesis `M = 1/32` (`NearTranslationOn` inside `Qreg`).
  have hbdd : ∀ w : ℂ, x₀ - 1 < w.re → w.re < x₀ + 3 → ‖deriv F w - 1‖ ≤ 1 / 32 := by
    intro w hw hw'
    exact (hF.1.2 w (hsub ⟨hw, hw'⟩)).2
  -- The `L¹` bound of `NearTranslationL1`, on the lines of that strip.
  have hline : ∀ x ∈ Ioo (x₀ - 1) (x₀ + 3),
      ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖ ≤
        ENNReal.ofReal (1 / 64) := by
    intro x hx
    exact hF.2 x (fun y => mem_openStrip_Qreg h₁ h₂ hx.1 hx.2 y)
  have hmain := cauchyLineBound (a := x₀ - 1) (b := x₀ + 3)
    (h := fun w : ℂ => deriv F w - 1) (by linarith : x₀ - 1 < x₀ + 3)
    (M := 1 / 32) (ε := 1 / 64) (by norm_num) hhol hbdd hline
    (by linarith : x₀ - 1 < z.re) (by linarith : z.re < x₀ + 3)
  -- Numerics: both denominators are `> 7/8`, hence the bracket is `≤ 16/7`.
  have hA0 : 0 < z.re - (x₀ - 1) := by linarith
  have hB0 : 0 < (x₀ + 3) - z.re := by linarith
  have hsum : (1 / (z.re - (x₀ - 1)) + 1 / ((x₀ + 3) - z.re)) ≤ 16 / 7 := by
    have h1 : (1 : ℝ) / (z.re - (x₀ - 1)) ≤ 8 / 7 := by
      rw [div_le_iff₀ hA0]; linarith
    have h2 : (1 : ℝ) / ((x₀ + 3) - z.re) ≤ 8 / 7 := by
      rw [div_le_iff₀ hB0]; linarith
    linarith
  have hfin : (1 : ℝ) / (56 * Real.pi) ≤ 1 / 150 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 56 * Real.pi) (by norm_num : (0 : ℝ) < 150)]
    linarith [Real.pi_gt_three]
  have heq : (1 / 64) / (2 * Real.pi) * (16 / 7) = 1 / (56 * Real.pi) := by
    field_simp
    ring
  calc ‖deriv F z - 1‖
      ≤ (1 / 64) / (2 * Real.pi) * (1 / (z.re - (x₀ - 1)) + 1 / ((x₀ + 3) - z.re)) := hmain
    _ ≤ (1 / 64) / (2 * Real.pi) * (16 / 7) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 / (56 * Real.pi) := heq
    _ ≤ 1 / 150 := hfin

end

end Work.FatouL1

-- sanity: the target rests only on the permitted axioms
#print axioms Work.FatouL1.wideDerivSmall
