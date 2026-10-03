import Mathlib
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.FatouL1.cauchyLineBound

/-!
# Pointwise bound for `F' - 1` on a vertical strip inside `Qreg b₁ b₂`

`MandelDim.NearTranslationL1 F Q` controls the derivative defect `F' - 1` only in `L¹` along the
vertical lines of `Q` (`∫⁻ y, ‖F' (x+iy) - 1‖ ≤ 1/64`) and pointwise by `1/32` on `Q`.  On the
strip `x₀ - 1 < Re z < x₀ + 3` — which lies inside `Qreg b₁ b₂` as soon as `h₁` puts the vertices
of `b₁` to the left of `x₀ - 1` and `h₂` puts those of `b₂` to the right of `x₀ + 3` — Cauchy's
formula on rectangles of increasing height upgrades this to the sharp *pointwise* estimate

  `‖F' z - 1‖ ≤ (1/64)/(2π) · (1/(Re z - (x₀ - 1)) + 1/((x₀ + 3) - Re z))`.

The analytic content (contour integration on an expanding rectangle with the horizontal parts
dominated by the sup bound and the vertical parts by the `L¹` masses) is
`Work.FatouL1.cauchyLineBound`; here we feed it the holomorphy and the two bounds.
-/

open Set MeasureTheory Filter Metric
open scoped Topology

namespace Work.FatouL1

noncomputable section

-- `hadm` is part of the requested statement but its content is not needed by the proof.
set_option linter.unusedVariables false in
theorem pointwiseDerivBound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∀ z : ℂ, x₀ - 1 < z.re → z.re < x₀ + 3 →
      ‖deriv F z - 1‖ ≤ (1 / 64) / (2 * Real.pi) *
        (1 / (z.re - (x₀ - 1)) + 1 / (x₀ + 3 - z.re)) := by
  -- A vertical line strictly between the vertices of `b₁` and those of `b₂` lies in `Qreg`.
  have hmem : ∀ x : ℝ, x₀ - 1 < x → x < x₀ + 3 → ∀ y : ℝ,
      ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
    intro x hx hx' y
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : a.re < x := by have := h₁ a ha; linarith
      have hre : (((x : ℂ) + y * Complex.I) - a).re = x - a.re := by simp
      have him : (((x : ℂ) + y * Complex.I) - a).im = y - a.im := by simp
      rw [hre, him]
      calc -|y - a.im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
        _ < x - a.re := by linarith
    · intro b hb
      have hb' : x < b.re := by have := h₂ b hb; linarith
      have hre : (((x : ℂ) + y * Complex.I) - b).re = x - b.re := by simp
      have him : (((x : ℂ) + y * Complex.I) - b).im = y - b.im := by simp
      rw [hre, him]
      calc x - b.re < 0 := by linarith
        _ ≤ |y - b.im| := abs_nonneg _
  -- The strip is contained in `Qreg`, and it is open.
  have hsub : {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} ⊆ MandelDim.Qreg b₁ b₂ := by
    intro w hw
    have h := hmem w.re hw.1 hw.2 w.im
    rwa [Complex.re_add_im] at h
  have hopen : IsOpen {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  -- `F` is holomorphic on the strip, hence so is `F' - 1`.
  have hhol : DifferentiableOn ℂ (fun w : ℂ => deriv F w - 1)
      {w : ℂ | x₀ - 1 < w.re ∧ w.re < x₀ + 3} :=
    ((hF.1.1.mono hsub).deriv hopen).sub_const 1
  intro z hz₁ hz₂
  -- Boundedness on the strip (`M = 1/32`).
  have hbdd : ∀ w : ℂ, x₀ - 1 < w.re → w.re < x₀ + 3 → ‖deriv F w - 1‖ ≤ 1 / 32 :=
    fun w hw hw' => (hF.1.2 w (hsub ⟨hw, hw'⟩)).2
  -- The `L¹` masses of the vertical lines (`ε = 1/64`).
  have hline : ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 3),
      ∫⁻ y : ℝ, ENNReal.ofReal ‖deriv F ((x : ℂ) + y * Complex.I) - 1‖ ≤
        ENNReal.ofReal (1 / 64) :=
    fun x hx => hF.2 x (hmem x hx.1 hx.2)
  exact cauchyLineBound (a := x₀ - 1) (b := x₀ + 3)
    (h := fun w : ℂ => deriv F w - 1) (M := 1 / 32) (ε := 1 / 64)
    (by linarith : x₀ - 1 < x₀ + 3) (by norm_num) hhol hbdd hline hz₁ hz₂

end

end Work.FatouL1

-- the target rests only on the permitted axioms
#print axioms Work.FatouL1.pointwiseDerivBound
