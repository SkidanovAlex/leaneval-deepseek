import Mathlib
import Submission.Work.FatouL1.epsAux

namespace Work.FatouL1

open MeasureTheory

/-- The vertical line through `x` lies in `Qreg b₁ b₂` (from `h₁`, `h₂`). -/
private lemma line_mem {b₁ b₂ : Option ℂ} {x₀ x : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hx : x₀ - 1 < x) (hx' : x < x₀ + 3) (y : ℝ) :
    ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
  mem_openStrip_Qreg h₁ h₂ hx hx' y

/-- The derivative defect restricted to a vertical line of the big strip is continuous
(hence strongly measurable). -/
private lemma continuous_vertDefect {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ x : ℝ}
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hx : x₀ - 1 < x) (hx' : x < x₀ + 3) :
    Continuous (vertDefect F x) := by
  have hline : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
    fun y => line_mem h₁ h₂ hx hx' y
  have hcomp : Continuous fun η : ℝ => deriv F ((x : ℂ) + η * Complex.I) :=
    (continuousOn_deriv_Qreg hF).comp_continuous (by fun_prop) (fun η => hline η)
  change Continuous (fun η : ℝ => deriv F ((x : ℂ) + η * Complex.I) - 1)
  exact hcomp.sub continuous_const

theorem epsLineMass {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {x : ℝ} (hx : x₀ - 1 < x) (hx' : x < x₀ + 3) :
    MeasureTheory.Integrable (Work.FatouL1.vertDefect F x) ∧
      Work.FatouL1.vertMass F x ≤ 1 / 64 := by
  have hline : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
    fun y => line_mem h₁ h₂ hx hx' y
  -- the `L¹` (lintegral) bound of `NearTranslationL1` on this line
  have hlin : ∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F x y‖ ≤ ENNReal.ofReal (1 / 64) :=
    hF.2 x hline
  have hdef : Continuous (vertDefect F x) :=
    continuous_vertDefect hF h₁ h₂ hx hx'
  have hae : AEStronglyMeasurable (vertDefect F x) := hdef.aestronglyMeasurable
  have hfin : HasFiniteIntegral (vertDefect F x) := by
    rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨⟨hae, hfin⟩, ?_⟩
  -- convert the lintegral bound into the integral bound
  have hbridge : ∫ y : ℝ, ‖vertDefect F x y‖ =
      (∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F x y‖).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => norm_nonneg _)
      (hdef.norm.aestronglyMeasurable)
  have hle : (∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F x y‖) ≤ ENNReal.ofReal (1 / 64) := hlin
  calc vertMass F x = ∫ y : ℝ, ‖vertDefect F x y‖ := rfl
    _ = (∫⁻ y : ℝ, ENNReal.ofReal ‖vertDefect F x y‖).toReal := hbridge
    _ ≤ (ENNReal.ofReal (1 / 64)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hle
    _ = 1 / 64 := ENNReal.toReal_ofReal (by norm_num)

end Work.FatouL1
