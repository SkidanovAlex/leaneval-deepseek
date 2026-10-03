import Mathlib
import Submission.Work.FatouL1.epsAux

namespace Work.FatouL1

/-- Every point of the horizontal segment between `a + η i` and `b + η i` lies in `Qreg b₁ b₂`
when both endpoints lie in the big strip `x₀ - 1 < Re < x₀ + 3` bounded by the vertices `b₁`
(left) and `b₂` (right). -/
lemma horizSeg_mem_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {a b : ℝ} (ha : x₀ - 1 < a) (ha' : a < x₀ + 3)
    (hb : x₀ - 1 < b) (hb' : b < x₀ + 3) (η : ℝ) :
    ∀ ξ ∈ Set.uIcc a b, ((ξ : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
  intro ξ hξ
  refine bigStrip_subset_Qreg h₁ h₂ ?_
  rw [mem_bigStrip]
  have hre : ((ξ : ℂ) + η * Complex.I).re = ξ := by simp [Complex.add_re, Complex.mul_re]
  rw [hre]
  have hmin : min a b ≤ ξ := by
    rw [Set.mem_uIcc] at hξ
    rcases hξ with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith [min_le_left a b, min_le_right a b]
  have hmax : ξ ≤ max a b := by
    rw [Set.mem_uIcc] at hξ
    rcases hξ with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [le_max_left a b, le_max_right a b]
  exact ⟨lt_of_lt_of_le (lt_min ha hb) hmin, lt_of_le_of_lt hmax (max_lt ha' hb')⟩

theorem norm_vertEps_sub_le {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    {x x' : ℝ} (hx : x₀ - 1 < x) (hx' : x < x₀ + 3)
    (hy : x₀ - 1 < x') (hy' : x' < x₀ + 3) (η : ℝ) :
    ‖Work.FatouL1.vertEps F x η - Work.FatouL1.vertEps F x' η‖ ≤
      ∫ ξ in (min x x')..(max x x'), ‖Work.FatouL1.vertDefect F ξ η‖ := by
  rcases le_total x x' with hxx' | hx'x
  · rw [min_eq_left hxx', max_eq_right hxx']
    have hseg : ∀ ξ ∈ Set.uIcc x x', ((ξ : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
      horizSeg_mem_Qreg h₁ h₂ hx hx' hy hy' η
    have hftc : Work.FatouL1.vertEps F x' η - Work.FatouL1.vertEps F x η
        = ∫ ξ in x..x', Work.FatouL1.vertDefect F ξ η := eps_horizontal_ftc hF hseg
    calc ‖Work.FatouL1.vertEps F x η - Work.FatouL1.vertEps F x' η‖
        = ‖Work.FatouL1.vertEps F x' η - Work.FatouL1.vertEps F x η‖ := norm_sub_rev _ _
      _ = ‖∫ ξ in x..x', Work.FatouL1.vertDefect F ξ η‖ := by rw [← hftc]
      _ ≤ ∫ ξ in x..x', ‖Work.FatouL1.vertDefect F ξ η‖ :=
          intervalIntegral.norm_integral_le_integral_norm hxx'
  · rw [min_eq_right hx'x, max_eq_left hx'x]
    have hseg : ∀ ξ ∈ Set.uIcc x' x, ((ξ : ℂ) + η * Complex.I) ∈ MandelDim.Qreg b₁ b₂ :=
      horizSeg_mem_Qreg h₁ h₂ hy hy' hx hx' η
    have hftc : Work.FatouL1.vertEps F x η - Work.FatouL1.vertEps F x' η
        = ∫ ξ in x'..x, Work.FatouL1.vertDefect F ξ η := eps_horizontal_ftc hF hseg
    calc ‖Work.FatouL1.vertEps F x η - Work.FatouL1.vertEps F x' η‖
        = ‖∫ ξ in x'..x, Work.FatouL1.vertDefect F ξ η‖ := by rw [hftc]
      _ ≤ ∫ ξ in x'..x, ‖Work.FatouL1.vertDefect F ξ η‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx'x

end Work.FatouL1
