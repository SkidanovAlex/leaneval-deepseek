import Mathlib
import Submission.Work.Fatou.Qreg.Setup
import Submission.Work.Interfaces.Fatou

/-!
# Injectivity of a near-translation on the vertical strip `x₀ - 1 < Re z < x₀ + 3`

`Work.Fatou.Qreg.stripInjOn`: if `F` is a near-translation on Shishikura's region
`𝒬(b₁,b₂)` (i.e. `‖F z - (z + 1)‖ ≤ 1/32` and `‖F' z - 1‖ ≤ 1/32` on `𝒬`), and the strip
`S = {z | x₀ - 1 < Re z < x₀ + 3}` lies in `𝒬` (which holds as soon as `Re a + 1 < x₀` for
`a ∈ b₁` and `x₀ + 3 < Re b` for `b ∈ b₂`, see `strip_subset_Qreg`), then `F` is injective
on `S`.

The argument is the mean value inequality applied to `g z = F z - z`, whose derivative
`F' z - 1` is bounded by `1/32` in norm on `S`: if `F z = F w` with `z, w ∈ S`, then
`g w - g z = z - w`, so `‖z - w‖ ≤ (1/32) ‖z - w‖`, forcing `z = w`.
-/

namespace Work.Fatou.Qreg

open Set Metric Complex

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- A near-translation on `𝒬` is `1/32`-close to the identity on the strip
`x₀ - 1 < Re z < x₀ + 3`: the mean value inequality for `z ↦ F z - z`, whose derivative
`F' z - 1` is bounded by `1/32` there. -/
lemma norm_sub_id_le_of_strip (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀)
    (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    {z w : ℂ} (hz : z ∈ strip x₀) (hw : w ∈ strip x₀) :
    ‖(F w - w) - (F z - z)‖ ≤ (1 / 32 : ℝ) * ‖w - z‖ := by
  have hsub : strip x₀ ⊆ MandelDim.Qreg b₁ b₂ := strip_subset_Qreg h₁ h₂
  have hconv : Convex ℝ (strip x₀) := convex_strip x₀
  have hopen : IsOpen (strip x₀) := isOpen_strip x₀
  have hF' : DifferentiableOn ℂ F (strip x₀) := hF.1.mono hsub
  have hdiff : ∀ u ∈ strip x₀, DifferentiableAt ℂ (fun u => F u - u) u := fun u hu =>
    (hF'.differentiableAt (hopen.mem_nhds hu)).sub differentiableAt_id
  have hbound : ∀ u ∈ strip x₀, ‖deriv (fun u => F u - u) u‖ ≤ (1 / 32 : ℝ) := by
    intro u hu
    have hFu : DifferentiableAt ℂ F u := hF'.differentiableAt (hopen.mem_nhds hu)
    have hder : deriv (fun v => F v - v) u = deriv F u - 1 := by
      change deriv (F - id) u = deriv F u - 1
      rw [deriv_sub hFu differentiableAt_id, deriv_id]
    rw [hder]
    exact (hF.2 u (hsub hu)).2
  exact hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hz hw

/-- **Injectivity on the strip.** `F` is injective on the vertical strip
`x₀ - 1 < Re z < x₀ + 3` contained in the region `𝒬(b₁,b₂)` on which `F` is a near-translation. -/
theorem stripInjOn {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) :
    Set.InjOn F {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := by
  intro z hz w hw hzw
  have h2 : (F w - w) - (F z - z) = z - w := by rw [hzw]; ring
  have h := norm_sub_id_le_of_strip h₁ h₂ hF hz hw
  rw [h2, norm_sub_rev] at h
  have hle : ‖w - z‖ ≤ 0 := by nlinarith [norm_nonneg (w - z)]
  have hwz : w - z = 0 := norm_le_zero_iff.mp hle
  exact (sub_eq_zero.mp hwz).symm

end Work.Fatou.Qreg
