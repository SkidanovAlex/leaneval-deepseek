import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.gSq_continuous

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun)

/-- **Continuity of `RtildeSq`** (GM (7.5) without the square root).

For every parameter `B`, every `N`, and every pair of bumps `ψ₁` (supported on `|x| ≤ C₀`,
`ψ₁ 0 = 1`) and `ψ₂` (supported on `x ∈ [1/C₀, C₀]`, `ψ₂ 1 = 1`) in the sense of
`IsBumpAtZero`/`IsBumpAtOne` of `Defs.lean`, the function

`u ↦ RtildeSq W N B ψ₁ ψ₂ u = ∫ u', (N B) ψ₁ (N B (u - u')) ψ₂ u' ‖R(u')‖² du'`

is continuous on `ℝ`. -/
theorem RtildeSq_continuous (W : Finset ℝ) (N : ℕ) (B : ℝ) (C₀ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (h₁ : Work.GM.S3.IsBumpAtZero ψ₁ C₀) (h₂ : Work.GM.S3.IsBumpAtOne ψ₂ C₀) :
    Continuous (fun u : ℝ => Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ u) := by
  -- `C₀ ≥ 1`, since `ψ₂ 1 = 1` forces `1 ∈ [1/C₀, C₀]`
  have hC₀ : 1 ≤ C₀ := by
    have hne : ψ₂ 1 ≠ 0 := by rw [h₂.2.2.2.1]; norm_num
    exact (Set.mem_Icc.mp (h₂.2.2.1 1 hne)).2
  -- `ψ₁` is bounded
  obtain ⟨c₁, hc₁nonneg, hc₁⟩ := h₁.2.2.2.2 0
  have hψ₁bd : ∀ x : ℝ, |ψ₁ x| ≤ c₁ := by
    intro x
    have := hc₁ x
    rwa [iteratedDeriv_zero] at this
  -- the weight `g = ψ₂ ‖R(W)‖²` is continuous with compact support, hence integrable
  set g : ℝ → ℝ := fun u' => ψ₂ u' * ‖Rfun W u'‖ ^ 2 with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]
    exact gSq_continuous ψ₂ C₀ hC₀ h₂ W
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc fun x hx => ?_
    have hx0 : ψ₂ x = 0 := by
      by_contra hne
      exact hx (h₂.2.2.1 x hne)
    rw [hgdef]
    simp [hx0]
  have hgint : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgcs
  -- the dominating function
  have hbnd_int : Integrable (fun u' : ℝ => |(N : ℝ) * B| * c₁ * ‖g u'‖) volume :=
    hgint.norm.const_mul _
  -- measurability of each section
  have hFmeas : ∀ u : ℝ, AEStronglyMeasurable
      (fun u' : ℝ => ((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * g u') volume := by
    intro u
    exact (((continuous_const : Continuous fun _ : ℝ => (N : ℝ) * B).mul
      (h₁.1.continuous.comp (by fun_prop))).mul hgcont).aestronglyMeasurable
  -- the uniform domination
  have hbnd : ∀ u : ℝ, ∀ᵐ u' ∂volume,
      ‖((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * g u'‖ ≤ |(N : ℝ) * B| * c₁ * ‖g u'‖ := by
    intro u
    refine Filter.Eventually.of_forall fun u' => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hψ₁bd _) (abs_nonneg _)) (abs_nonneg _)
  -- continuity of each section
  have hcont : ∀ᵐ u' ∂volume,
      Continuous (fun u : ℝ => ((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * g u') :=
    Filter.Eventually.of_forall fun u' =>
      ((continuous_const : Continuous fun _ : ℝ => (N : ℝ) * B).mul
        (h₁.1.continuous.comp (by fun_prop))).mul continuous_const
  have hmain : Continuous
      (fun u : ℝ => ∫ u', ((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * g u') :=
    continuous_of_dominated (μ := volume) hFmeas hbnd hbnd_int hcont
  -- identify the two functions
  have heq : (fun u : ℝ => RtildeSq W N B ψ₁ ψ₂ u)
      = fun u : ℝ => ∫ u', ((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (u - u'))) * g u' := by
    funext u
    rw [RtildeSq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    simp only [hgdef]
    ring
  rw [heq]
  exact hmain

end Work.GM.S3
