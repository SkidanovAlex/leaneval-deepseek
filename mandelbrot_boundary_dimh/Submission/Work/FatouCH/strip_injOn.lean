import Mathlib
import Submission.Work.Interfaces.Fatou

namespace Work.FatouCH

open MandelDim in
lemma strip_injOn {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re)
    (hF : NearTranslationOn F (Qreg b₁ b₂)) :
    Set.InjOn F {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} := by
  -- The vertical strip `S = {x₀ - 1 < Re < x₀ + 3}` is convex and lies inside `Qreg b₁ b₂`.
  have hconv : Convex ℝ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} :=
    (convex_Ioo (x₀ - 1) (x₀ + 3)).linear_preimage Complex.reCLM.toLinearMap
  have hSsub : {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} ⊆ MandelDim.Qreg b₁ b₂ := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, ?_⟩
    · intro a ha
      have haz : a.re < z.re := by have := h₁ a ha; linarith
      have hpos : 0 < (z - a).re := by simp [Complex.sub_re]; linarith
      exact lt_of_le_of_lt (neg_nonpos.mpr (abs_nonneg _)) hpos
    · intro b hb
      have hbz : b.re > z.re := by have := h₂ b hb; linarith
      have hneg : (z - b).re < 0 := by simp [Complex.sub_re]; linarith
      exact lt_of_lt_of_le hneg (abs_nonneg _)
  have hopen : IsOpen {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  rintro z₁ hz₁ z₂ hz₂ hFz
  -- On `S`, `F - id` has derivative `F' - 1` of norm `≤ 1/32`, so it is `1/32`-Lipschitz.
  have hdiffAt : ∀ x ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3},
      DifferentiableAt ℂ (fun z : ℂ => F z - z) x := by
    intro x hx
    exact ((hF.1.differentiableAt (Filter.mem_of_superset (hopen.mem_nhds hx) hSsub))).sub
      differentiableAt_id
  have hbound : ∀ x ∈ {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 3},
      ‖deriv (fun z : ℂ => F z - z) x‖ ≤ (1 / 32 : ℝ) := by
    intro x hx
    have hxQ : x ∈ MandelDim.Qreg b₁ b₂ := hSsub hx
    have hd : HasDerivAt (fun z : ℂ => F z - z) (deriv F x - 1) x :=
      (((hF.1.differentiableAt
        (Filter.mem_of_superset (hopen.mem_nhds hx) hSsub))).hasDerivAt).sub (hasDerivAt_id x)
    rw [hd.deriv]
    exact (hF.2 x hxQ).2
  have hMVT := hconv.norm_image_sub_le_of_norm_deriv_le hdiffAt hbound hz₁ hz₂
  have h0 : (F z₂ - z₂) - (F z₁ - z₁) = -(z₂ - z₁) := by rw [← hFz]; ring
  rw [h0, norm_neg] at hMVT
  have hz : ‖z₂ - z₁‖ = 0 := by
    nlinarith [hMVT, norm_nonneg (z₂ - z₁)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end Work.FatouCH
