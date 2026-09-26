import Mathlib

namespace Work.Smooth.Morse.Regular

open Set Filter
open scoped Topology

/-- If `g` is continuous on a neighbourhood `Ioo (a - ρ) (a + ρ)` of `a` and `g a ≠ 0`, then on a
smaller symmetric neighbourhood `Ioo (a - δ) (a + δ)` with `0 < δ ≤ ρ` the function `g` keeps a
constant (strict) sign. -/
private lemma exists_sign_neighborhood {g : ℝ → ℝ} {a ρ : ℝ} (hρ : 0 < ρ)
    (hc : ContinuousOn g (Set.Ioo (a - ρ) (a + ρ))) (hne : g a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ((∀ x ∈ Set.Ioo (a - δ) (a + δ), 0 < g x) ∨
        (∀ x ∈ Set.Ioo (a - δ) (a + δ), g x < 0)) := by
  have ha : a ∈ Set.Ioo (a - ρ) (a + ρ) := ⟨by linarith, by linarith⟩
  have hs : Set.Ioo (a - ρ) (a + ρ) ∈ 𝓝 a := isOpen_Ioo.mem_nhds ha
  have hca : ContinuousAt g a := hc.continuousAt hs
  rcases lt_or_gt_of_ne hne with h | h
  · have hU : {x | g x < 0} ∈ 𝓝 a := hca.eventually (isOpen_Iio.mem_nhds h)
    have hint : ({x | g x < 0} ∩ Set.Ioo (a - ρ) (a + ρ)) ∈ 𝓝 a := Filter.inter_mem hU hs
    rcases Metric.mem_nhds_iff.mp hint with ⟨ε, hε, hball⟩
    refine ⟨min ε ρ, lt_min hε hρ, min_le_right _ _, Or.inr ?_⟩
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hb : x ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1, min_le_left ε ρ], by linarith [hx.2, min_le_left ε ρ]⟩
    exact (hball hb).1
  · have hU : {x | 0 < g x} ∈ 𝓝 a := hca.eventually (isOpen_Ioi.mem_nhds h)
    have hint : ({x | 0 < g x} ∩ Set.Ioo (a - ρ) (a + ρ)) ∈ 𝓝 a := Filter.inter_mem hU hs
    rcases Metric.mem_nhds_iff.mp hint with ⟨ε, hε, hball⟩
    refine ⟨min ε ρ, lt_min hε hρ, min_le_right _ _, Or.inl ?_⟩
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hb : x ∈ Metric.ball a ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1, min_le_left ε ρ], by linarith [hx.2, min_le_left ε ρ]⟩
    exact (hball hb).1

theorem strictMonoOn_or_strictAntiOn_of_deriv_ne_zero {ψ : ℝ → ℝ} {a ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x ∈ Set.Ioo (a - ρ) (a + ρ), HasDerivAt ψ (deriv ψ x) x)
    (hdc : ContinuousOn (deriv ψ) (Set.Ioo (a - ρ) (a + ρ))) (hne : deriv ψ a ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      (StrictMonoOn ψ (Set.Ioo (a - δ) (a + δ)) ∨
        StrictAntiOn ψ (Set.Ioo (a - δ) (a + δ))) := by
  rcases exists_sign_neighborhood hρ hdc hne with ⟨δ, hδpos, hδρ, hsign⟩
  refine ⟨δ, hδpos, hδρ, ?_⟩
  have hsub : Set.Ioo (a - δ) (a + δ) ⊆ Set.Ioo (a - ρ) (a + ρ) := by
    intro x hx
    simp only [Set.mem_Ioo] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hdiff : DifferentiableOn ℝ ψ (Set.Ioo (a - δ) (a + δ)) := fun x hx =>
    (hd x (hsub hx)).differentiableAt.differentiableWithinAt
  have hcont : ContinuousOn ψ (Set.Ioo (a - δ) (a + δ)) := hdiff.continuousOn
  rcases hsign with hpos | hneg
  · left
    refine strictMonoOn_of_deriv_pos (convex_Ioo (a - δ) (a + δ)) hcont (fun x hx => ?_)
    rw [isOpen_Ioo.interior_eq] at hx
    exact hpos x hx
  · right
    refine strictAntiOn_of_deriv_neg (convex_Ioo (a - δ) (a + δ)) hcont (fun x hx => ?_)
    rw [isOpen_Ioo.interior_eq] at hx
    exact hneg x hx

end Work.Smooth.Morse.Regular
