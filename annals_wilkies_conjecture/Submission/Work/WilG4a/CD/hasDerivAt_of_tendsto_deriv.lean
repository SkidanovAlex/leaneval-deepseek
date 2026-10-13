import Mathlib
import Submission.Work.WilG4a.Defs

set_option autoImplicit false

namespace Work.WilG4a.CD

/-- The punctured `ε`-`δ` condition of the target statement is exactly continuity at `c`:
the case `x = c` of the standard formulation is trivial. -/
private lemma continuousAt_of_punctured (F : ℝ → ℝ) (c ρ : ℝ)
    (h : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |F x - F c| < ε) :
    ContinuousAt F c := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, -, hδp⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_cases hxc : x = c
  · subst hxc
    simpa using hε
  · rw [Real.dist_eq] at hx ⊢
    exact hδp x hxc hx

/-- Lagrange's mean value theorem on the interval between `c` and `x`, in the form needed
below: the secant slope of `F` over `[c, x]` equals the derivative of `F` at some point `ξ`
lying strictly between `c` and `x` (hence `ξ ≠ c`, and `ξ` is closer to `c` than `x` is).
Requires `F` continuous at `c` and differentiable on the punctured `ρ`-neighbourhood of `c`. -/
private lemma exists_deriv_eq_slope_of_continuousAt (F : ℝ → ℝ) (c ρ : ℝ) (hρ : 0 < ρ)
    (hcontAt : ContinuousAt F c)
    (hdiff : ∀ x ∈ Set.Ioo (c - ρ) (c + ρ), x ≠ c → DifferentiableAt ℝ F x)
    (x : ℝ) (hx : |x - c| < ρ) (hxc : x ≠ c) :
    ∃ ξ : ℝ, ξ ≠ c ∧ |ξ - c| < |x - c| ∧ deriv F ξ = slope F c x := by
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hx
  have hmem : ∀ y : ℝ, c - ρ < y → y < c + ρ → y ∈ Set.Ioo (c - ρ) (c + ρ) :=
    fun y h1 h2 => ⟨h1, h2⟩
  rcases lt_or_gt_of_ne hxc with hlt | hgt
  · -- Case `x < c`: mean value theorem on `[x, c]`.
    have hcontOn : ContinuousOn F (Set.Icc x c) :=
      continuousOn_of_forall_continuousAt fun y hy => by
        rw [Set.mem_Icc] at hy
        rcases eq_or_ne y c with hyc | hyne
        · rw [hyc]; exact hcontAt
        · exact (hdiff y (hmem y (by linarith [hy.1, hxlo]) (by linarith [hy.2, hρ])) hyne).continuousAt
    have hdiffOn : DifferentiableOn ℝ F (Set.Ioo x c) := fun y hy => by
      rw [Set.mem_Ioo] at hy
      exact (hdiff y (hmem y (by linarith [hy.1, hxlo]) (by linarith [hy.2, hρ]))
        (by linarith [hy.2])).differentiableWithinAt
    obtain ⟨ξ, hξmem, hξ⟩ := exists_deriv_eq_slope' F hlt hcontOn hdiffOn
    rw [Set.mem_Ioo] at hξmem
    refine ⟨ξ, ne_of_lt hξmem.2, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hξmem.2] : ξ - c < 0),
          abs_of_neg (by linarith [hlt] : x - c < 0)]
      linarith [hξmem.1]
    · rw [hξ]; exact slope_comm F x c
  · -- Case `c < x`: mean value theorem on `[c, x]`.
    have hcontOn : ContinuousOn F (Set.Icc c x) :=
      continuousOn_of_forall_continuousAt fun y hy => by
        rw [Set.mem_Icc] at hy
        rcases eq_or_ne y c with hyc | hyne
        · rw [hyc]; exact hcontAt
        · exact (hdiff y (hmem y (by linarith [hy.1, hρ]) (by linarith [hy.2, hxhi])) hyne).continuousAt
    have hdiffOn : DifferentiableOn ℝ F (Set.Ioo c x) := fun y hy => by
      rw [Set.mem_Ioo] at hy
      exact (hdiff y (hmem y (by linarith [hy.1, hρ]) (by linarith [hy.2, hxhi]))
        (by linarith [hy.1])).differentiableWithinAt
    obtain ⟨ξ, hξmem, hξ⟩ := exists_deriv_eq_slope' F hgt hcontOn hdiffOn
    rw [Set.mem_Ioo] at hξmem
    exact ⟨ξ, ne_of_gt hξmem.1, by
      rw [abs_of_pos (by linarith [hξmem.1] : 0 < ξ - c),
          abs_of_pos (by linarith [hgt] : 0 < x - c)]
      linarith [hξmem.2], hξ⟩

theorem hasDerivAt_of_tendsto_deriv (F : ℝ → ℝ) (c L ρ : ℝ) (hρ : 0 < ρ)
    (hdiff : ∀ x ∈ Set.Ioo (c - ρ) (c + ρ), x ≠ c → DifferentiableAt ℝ F x)
    (hcont : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |F x - F c| < ε)
    (htend : ∀ ε > 0, ∃ δ > 0, δ ≤ ρ ∧ ∀ x : ℝ, x ≠ c → |x - c| < δ → |deriv F x - L| < ε) :
    HasDerivAt F L c := by
  have hcontAt : ContinuousAt F c := continuousAt_of_punctured F c ρ hcont
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδρ, hδb⟩ := htend ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro x hxmem hxdist
  have hxc : x ≠ c := by simpa using hxmem
  rw [Real.dist_eq] at hxdist
  rw [Real.dist_eq]
  obtain ⟨ξ, hξne, hξlt, hξeq⟩ :=
    exists_deriv_eq_slope_of_continuousAt F c ρ hρ hcontAt hdiff x
      (lt_of_lt_of_le hxdist hδρ) hxc
  have hb : |deriv F ξ - L| < ε := hδb ξ hξne (lt_trans hξlt hxdist)
  rw [← hξeq]
  exact hb

end Work.WilG4a.CD
