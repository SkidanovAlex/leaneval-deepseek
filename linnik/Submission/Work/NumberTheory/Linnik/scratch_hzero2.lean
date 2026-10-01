import Mathlib
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory MeromorphicOn
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- **Window-maximality transfer.**

Suppose every zero `u` of `L(·,χ)` with `|Im u| ≤ 10 L` satisfies `Re u ≤ A`. Then every zero of the
completed `L`-function lying in the window `|1 + i·Im s - u| ≤ δ` (with `|Im s| + δ ≤ 10 L`) has
`Re u ≤ A ≤ Re s`. This is the form of the maximality information needed to feed the window-sum
lemmas of §6.

The two auxiliary facts about the archimedean gamma factor (it is non-vanishing on `Re > 0`, and
`completedLFunction χ = LFunction χ · gammaFactor χ` there) are proved inline so that the lemma
only depends on Mathlib and the already published commons. -/
theorem window_hzero_of_Lzero' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {L A δ : ℝ} {s σ : ℂ} (hδ1 : δ < 1) (hwin10 : |s.im| + δ ≤ 10 * L) (hA : A ≤ s.re)
    (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ u = 0 → |u.im| ≤ 10 * L →
      u = σ ∨ u.re ≤ A) :
    ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ σ → u.re ≤ s.re := by
  intro u hdiv hwin hne
  have hmem : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) :=
    Commons.Analysis.Complex.divisor_mem_of_ne_zero hdiv
  -- positivity of `Re u`
  have hre1 : |1 - u.re| ≤ δ := by
    have h := Complex.abs_re_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).re) = 1 - u.re := by simp
    rw [h'] at h
    linarith only [h, hwin]
  have hure : 0 < u.re := by
    have := (abs_le.mp hre1).2
    linarith only [this, hδ1]
  -- `u` is a zero of `LFunction χ`
  have hzero : DirichletCharacter.LFunction χ u = 0 := by
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u =
        ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℤ) :=
      Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem
    have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
      intro h0
      exact hdiv (by rw [hcast, h0]; rfl)
    have hz0 : DirichletCharacter.completedLFunction χ u = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero hnat
    have hgf : DirichletCharacter.gammaFactor χ u ≠ 0 := by
      have key : ∀ z : ℂ, 0 < z.re → z.Gammaℝ ≠ 0 := by
        intro z hz h0
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
        rw [hn] at hz
        have hre : ((-(2 * (n : ℂ)) : ℂ)).re = -(2 * (n : ℝ)) := by simp
        rw [hre] at hz
        have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
        linarith
      unfold DirichletCharacter.gammaFactor
      split_ifs with h
      · exact key u hure
      · exact key (u + 1) (by rw [Complex.add_re, Complex.one_re]; linarith)
    have hune : u ≠ 0 := fun h => by rw [h] at hure; simp at hure
    have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hune)
    have hprod : DirichletCharacter.completedLFunction χ u =
        DirichletCharacter.LFunction χ u * DirichletCharacter.gammaFactor χ u := by
      rw [h0, div_eq_mul_inv, inv_mul_cancel_right₀ hgf]
    rw [hz0] at hprod
    exact (mul_eq_zero.mp hprod.symm).resolve_right hgf
  -- the imaginary part is small
  have him : |u.im| ≤ 10 * L := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
    rw [h'] at h
    have h2 : |u.im| ≤ |s.im| + |s.im - u.im| := by
      calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
    linarith only [h, h2, hwin, hwin10]
  rcases hmax u hzero him with h | h
  · exact absurd h hne
  · exact le_trans h hA

end Commons.NumberTheory.Linnik
