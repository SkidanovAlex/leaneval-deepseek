import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude
import Submission.Work.LinnikAreas.completedRiemannZeta_zero_strip

namespace Work.LinnikAreas

open Commons.NumberTheory.DirichletCharacter (rectBoundary rectSet)

/-- **Non-vanishing of `Λ` on the boundary of the rectangle** `[-1/2, 2] × [-T', T']`.

The quadratic (vertical) edges are harmless: `Λ` has no zeros at all off the critical
strip `0 < re s < 1`.  On the two horizontal edges `im s = ±T'` a zero of `Λ` would be a
zero of `ζ`, hence (being `≠ 1`) a zero of `riemannZeta₁`, and the separation hypothesis
`hsep` forbids zeros of `riemannZeta₁` at height `±T'`. -/
theorem completedRiemannZeta_ne_zero_rectBoundary {c T' : ℝ} (hc : 0 < c) (hT' : 2 ≤ T')
    (hsep : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 →
      c / Real.log (T' + 3) ≤ |ρ.im - T'| ∧ c / Real.log (T' + 3) ≤ |ρ.im + T'|)
    {s : ℂ} (hs : s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary
        (((-1 / 2 : ℝ) : ℂ) - ((T' : ℝ) : ℂ) * Complex.I)
        ((2 : ℂ) + ((T' : ℝ) : ℂ) * Complex.I)) :
    completedRiemannZeta s ≠ 0 ∧ s ≠ 0 ∧ s ≠ 1 := by
  -- coordinates of the two corners
  have hZre : (((-1 / 2 : ℝ) : ℂ) - ((T' : ℝ) : ℂ) * Complex.I).re = -1 / 2 := by simp
  have hZim : (((-1 / 2 : ℝ) : ℂ) - ((T' : ℝ) : ℂ) * Complex.I).im = -T' := by simp
  have hWre : ((2 : ℂ) + ((T' : ℝ) : ℂ) * Complex.I).re = 2 := by simp
  have hWim : ((2 : ℂ) + ((T' : ℝ) : ℂ) * Complex.I).im = T' := by simp
  have hpos : 0 < c / Real.log (T' + 3) := div_pos hc (Real.log_pos (by linarith))
  -- `s ≠ 0` and `s ≠ 1`: both points are strictly interior
  have hs0 : s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.ne_zero_of_mem_rectBoundary
      (by rw [hZre]; norm_num) (by rw [hWre]; norm_num)
      (by rw [hZim]; linarith) (by rw [hWim]; linarith) hs
  have hs1 : s ≠ 1 := by
    refine Commons.NumberTheory.DirichletCharacter.ne_of_mem_rectBoundary_of_inside ?_ hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hZre]; norm_num
    · rw [hWre]; norm_num
    · rw [hZim]; simp; linarith
    · rw [hWim]; simp; linarith
  -- every zero of `riemannZeta₁` has imaginary part different from `±T'`
  have hne : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ T' ∧ ρ.im ≠ -T' := by
    intro ρ hρ
    have h1 := (hsep ρ hρ).1
    have h2 := (hsep ρ hρ).2
    constructor
    · intro h; rw [h] at h1; simp only [sub_self, abs_zero] at h1; linarith
    · intro h; rw [h] at h2; simp only [neg_add_cancel, abs_zero] at h2; linarith
  -- a zero of `Λ` inside the critical strip is a zero of `riemannZeta₁`
  have hzeta1 : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → completedRiemannZeta ρ = 0 →
      riemannZeta₁ ρ = 0 := by
    intro ρ h0 h1 hΛρ
    have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos h0
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h] at h1; simp at h1
    have hζ : riemannZeta ρ = 0 := by
      rw [riemannZeta_def_of_ne_zero hρ0, hΛρ, zero_div]
    have h := riemannZeta_eq_inv_sub_mul hρ1
    rw [hζ] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' (inv_ne_zero (sub_ne_zero.mpr hρ1))
    · exact h'
  refine ⟨?_, hs0, hs1⟩
  intro hΛ
  have hstrip := completedRiemannZeta_zero_strip hΛ
  have hz1 : riemannZeta₁ s = 0 := hzeta1 s hstrip.1 hstrip.2 hΛ
  have hs' := hs
  rw [rectBoundary] at hs'
  simp only [Set.mem_ofPred_eq, Set.mem_uIcc, hZre, hZim, hWre, hWim] at hs'
  rcases hs' with ⟨_, him | him⟩ | ⟨_, hre | hre⟩
  · exact (hne s hz1).2 (by rw [him])
  · exact (hne s hz1).1 (by rw [him])
  · rw [hre] at hstrip; linarith [hstrip.1]
  · rw [hre] at hstrip; linarith [hstrip.2]

end Work.LinnikAreas
