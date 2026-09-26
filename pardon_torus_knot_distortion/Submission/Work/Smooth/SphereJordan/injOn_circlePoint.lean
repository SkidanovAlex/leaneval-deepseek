import Mathlib
import Submission.Work.Smooth.Jordan.Defs

namespace Work.Smooth.SphereJordan

/-- The standard parametrisation `θ ↦ e^{iθ}` of the boundary circle of the model disc `𝔻` is
injective on one period `[0, 2π)`.  This is the injectivity of the exponential function on an
interval of length `2π`. -/
theorem injOn_circlePoint : Set.InjOn (Work.Smooth.Jordan.circlePoint : ℝ → Work.Smooth.Jordan.Disc) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  rw [Set.mem_Ico] at ha hb
  -- equality in the disc descends to equality of the complex exponentials
  have h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
    have := congrArg (fun z : Work.Smooth.Jordan.Disc => (z : ℂ)) hab
    simpa [Work.Smooth.Jordan.circlePoint_coe] using this
  -- `exp` is injective up to integer multiples of `2π`
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have h2 : a = b + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa [Complex.exp_ofReal_mul_I_im] using this
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · -- `n ≤ -1`: `a = b + n·2π < 0`, contradicting `0 ≤ a`
    have hnle : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    have hb' : b + (n : ℝ) * (2 * Real.pi) < 0 := by nlinarith [hb.1, hb.2]
    linarith [ha.1, h2, hb']
  · -- `n = 0`: immediately `a = b`
    subst hn0
    simp at h2
    linarith [h2]
  · -- `n ≥ 1`: `a = b + n·2π ≥ 2π`, contradicting `a < 2π`
    have hnge : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := by omega
      exact_mod_cast this
    have hb' : 2 * Real.pi ≤ b + (n : ℝ) * (2 * Real.pi) := by nlinarith [hb.1]
    linarith [ha.2, h2, hb']

end Work.Smooth.SphereJordan
