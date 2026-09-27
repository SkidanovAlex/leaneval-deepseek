import Mathlib
import Submission.Work.EQ.strip_path_avoiding_countable
import Submission.Work.EQ.countable_preimage_complex_exp

namespace Work.EQ

open Filter _root_.Topology Set

/-- Given a countable `P`, any two points `x, y` of the open annulus `r₁ < ‖z‖ < r₂` with
`y ∉ P` are joined by a path in the annulus which avoids `P` on `(0,1]` (the starting point may
lie in `P`). -/
theorem annulus_path_avoiding_countable {P : Set ℂ} (hP : P.Countable) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) {x y : ℂ} (hx₁ : r₁ < ‖x‖) (hx₂ : ‖x‖ < r₂)
    (hy₁ : r₁ < ‖y‖) (hy₂ : ‖y‖ < r₂) (hyP : y ∉ P) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      (∀ t ∈ Set.Icc 0 1, r₁ < ‖γ t‖ ∧ ‖γ t‖ < r₂) ∧
      (∀ t ∈ Set.Ioo 0 1, γ t ∉ P) := by
  -- The annulus `{r₁ < ‖z‖ < r₂}` is the image of the horizontal convex strip
  -- `{a < Re z < b}` (`a = log r₁`, `b = log r₂`) under `Complex.exp`.
  have hlt₁ : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁ hr₁₂
  -- the endpoints are nonzero
  have hxne : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₁; linarith
  have hyne : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy₁; linarith
  have hxnorm : 0 < ‖x‖ := lt_trans hr₁ hx₁
  have hynorm : 0 < ‖y‖ := lt_trans hr₁ hy₁
  -- the logs of the endpoints lie in the strip
  have hux : Real.log r₁ < (Complex.log x).re ∧ (Complex.log x).re < Real.log r₂ := by
    rw [Complex.log_re]
    exact ⟨Real.log_lt_log hr₁ hx₁, Real.log_lt_log hxnorm hx₂⟩
  have hvy : Real.log r₁ < (Complex.log y).re ∧ (Complex.log y).re < Real.log r₂ := by
    rw [Complex.log_re]
    exact ⟨Real.log_lt_log hr₁ hy₁, Real.log_lt_log hynorm hy₂⟩
  have hvQ : Complex.log y ∉ Complex.exp ⁻¹' P := by
    rw [Set.mem_preimage, Complex.exp_log hyne]
    exact hyP
  obtain ⟨γ₀, hcont, h0, h1, hstrip, havoid⟩ :=
    strip_path_avoiding_countable hlt₁ (countable_preimage_complex_exp hP) hux hvy hvQ
  refine ⟨fun t => Complex.exp (γ₀ t), ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_exp.comp_continuousOn hcont
  · show Complex.exp (γ₀ 0) = x
    rw [h0, Complex.exp_log hxne]
  · show Complex.exp (γ₀ 1) = y
    rw [h1, Complex.exp_log hyne]
  · intro t ht
    rw [Complex.norm_exp]
    obtain ⟨hlo, hhi⟩ := hstrip t ht
    constructor
    · have h1' : Real.exp (Real.log r₁) < Real.exp ((γ₀ t).re) := Real.exp_lt_exp.mpr hlo
      rwa [Real.exp_log hr₁] at h1'
    · have h1' : Real.exp ((γ₀ t).re) < Real.exp (Real.log r₂) := Real.exp_lt_exp.mpr hhi
      rwa [Real.exp_log (lt_trans hr₁ hr₁₂)] at h1'
  · intro t ht hmem
    exact havoid t ht (by rwa [Set.mem_preimage])

end Work.EQ
