import Submission.Work.Smooth.JordanSeparation.Unconditional

/-!
# `γ (arg z)` is continuous for a periodic `γ`

For a continuous `2π`-periodic `γ : ℝ → ℂ`, the composite `z ↦ γ (arg z)` is continuous on
`ℂ ∖ {0}` even though `Complex.arg` itself jumps by `2π` across the negative real axis: the jump is
absorbed by the periodicity.

The key identity is

`γ (arg w) = γ (arg (-w) + π)`   (`w ≠ 0`),

proved through `Complex.exp_eq_exp_iff_exists_int` (the two arguments differ by `π` modulo `2π`).
It lets one continue `z ↦ γ (arg z)` across the cut by the branch of `arg` at `-w`: on the slit
plane `Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}` use `Complex.continuousAt_arg`, and on its
complement (`w` a negative real, so that `-w` lies in the slit plane) use the identity.

This is the analytic plumbing needed by every "radial" or "sweep" construction of the
Jordan–Schoenflies theorem; see `SCHOENFLIES.md` §3.6.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- `exp (arg z * I) = z / ‖z‖` for `z ≠ 0`. -/
theorem exp_arg_mul_I_eq (z : ℂ) (hz : z ≠ 0) :
    Complex.exp ((Complex.arg z : ℝ) * Complex.I) = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [eq_div_iff (by exact_mod_cast norm_ne_zero_iff.mpr hz), mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- Two real parameters with the same exponential give the same value of a `2π`-periodic
function. -/
theorem eq_of_exp_eq_periodic {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    {θ θ' : ℝ} (h : Complex.exp (θ * Complex.I) = Complex.exp (θ' * Complex.I)) :
    γ θ = γ θ' := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hk'' : (θ : ℂ) * Complex.I
      = ((θ' + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hk]; push_cast; ring
  have hθ : (θ : ℂ) = ((θ' + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hk''
  have hθR : θ = θ' + (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hθ
  rw [hθR]
  exact hper.int_mul k θ'

/-- **The `2π`-shift of the argument changes nothing**: `γ (arg w) = γ (arg (-w) + π)` for a
`2π`-periodic `γ` and `w ≠ 0`. -/
theorem curve_arg_neg_periodic {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    {w : ℂ} (hw : w ≠ 0) :
    γ (Complex.arg w) = γ (Complex.arg (-w) + Real.pi) := by
  have h1 : Complex.exp ((Complex.arg (-w) + Real.pi : ℝ) * Complex.I)
      = Complex.exp ((Complex.arg w : ℝ) * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, exp_arg_mul_I_eq w hw,
      exp_arg_mul_I_eq (-w) (neg_ne_zero.mpr hw), Complex.exp_pi_mul_I, norm_neg]
    rw [neg_div, neg_mul_neg]
    simp
  exact (eq_of_exp_eq_periodic hper h1).symm

/-- **`z ↦ γ (arg z)` is continuous off the origin.** -/
theorem continuousAt_curve_arg_periodic {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi)) (hcont : Continuous γ) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (fun z : ℂ => γ (Complex.arg z)) w := by
  by_cases hslit : w ∈ Complex.slitPlane
  · exact hcont.continuousAt.comp (Complex.continuousAt_arg hslit)
  · have hle : w.re ≤ 0 := by
      by_contra h
      exact hslit (Or.inl (by simpa using not_le.mp h))
    have him : w.im = 0 := by
      by_contra h
      exact hslit (Or.inr h)
    have hlt : w.re < 0 := by
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · refine absurd h' ?_
        intro h0
        exact hw (Complex.ext h0 him)
    have hneg : -w ∈ Complex.slitPlane := Or.inl (by rw [Complex.neg_re]; linarith)
    have hcomp₀ : ContinuousAt (fun z : ℂ => Complex.arg (-z)) w := by
      simpa [Function.comp_def] using (Complex.continuousAt_arg hneg).comp continuousAt_neg
    have hcomp₁ : ContinuousAt (fun z : ℂ => Complex.arg (-z) + Real.pi) w :=
      hcomp₀.add_const Real.pi
    have hcomp₂ : ContinuousAt (fun z : ℂ => γ (Complex.arg (-z) + Real.pi)) w := by
      simpa [Function.comp_def] using hcont.continuousAt.comp hcomp₁
    refine hcomp₂.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    exact (curve_arg_neg_periodic hper hz).symm

/-- **`z ↦ γ (arg z)` is continuous on `ℂ ∖ {0}`.** -/
theorem continuousOn_curve_arg_periodic {γ : ℝ → ℂ}
    (hper : Function.Periodic γ (2 * Real.pi)) (hcont : Continuous γ) :
    ContinuousOn (fun z : ℂ => γ (Complex.arg z)) {w : ℂ | w ≠ 0} := fun w hw =>
  (continuousAt_curve_arg_periodic hper hcont hw).continuousWithinAt

end

end Work.Smooth.JordanSeparation
