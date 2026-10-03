import Mathlib
import Submission.Work.FatouL1.solverKernel

/-!
# FATOU-L1: the horizontal (`+∞`) contribution to the Cauchy–Heine kernel

The Cauchy–Heine / translation solver of `solverKernel.lean` is
`hcSolver h z = (I/2) * ∫ y, h (z - 1/2 + y*I) * tanh (π y)`, i.e. the kernel is
`cot (π (s - z))` on the vertical line `Re s = Re z - 1/2`.  When the contour is moved
vertically, the horizontal pieces carry the integrand

  `h (x + Y*I) * (I/2) * cot (π ((x + Y*I) - z))`,   `x ∈ [A,B]`.

As `Y → +∞` the argument `τ = (x + Y*I) - z` lies in the half-plane `Im τ ≥ 1/2`, and the
classical expansion `cot (π τ) = -I + O(e^{-2π Im τ})` (made quantitative by `hdec`) splits
the kernel into

  `(I/2) * cot (π τ) = 1/2 + (I/2) * (cot (π τ) + I)`,

the constant part pairing with `∫ h` — which tends to `0` by `hlim` — and the remainder decaying
exponentially, hence of size `O(e^{-2π Y})` uniformly on the bounded interval `[A,B]`.  The
conclusion is the horizontal contribution statement used for the contour shifts in the
`L¹` Fatou-coordinate construction.
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.FatouL1

noncomputable section

/-- **The horizontal `+∞` contribution of the Cauchy–Heine kernel tends to `0`.**

Bounded data `h` on the horizontal lines `x ↦ h (x + Y*I)` (`x ∈ [A,B]`, `‖h‖ ≤ C`), the
quantitative half-plane bound `‖cot (π τ) + I‖ ≤ 4 e^{-2π Im τ}` for `Im τ ≥ 1/2`, continuity of
the two factors on `[A,B]`, and vanishing of the horizontal averages `∫_A^B h ((·) + Y*I) → 0`
imply that `∫_A^B h (x + Y*I) * (I/2) cot (π ((x + Y*I) - z)) → 0`. -/
theorem hcHorizontalPlus {h : ℂ → ℂ} {z : ℂ} {A B C : ℝ}
    (hAB : A ≤ B) (hC : 0 ≤ C)
    (hCpt : ∀ x ∈ Set.Icc A B, ∀ y : ℝ, ‖h ((x : ℂ) + y * Complex.I)‖ ≤ C)
    (hdec : ∀ τ : ℂ, 1 / 2 ≤ τ.im → ‖Complex.cot (Real.pi * τ) + Complex.I‖ ≤ 4 * Real.exp (-2 * Real.pi * τ.im))
    (hcont : ∀ Y : ℝ, ContinuousOn (fun x : ℝ => h ((x : ℂ) + Y * Complex.I)) (Set.uIcc A B))
    (hcont2 : ∀ Y : ℝ, z.im + 1 / 2 ≤ Y → ContinuousOn (fun x : ℝ =>
        Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z))) (Set.uIcc A B))
    (hlim : Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in A..B, h ((x : ℂ) + Y * Complex.I)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun Y : ℝ => ∫ x : ℝ in A..B,
      h ((x : ℂ) + Y * Complex.I) * (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z))))
      Filter.atTop (nhds 0) := by
  -- The uniform exponential bound `|kernel remainder| ≤ C * (1/2) * 4 e^{-2π(Y - z.im)}` on `[A,B]`.
  have hbd : Filter.Tendsto
      (fun Y : ℝ => (C * (1 / 2) * (4 * Real.exp (-2 * Real.pi * (Y - z.im)))) * |B - A|)
      Filter.atTop (nhds 0) := by
    have harg : Filter.Tendsto (fun Y : ℝ => 2 * Real.pi * (Y - z.im)) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b / (2 * Real.pi) + z.im, fun a ha => ?_⟩
      have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
      have hmul : (2 * Real.pi) * (b / (2 * Real.pi)) ≤ (2 * Real.pi) * (a - z.im) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hπ)
      have hbb : (2 * Real.pi) * (b / (2 * Real.pi)) = b := by field_simp
      linarith [hbb ▸ hmul]
    have hexp : Filter.Tendsto (fun Y : ℝ => Real.exp (-2 * Real.pi * (Y - z.im))) Filter.atTop (nhds 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
      have h' : Filter.Tendsto (fun Y : ℝ => Real.exp (-(2 * Real.pi * (Y - z.im)))) Filter.atTop (nhds 0) := h
      simpa [neg_mul] using h'
    have h2 := hexp.const_mul (C * (1 / 2) * 4)
    have h3 := h2.mul_const |B - A|
    simpa [mul_assoc] using h3
  -- The constant piece `∫ h * (1/2)` tends to `0` by `hlim`.
  have hg : Filter.Tendsto
      (fun Y : ℝ => ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) * (1 / 2 : ℂ)) Filter.atTop (nhds 0) := by
    have h1 : (fun Y : ℝ => ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) * (1 / 2 : ℂ))
        = fun Y : ℝ => (∫ x in A..B, h ((x : ℂ) + Y * Complex.I)) * (1 / 2 : ℂ) := by
      funext Y
      exact intervalIntegral.integral_mul_const (1 / 2 : ℂ) _
    rw [h1]
    simpa using hlim.mul_const (1 / 2 : ℂ)
  -- The decaying piece, controlled uniformly by `hbd`.
  have he : Filter.Tendsto
      (fun Y : ℝ => ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) *
        (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - 1 / 2))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall (fun Y => norm_nonneg _)) ?_ hbd
    filter_upwards [Filter.eventually_atTop.mpr ⟨z.im + 1 / 2, fun Y hY => hY⟩] with Y hY
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [Set.uIoc_of_le hAB] at hx
    have hxI : x ∈ Set.Icc A B := ⟨le_of_lt hx.1, hx.2⟩
    have htau : (((x : ℂ) + Y * Complex.I) - z).im = Y - z.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    have hge : 1 / 2 ≤ (((x : ℂ) + Y * Complex.I) - z).im := by rw [htau]; linarith
    have h1 : ‖h ((x : ℂ) + Y * Complex.I)‖ ≤ C := hCpt x hxI Y
    have h2 := hdec (((x : ℂ) + Y * Complex.I) - z) hge
    have hEq : Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - (1 / 2 : ℂ)
        = Complex.I / 2 * (Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) + Complex.I) := by
      rw [mul_add]
      rw [show Complex.I / 2 * Complex.I = -(1 / 2) by
        rw [div_mul_eq_mul_div, Complex.I_mul_I]; norm_num]
      ring
    calc ‖h ((x : ℂ) + Y * Complex.I) *
            (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - 1 / 2)‖
        = ‖h ((x : ℂ) + Y * Complex.I)‖ * ‖Complex.I / 2‖
            * ‖Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) + Complex.I‖ := by
          rw [hEq, norm_mul, norm_mul]; ring
      _ ≤ C * (1 / 2) * (4 * Real.exp (-2 * Real.pi * (((x : ℂ) + Y * Complex.I) - z).im)) := by
          rw [show ‖Complex.I / 2‖ = (1 / 2 : ℝ) by rw [norm_div, Complex.norm_I]; norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h2 (norm_nonneg _) (by positivity)
      _ = C * (1 / 2) * (4 * Real.exp (-2 * Real.pi * (Y - z.im))) := by rw [htau]
  -- The exact splitting of the integral for `Y ≥ z.im + 1/2`.
  have hsplit : ∀ Y : ℝ, z.im + 1 / 2 ≤ Y →
      ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) *
          (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)))
      = (∫ x in A..B, h ((x : ℂ) + Y * Complex.I) * (1 / 2 : ℂ))
        + ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) *
            (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - 1 / 2) := by
    intro Y hY
    have hGint : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + Y * Complex.I) * (1 / 2 : ℂ)) volume A B :=
      ((hcont Y).mul_const (1 / 2 : ℂ)).intervalIntegrable
    have hEint : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + Y * Complex.I) *
        (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - 1 / 2)) volume A B :=
      ((hcont Y).mul ((hcont2 Y hY).sub (continuousOn_const (c := (1 / 2 : ℂ))))).intervalIntegrable
    rw [← intervalIntegral.integral_add hGint hEint]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hsum : Filter.Tendsto
      (fun Y : ℝ => (∫ x in A..B, h ((x : ℂ) + Y * Complex.I) * (1 / 2 : ℂ))
        + ∫ x in A..B, h ((x : ℂ) + Y * Complex.I) *
            (Complex.I / 2 * Complex.cot (Real.pi * (((x : ℂ) + Y * Complex.I) - z)) - 1 / 2))
      Filter.atTop (nhds 0) := by
    simpa using hg.add he
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards [Filter.eventually_atTop.mpr ⟨z.im + 1 / 2, fun Y hY => hY⟩] with Y hY
  exact (hsplit Y hY).symm

end

end Work.FatouL1
