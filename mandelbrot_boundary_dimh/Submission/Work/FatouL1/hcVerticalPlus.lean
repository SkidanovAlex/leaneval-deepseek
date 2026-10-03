import Mathlib
import Submission.Work.FatouL1.solverKernel

/-!
# FATOU-L1: the vertical contour of the Cauchy–Heine solver, at `Re s = Re z + 1/2`

`solverKernel.lean` defines the Cauchy–Heine solver along the vertical line
`Re s = Re z - 1/2`:

  `hcSolver h z = (I/2) * ∫ y, h (z - 1/2 + y*I) * tanh (π y)`,

the kernel there being `cot (π (s - z)) = -I * tanh (π (·))` on that line.  The lemma below is the
companion piece for the *other* boundary line, `Re s = Re z + 1/2`: the truncated integrals

  `I * ∫_{-Y}^{Y} h (Re z + 1/2 + y*I) * (I/2) * cot (π ((Re z + 1/2 + y*I) - z))`

converge, as `Y → +∞`, to `hcSolver h (z + 1)`.  Indeed on that line
`(Re z + 1/2 + y*I) - z = 1/2 + (y - Im z) I`, so the kernel is again `-I * tanh (π (y - Im z))`,
and the two sides differ only by the substitution `y ↦ y - Im z` in the integral defining
`hcSolver h (z + 1)` — which is the content of the change-of-variables identity
`MeasureTheory.integral_add_right_eq_self`.

The statement is exactly what a contour-shift argument needs: moving the contour of `hcSolver`
up to `Re s = Re z + 1/2` does not change the value, and the difference equation
`hcSolver h (z+1) - hcSolver h z = -h z` of `solverKernel.lean` is the residue of the crossed pole.
-/

namespace Work.FatouL1

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- `Real.tanh` is continuous (Mathlib has no continuity lemma for `tanh`). -/
lemma continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y from
    funext (fun y => Real.tanh_eq_sinh_div_cosh y)]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun y => ne_of_gt (Real.cosh_pos y))

/-- **The vertical contour `Re s = Re z + 1/2` of the Cauchy–Heine solver.**

For `h` integrable along the vertical line through `Re z + 1/2`
(the line carrying the contour) and the standard boundary value
`cot (π (1/2 + y I)) = -I tanh (π y)` of the kernel, the truncated contour integrals
`I ∫_{-Y}^{Y} h (Re z + 1/2 + y I) (I/2) cot (π ((Re z + 1/2 + y I) - z))`
converge to `hcSolver h (z + 1)`. -/
theorem hcVerticalPlus {h : ℂ → ℂ} {z : ℂ}
    (hint : MeasureTheory.Integrable (fun y : ℝ => h (((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I)))
    (hcot : ∀ y : ℝ, Complex.cot (Real.pi * ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) = -Complex.I * (Real.tanh (Real.pi * y) : ℂ)) :
    Filter.Tendsto (fun Y : ℝ => Complex.I * ∫ y : ℝ in (-Y)..Y,
      h (((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I)
        * (Complex.I / 2 * Complex.cot (Real.pi * ((((z.re + 1 / 2 : ℝ) : ℂ) + y * Complex.I) - z))))
      Filter.atTop (nhds (Work.FatouL1.hcSolver h (z + 1))) := by
  -- Write `w := Re z + 1/2` for the real part of the contour.
  set w : ℂ := ((z.re + 1 / 2 : ℝ) : ℂ) with hw
  -- The limiting integrand: `h` on the contour, with the kernel `-I tanh (π (y - Im z))`.
  set f : ℝ → ℂ := fun y => h (w + y * Complex.I) * ((Real.tanh (Real.pi * (y - z.im))) : ℂ) with hf
  have hintw : MeasureTheory.Integrable (fun y : ℝ => h (w + y * Complex.I)) := by
    simpa only [hw] using hint
  have hcont : Continuous fun y : ℝ => ((Real.tanh (Real.pi * (y - z.im))) : ℂ) :=
    Complex.continuous_ofReal.comp
      (continuous_tanh.comp (continuous_const.mul (continuous_id.sub continuous_const)))
  have hfi : MeasureTheory.Integrable f := by
    rw [hf]
    refine hintw.mul_bdd (c := 1) hcont.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_tanh_le_one _
  -- Step 1: the boundary value of the kernel on the contour.
  have hpoint : ∀ y : ℝ, h (w + y * Complex.I) *
        (Complex.I / 2 * Complex.cot (Real.pi * ((w + y * Complex.I) - z))) = f y * (1 / 2) := by
    intro y
    rw [hf]
    have harg : Real.pi * ((w + y * Complex.I) - z) =
        Real.pi * ((1 / 2 : ℂ) + ((y - z.im : ℝ) : ℂ) * Complex.I) := by
      rw [hw]
      congr 1
      apply Complex.ext <;> simp
    rw [harg, hcot (y - z.im)]
    have hkey : Complex.I / 2 * (-Complex.I * ((Real.tanh (Real.pi * (y - z.im))) : ℂ)) =
        ((Real.tanh (Real.pi * (y - z.im))) : ℂ) * (1 / 2) := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hkey, mul_assoc]
  -- Step 2: the truncated integrals of the two integrands coincide meanwhile.
  have hLint : ∀ Y : ℝ,
      ∫ y : ℝ in (-Y)..Y, h (w + y * Complex.I) *
          (Complex.I / 2 * Complex.cot (Real.pi * ((w + y * Complex.I) - z)))
        = (∫ y : ℝ in (-Y)..Y, f y) * (1 / 2) := by
    intro Y
    rw [intervalIntegral.integral_congr (fun y _ => hpoint y)]
    exact intervalIntegral.integral_mul_const (1 / 2 : ℂ) f
  have hL2 : ∀ Y : ℝ, Complex.I * ∫ y : ℝ in (-Y)..Y, h (w + y * Complex.I) *
          (Complex.I / 2 * Complex.cot (Real.pi * ((w + y * Complex.I) - z)))
        = (Complex.I / 2) * ∫ y : ℝ in (-Y)..Y, f y := by
    intro y
    rw [hLint y]
    ring
  -- Step 3: `hcSolver h (z+1)` is the same integral, by the shift `y ↦ y + Im z`.
  have hpt2 : ∀ y : ℝ,
      h ((z + 1) - 1 / 2 + y * Complex.I) * ((Real.tanh (Real.pi * y)) : ℂ) = f (y + z.im) := by
    intro y
    simp only [hf]
    have hA : (z + 1) - 1 / 2 + y * Complex.I = w + ((y + z.im : ℝ) : ℂ) * Complex.I := by
      rw [hw]
      apply Complex.ext <;> simp <;> ring
    rw [hA]
    have ht : Real.tanh (Real.pi * y) = Real.tanh (Real.pi * ((y + z.im) - z.im)) := by
      congr 2
      ring
    rw [ht]
  have hRint : (∫ y : ℝ, h ((z + 1) - 1 / 2 + y * Complex.I) *
        ((Real.tanh (Real.pi * y)) : ℂ)) = ∫ y : ℝ, f y := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt2),
      MeasureTheory.integral_add_right_eq_self]
  have hR : Work.FatouL1.hcSolver h (z + 1) = (Complex.I / 2) * ∫ y : ℝ, f y := by
    rw [Work.FatouL1.hcSolver, hRint]
  -- Step 4: the truncated integrals converge to the full one.
  have hLim : Filter.Tendsto (fun Y : ℝ => ∫ y : ℝ in (-Y)..Y, f y) Filter.atTop
      (nhds (∫ y : ℝ, f y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hfi Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hLim2 : Filter.Tendsto (fun Y : ℝ => (Complex.I / 2) * ∫ y : ℝ in (-Y)..Y, f y)
      Filter.atTop (nhds ((Complex.I / 2) * ∫ y : ℝ, f y)) :=
    hLim.const_mul (Complex.I / 2)
  rw [hR]
  refine Filter.Tendsto.congr' ?_ hLim2
  exact Filter.Eventually.of_forall (fun Y => (hL2 Y).symm)

end

end Work.FatouL1
