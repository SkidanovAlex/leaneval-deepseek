import Mathlib
import Submission.Work.Pert.StripChart

/-!
# `Work.Pert.Strip` — elementary data of the strip chart `Work.Pert.stripChart`

For `h > 0` the chart

    Work.Pert.stripChart h ζ = (exp (i π ζ/(2h)) - 1) / (exp (i π ζ/(2h)) + 1)

of the vertical strip `|Re ζ| ≤ h` onto the closed unit disc is analysed through its
exponential factor `chartExp`, its modulus `chartR` and its argument `chartP`:

* `chartC h = i π/(2h)` is the coefficient in the exponent, `chartExp h ζ = exp (chartC h * ζ)`;
* `chartK h = π/(2h)` is the same coefficient as a real number, so `chartC h = i * chartK h`;
* `chartR h ζ = exp (-chartK h * ζ.im) = ‖chartExp h ζ‖`;
* `chartP h ζ = chartK h * ζ.re`, so that
  `chartExp h ζ = chartR h ζ * (cos (chartP h ζ) + i sin (chartP h ζ))`.
-/

namespace Work.Pert.Strip

noncomputable section

/-- The coefficient `k = π/(2h)` of the chart, as a complex number. -/
def chartC (h : ℝ) : ℂ := Complex.I * (Real.pi / (2 * h))

/-- The coefficient `k = π/(2h)` of the chart, as a real number. -/
def chartK (h : ℝ) : ℝ := Real.pi / (2 * h)

/-- The exponential factor `exp (i π ζ/(2h))` occurring in `Work.Pert.stripChart`. -/
def chartExp (h : ℝ) (ζ : ℂ) : ℂ := Complex.exp (chartC h * ζ)

/-- The modulus `exp (-k Im ζ)` of `chartExp h ζ`. -/
def chartR (h : ℝ) (ζ : ℂ) : ℝ := Real.exp (-(chartK h * ζ.im))

/-- The argument `k Re ζ` of `chartExp h ζ`. -/
def chartP (h : ℝ) (ζ : ℂ) : ℝ := chartK h * ζ.re

/-- The chart is the Cayley transform of its exponential factor. -/
lemma stripChart_eq_cayley (h : ℝ) (ζ : ℂ) :
    Work.Pert.stripChart h ζ = (chartExp h ζ - 1) / (chartExp h ζ + 1) := rfl

/-- `chartK` is positive for `h > 0`. -/
lemma chartK_pos {h : ℝ} (hh : 0 < h) : 0 < chartK h :=
  div_pos Real.pi_pos (by positivity)

/-- The complex coefficient is the imaginary unit times the real one. -/
lemma chartC_eq_ofReal (h : ℝ) : chartC h = Complex.I * ((chartK h : ℝ) : ℂ) := by
  simp only [chartC, chartK, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- The complex coefficient does not vanish for `h > 0`. -/
lemma chartC_ne_zero {h : ℝ} (hh : 0 < h) : chartC h ≠ 0 := by
  rw [chartC_eq_ofReal]
  exact mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (chartK_pos hh)))

/-- The exponential factor never vanishes. -/
lemma chartExp_ne_zero (h : ℝ) (ζ : ℂ) : chartExp h ζ ≠ 0 :=
  Complex.exp_ne_zero _

end

end Work.Pert.Strip
