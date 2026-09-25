import Mathlib
import Submission.Work.BourgainPlan.Maximal.dilation_hl

namespace Work.BourgainPlan.Maximal

open MeasureTheory ENNReal

set_option linter.unusedVariables false

/-- Change of variables for a polynomial piece on which the derivative is bounded below: the integral of `ψ (x - q u)` over `(a,b]` is at most `1/m` times the integral of `ψ (x - v)` over the image of `(a,b]` under `q`.  HINT: `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` gives `∫⁻ v in q '' (a,b], ψ (x - v) = ∫⁻ u in (a,b], ENNReal.ofReal |q' u| * ψ (x - q u)`, and `|q' u| ≥ m > 0` on `(a,b]` (injectivity of `q` on `(a,b]` follows from the lower bound on the derivative). -/
theorem flat_piece_le_hlMax (q : Polynomial ℝ) {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hderiv : ∀ u ∈ Set.Icc a b, m ≤ q.derivative.eval u) :
    ∀ (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
        ≤ (ENNReal.ofReal m)⁻¹
            * ∫⁻ v in (fun u : ℝ => q.eval u) '' Set.Ioc a b, ψ (x - v) := by
  intro ψ hψ x
  set s := Set.Ioc a b with hs_def
  have hs : MeasurableSet s := measurableSet_Ioc
  -- `q` has derivative `q'` on `s`, and `q' ≥ m > 0` there, so `q` is strictly increasing on `s`.
  have hdw : ∀ u ∈ s, HasDerivWithinAt (fun u : ℝ => q.eval u) (q.derivative.eval u) s u :=
    fun u _ => (q.hasDerivAt u).hasDerivWithinAt
  have hmono : MonotoneOn (fun u : ℝ => q.eval u) s := by
    have hcont : ContinuousOn (fun u : ℝ => q.eval u) s := q.continuous.continuousOn
    have hpos : ∀ u ∈ interior s, 0 < deriv (fun u : ℝ => q.eval u) u := by
      intro u hu
      rw [Polynomial.deriv]
      exact lt_of_lt_of_le hm (hderiv u (Set.Ioc_subset_Icc_self (interior_subset hu)))
    exact (strictMonoOn_of_deriv_pos (convex_Ioc a b) hcont hpos).monotoneOn
  -- The one-dimensional change of variables formula.
  have hchange := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hdw hmono
      (fun v : ℝ => ψ (x - v))
  have hinv : (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal m = 1 :=
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm)) ENNReal.ofReal_ne_top
  have hmeas_g : Measurable
      (fun u : ℝ => ENNReal.ofReal (q.derivative.eval u) * ψ (x - q.eval u)) := by
    fun_prop
  calc ∫⁻ u in s, ψ (x - q.eval u)
      = ∫⁻ u in s, (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * ψ (x - q.eval u)) := by
        apply setLIntegral_congr_fun hs
        intro u _
        simp only [← mul_assoc, hinv, one_mul]
    _ = (ENNReal.ofReal m)⁻¹ * ∫⁻ u in s, ENNReal.ofReal m * ψ (x - q.eval u) := by
        apply lintegral_const_mul
        fun_prop
    _ ≤ (ENNReal.ofReal m)⁻¹ * ∫⁻ u in s, ENNReal.ofReal (q.derivative.eval u) * ψ (x - q.eval u) := by
        apply mul_le_mul_right
        · apply setLIntegral_mono hmeas_g
          intro u hu
          have hmu : m ≤ q.derivative.eval u := hderiv u ⟨hu.1.le, hu.2⟩
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hmu) le_rfl
    _ = (ENNReal.ofReal m)⁻¹ * ∫⁻ v in (fun u : ℝ => q.eval u) '' s, ψ (x - v) := by
        rw [hchange]

end Work.BourgainPlan.Maximal
