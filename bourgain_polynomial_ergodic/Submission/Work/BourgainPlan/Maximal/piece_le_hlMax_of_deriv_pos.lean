import Mathlib
import Submission.Work.BourgainPlan.Maximal.dilation_hl
import Submission.Work.BourgainPlan.Maximal.piece_helpers
import Submission.Work.BourgainPlan.Maximal.lintegral_poly_piece_change_eq
import Submission.Work.BourgainPlan.Maximal.poly_piece_weight_lower_bound

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

open Commons.Analysis.Maximal (hlMax)

/-- Averages over an increasing polynomial piece are dominated by the Hardy–Littlewood maximal function anchored at the left endpoint value.  HINT: let `k := Polynomial.rootMultiplicity a (q - Polynomial.C (q.eval a))` and `s := (q - Polynomial.C (q.eval a)) /ₘ (Polynomial.X - Polynomial.C a)^k`, so `(X - C a)^k * s = q - C (q.eval a)` (`Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`) and `s.eval a ≠ 0` (`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`).  For `u ∈ (a,b]` the weight `q'(u) * (q(u) - q(a))^(1/k-1)` equals `s(u)^(1/k-1) * (k*s(u) + (u-a)*s'(u))`, which extends continuously to `[a,b]` with positive value `k * s(a)^(1/k)` at `a`; hence it is bounded below by some `c > 0` on `(a,b]`.  Then use `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` for `u ↦ q.eval u` on `(a,b]` (whose image is `Set.Ioc (q.eval a) (q.eval b)`) together with `Work.BourgainPlan.Maximal.dilation_weight_le_hlMax`. -/
theorem piece_le_hlMax_of_deriv_pos (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
        ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax ψ (x - q.eval a) := by
  obtain ⟨k, c, hk, hc, hW⟩ := poly_piece_weight_lower_bound q hab hderiv
  have ht : 0 < q.eval b - q.eval a := poly_eval_sub_pos q hab hderiv
  refine ⟨2 * ((k : ℝ) * (q.eval b - q.eval a) ^ ((k : ℝ)⁻¹)) / c, by positivity,
    fun ψ hψ x => ?_⟩
  -- insert the weight `q'(u) * (q u - q a)^{1/k-1} ≥ c` into the integral over `(a,b]`
  have h1 := setLIntegral_le_inv_mul_of_le_weight (μ := volume) (s := Set.Ioc a b)
    measurableSet_Ioc hc (fun u => ψ (x - q.eval u))
    (fun u => q.derivative.eval u * (q.eval u - q.eval a) ^ ((k : ℝ)⁻¹ - 1)) hW
  -- change of variables `s = q u - q a` followed by the dilation bound
  have h2 := lintegral_poly_piece_change_eq q hab hderiv hk ψ hψ x
  have h3 := dilation_weight_le_hlMax k hk ψ hψ ht (x - q.eval a)
  calc ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
      ≤ (ENNReal.ofReal c)⁻¹ * ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
          * ENNReal.ofReal
              (q.derivative.eval u * (q.eval u - q.eval a) ^ ((k : ℝ)⁻¹ - 1)) := h1
    _ = (ENNReal.ofReal c)⁻¹ * ∫⁻ s in Set.Ioc (0 : ℝ) (q.eval b - q.eval a),
          ψ (x - q.eval a - s) * ENNReal.ofReal (s ^ ((k : ℝ)⁻¹ - 1)) := by rw [h2]
    _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal
          (2 * ((k : ℝ) * (q.eval b - q.eval a) ^ ((k : ℝ)⁻¹)))
            * hlMax ψ (x - q.eval a)) := mul_le_mul_right h3 _
    _ = ENNReal.ofReal (2 * ((k : ℝ) * (q.eval b - q.eval a) ^ ((k : ℝ)⁻¹)) / c)
          * hlMax ψ (x - q.eval a) := by
        rw [← ENNReal.ofReal_inv_of_pos hc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_eq_mul_inv, mul_comm]

end Work.BourgainPlan.Maximal
