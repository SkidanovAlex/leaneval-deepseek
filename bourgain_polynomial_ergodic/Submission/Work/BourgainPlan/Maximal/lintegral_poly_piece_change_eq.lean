import Mathlib
import Submission.Work.BourgainPlan.Maximal.piece_helpers

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedVariables false

/-- **Change of variables along a polynomial piece.**  For a polynomial `q` with `q' > 0` on
`(a,b]`, `a < b`, an integer `k ≥ 1`, a measurable `ψ : ℝ → ℝ≥0∞` and a real `x`, the weighted
integral of `ψ (x - q u)` over `(a,b]` equals the integral of `ψ (x - q a - s) · s^{1/k-1}` over
`(0, q b - q a]`.

HINT: `u ↦ q.eval u` is strictly increasing on `[a,b]` (`Work.BourgainPlan.Maximal.poly_strictMonoOn_Icc_of_deriv_pos` in the imported helpers module, hence injective) with image
`(q a, q b]` (`Work.BourgainPlan.Maximal.image_Ioc_poly_eval`), so
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` applied to
`G v := ψ (x - v) * ENNReal.ofReal ((v - q.eval a) ^ ((k:ℝ)⁻¹ - 1))` gives
`∫_{v ∈ (q a, q b]} G v = ∫_{u ∈ (a,b]} ofReal |q' u| * G (q u)`;
since `q' u > 0` and `q u - q a > 0` on `(a,b]`, the right-hand side is
`∫_{u ∈ (a,b]} ψ (x - q u) * ofReal (q' u * (q u - q a)^((k:ℝ)⁻¹-1))` (via `ENNReal.ofReal_mul`
and the positivity of both factors).  Finally reindex the left-hand side with `v = q a + s`, i.e.
apply `lintegral_image_eq_lintegral_abs_deriv_mul` a second time to `s ↦ q.eval a + s` on
`(0, q b - q a]` (derivative `1`, image `(q a, q b]`).  A single application to
`u ↦ q.eval u - q.eval a` on `(a,b]` (image `(0, q b - q a]`) also works. -/
theorem lintegral_poly_piece_change_eq (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u)
    {k : ℕ} (hk : 0 < k) (ψ : ℝ → ENNReal) (hψ : Measurable ψ) (x : ℝ) :
    ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
        * ENNReal.ofReal (q.derivative.eval u * (q.eval u - q.eval a) ^ ((k : ℝ)⁻¹ - 1))
      = ∫⁻ s in Set.Ioc (0 : ℝ) (q.eval b - q.eval a),
          ψ (x - q.eval a - s) * ENNReal.ofReal (s ^ ((k : ℝ)⁻¹ - 1)) := by
  have hmono : StrictMonoOn (fun u => q.eval u) (Set.Icc a b) :=
    poly_strictMonoOn_Icc_of_deriv_pos q hderiv
  -- the substitution map `u ↦ q u - q a` is injective and has image `(0, q b - q a]`
  have hinj : Set.InjOn (fun u : ℝ => q.eval u - q.eval a) (Set.Ioc a b) := by
    intro u hu v hv huv
    simp only at huv
    exact hmono.injOn ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩ (by linarith)
  have hderiv' : ∀ u ∈ Set.Ioc a b,
      HasDerivWithinAt (fun u : ℝ => q.eval u - q.eval a) (q.derivative.eval u) (Set.Ioc a b) u :=
    fun u _ => ((Polynomial.hasDerivAt q u).sub_const _).hasDerivWithinAt
  have himg1 : (fun u => q.eval u) '' Set.Ioc a b = Set.Ioc (q.eval a) (q.eval b) :=
    image_Ioc_poly_eval q hab.le hmono
  have himg : (fun u : ℝ => q.eval u - q.eval a) '' Set.Ioc a b
      = Set.Ioc (0 : ℝ) (q.eval b - q.eval a) := by
    rw [show (fun u : ℝ => q.eval u - q.eval a)
        = (fun v : ℝ => v - q.eval a) ∘ (fun u => q.eval u) from rfl,
      Set.image_comp, himg1, Set.image_sub_const_Ioc]
    norm_num
  -- change of variables `v = q u - q a`, with weight `v ^ (1/k - 1)`
  have hchange := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (s := Set.Ioc a b) measurableSet_Ioc hderiv' hinj
      (fun v : ℝ => ψ (x - q.eval a - v) * ENNReal.ofReal (v ^ ((k : ℝ)⁻¹ - 1)))
  rw [himg] at hchange
  rw [hchange]
  -- pointwise identification of the two integrands on `(a,b]`
  refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  have hq' : 0 < q.derivative.eval u := hderiv u hu
  have harg : x - q.eval a - (q.eval u - q.eval a) = x - q.eval u := by ring
  rw [harg, abs_of_pos hq', ENNReal.ofReal_mul hq'.le]
  exact mul_left_comm _ _ _

end Work.BourgainPlan.Maximal
