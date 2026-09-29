import Mathlib

/-!
# Jensen's inequality for the logarithmic Mahler measure of a polynomial

For a complex polynomial `p` with `p(0) ≠ 0`, the logarithm of `‖p 0‖` is at most the
average of `log ‖p‖` over the unit circle (Jensen's formula for polynomials, in the weak
form of an inequality).  Here `Work.TMLECore.jensen_poly` states this with the unit circle
parametrised as `x ↦ exp (2 * π * I * x)` for `x ∈ [0,1]`.

The proof reduces the statement to two facts about the (logarithmic) Mahler measure that
Mathlib already provides:
* `Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`, and
* `Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`,
together with the elementary relation `p 0 = leadingCoeff p * ∏ (roots of p)`.
-/

namespace Work.TMLECore

open Polynomial Real Complex

/-- The norm of a product of a multiset of complex numbers is the product of the norms. -/
private lemma norm_multiset_prod_complex (m : Multiset ℂ) : ‖m.prod‖ = (m.map norm).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih]

/-- The constant term of a polynomial as leading coefficient times the product of the
(negated) roots. -/
private lemma eval_zero_eq_leadingCoeff_mul_prod_neg_roots (p : ℂ[X]) :
    Polynomial.eval 0 p = p.leadingCoeff * (p.roots.map (fun a => -a)).prod := by
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
  have : (Multiset.map (eval 0 ∘ fun x => X - C x) p.roots) = (p.roots.map (fun a => -a)) := by
    apply Multiset.map_congr rfl
    intro a ha
    simp [Polynomial.eval_sub]
  rw [this]

/-- The norm of the constant term of a polynomial is at most its Mahler measure. -/
private lemma norm_eval_zero_le_mahlerMeasure (p : ℂ[X]) :
    ‖Polynomial.eval 0 p‖ ≤ p.mahlerMeasure := by
  rw [eval_zero_eq_leadingCoeff_mul_prod_neg_roots,
    Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, norm_mul]
  have hnorm : ‖(p.roots.map (fun a => -a)).prod‖ = (p.roots.map (fun a => ‖a‖)).prod := by
    rw [norm_multiset_prod_complex, Multiset.map_map]
    have hmap : (Multiset.map (Norm.norm ∘ fun a => -a) p.roots)
        = p.roots.map (fun a => ‖a‖) := by
      apply Multiset.map_congr rfl
      intro a ha
      simp
    rw [hmap]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Multiset.prod_map_le_prod_map₀ (fun a => ‖a‖) (fun a => max 1 ‖a‖)
    (fun i _ => norm_nonneg i) (fun i _ => le_max_right 1 ‖i‖)

/-- `log ‖p 0‖ ≤ logMahlerMeasure p` whenever `p 0 ≠ 0`. -/
private lemma log_eval_zero_le_logMahlerMeasure (p : ℂ[X]) (h0 : Polynomial.eval 0 p ≠ 0) :
    Real.log ‖Polynomial.eval 0 p‖ ≤ p.logMahlerMeasure := by
  rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr h0) (norm_eval_zero_le_mahlerMeasure p)

/-- The logarithmic Mahler measure, computed as the interval integral over the unit circle. -/
private lemma logMahlerMeasure_eq_integral (p : ℂ[X]) :
    p.logMahlerMeasure =
      ∫ x in (0:ℝ)..1, Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖ := by
  rw [Polynomial.logMahlerMeasure_def, circleAverage_def]
  set g : ℝ → ℝ := fun θ => Real.log ‖Polynomial.eval (Complex.exp (θ * Complex.I)) p‖ with hg
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hstep : (∫ θ in (0:ℝ)..(2 * Real.pi),
        Real.log ‖Polynomial.eval (circleMap (0:ℂ) 1 θ) p‖)
      = ∫ θ in (0:ℝ)..(2 * Real.pi), g θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [hg]
    rw [circleMap]
    simp
  rw [hstep]
  have hcomp : ∫ x in (0:ℝ)..1, g (2 * Real.pi * x)
      = (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), g θ := by
    rw [intervalIntegral.integral_comp_mul_left g hc]
    simp
  rw [← hcomp]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [hg]
  congr 3
  push_cast
  ring_nf

theorem jensen_poly (p : Polynomial ℂ) (h0 : Polynomial.eval 0 p ≠ 0) :
    Real.log ‖Polynomial.eval 0 p‖ ≤
      ∫ x in (0 : ℝ)..1, Real.log ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) p‖ := by
  rw [← logMahlerMeasure_eq_integral p]
  exact log_eval_zero_le_logMahlerMeasure p h0

end Work.TMLECore
