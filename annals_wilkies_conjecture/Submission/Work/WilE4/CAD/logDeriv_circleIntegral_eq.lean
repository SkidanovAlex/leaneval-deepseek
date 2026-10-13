import Mathlib
import Submission.Work.WilE4.CAD.circleIntegral_multiset_sum_inv
import Submission.Work.WilE4.CAD.hasDerivAt_multiset_prod_sub

namespace Work.WilE4.CAD

open Polynomial MeasureTheory

/-- Evaluation of a complex polynomial in terms of its roots: for `ℂ` (algebraically closed)
every polynomial splits, so `p z = leadingCoeff · ∏_{a ∈ p.roots} (z - a)` where the product
runs over the multiset of roots, i.e. with multiplicities. -/
theorem eval_eq_leadingCoeff_mul_prod_roots (p : Polynomial ℂ) (z : ℂ) :
    p.eval z = p.leadingCoeff * (p.roots.map (fun a => z - a)).prod := by
  have hcard : p.roots.card = p.natDegree := by
    rw [← Polynomial.splits_iff_card_roots]; exact IsAlgClosed.splits p
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (R := ℂ) hcard
  have h1 := congrArg (fun q : Polynomial ℂ => Polynomial.eval z q) h
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod] at h1
  have hmap : (Multiset.map (Polynomial.eval z)
        (Multiset.map (fun a => Polynomial.X - Polynomial.C a) p.roots))
      = Multiset.map (fun a => z - a) p.roots := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl (fun a _ => by simp)
  rw [hmap] at h1
  exact h1.symm

/-- The logarithmic derivative of a complex polynomial, written as a sum of simple poles at
its roots (with multiplicity):  `p'(z)/p(z) = ∑_{a ∈ p.roots} (z - a)⁻¹` whenever `p z ≠ 0`. -/
theorem derivative_eval_div_eval_eq_sum_roots (p : Polynomial ℂ) {z : ℂ} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z = (p.roots.map (fun a => (z - a)⁻¹)).sum := by
  have hne : ∀ a ∈ p.roots, z ≠ a := by
    intro a ha hEq
    have ha0 : p.eval a = 0 := Polynomial.IsRoot.def.mp (Polynomial.mem_roots'.1 ha).2
    exact hz (by rw [hEq]; exact ha0)
  have hd1 : HasDerivAt (fun w : ℂ => p.leadingCoeff * (p.roots.map (fun a => w - a)).prod)
      (p.leadingCoeff * ((p.roots.map (fun a => z - a)).prod *
        (p.roots.map (fun a => (z - a)⁻¹)).sum)) z :=
    (hasDerivAt_multiset_prod_sub p.roots z hne).const_mul p.leadingCoeff
  have hd2 : HasDerivAt (fun w : ℂ => p.eval w) (p.derivative.eval z) z :=
    Polynomial.hasDerivAt p z
  have hfun : (fun w : ℂ => p.eval w)
      = fun w => p.leadingCoeff * (p.roots.map (fun a => w - a)).prod :=
    funext (fun w => eval_eq_leadingCoeff_mul_prod_roots p w)
  rw [hfun] at hd2
  have huniq := hd2.unique hd1
  have hmul : p.leadingCoeff * ((p.roots.map (fun a => z - a)).prod *
      (p.roots.map (fun a => (z - a)⁻¹)).sum)
      = p.eval z * (p.roots.map (fun a => (z - a)⁻¹)).sum := by
    rw [eval_eq_leadingCoeff_mul_prod_roots p z]; ring
  rw [huniq, hmul, mul_div_cancel_left₀ _ hz]

/-- **Argument principle for a polynomial** (logarithmic derivative form): if `p : ℂ[X]` has no
zero on the circle `C(c, R)`, then the contour integral of `p'/p` along that circle equals
`2πi` times the number of zeros of `p` inside the circle, counted with multiplicity. -/
theorem logDeriv_circleIntegral_eq (p : Polynomial ℂ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hno : ∀ z : ℂ, dist z c = R → p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z)
      = 2 * Real.pi * Complex.I * ((p.roots.filter (fun z : ℂ => dist z c < R)).card : ℂ) := by
  have hcongr : (∮ z in C(c, R), p.derivative.eval z / p.eval z)
      = ∮ z in C(c, R), (p.roots.map (fun a => (z - a)⁻¹)).sum :=
    circleIntegral.integral_congr hR.le
      (fun z hz => derivative_eval_div_eval_eq_sum_roots p (hno z hz))
  have hroots_ne : ∀ a ∈ p.roots, dist a c ≠ R := by
    intro a ha hda
    exact hno a hda (Polynomial.IsRoot.def.mp (Polynomial.mem_roots'.1 ha).2)
  rw [hcongr, circleIntegral_multiset_sum_inv p.roots c hR hroots_ne]

end Work.WilE4.CAD
