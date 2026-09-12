import Mathlib
import Submission.F_gauss
import Submission.F_freshlin
import Submission.LMProbs
import Submission.LMMeas
import Submission.ExpQuad
import Submission.VecGauss2

/-!
Gaussian step bound, quartic part (child task).

The lemma below is fully proved in this module.

Meaning: for a standard Gaussian `g` on `Vec n = EuclideanSpace ℝ (Fin n)`
(`stdGaussian (Vec n)`), for all real `a γ` and `u : Vec n`:

    ∫⁻ g, ofReal ((a + γ * vin g u)^4) = ofReal (a^4 + 6*a^2*γ^2*‖u‖^2 + 3*γ^4*‖u‖^4)

i.e. `E (a + γ⟨g,u⟩)⁴ = a⁴ + 6a²γ²‖u‖² + 3γ⁴‖u‖⁴`.  (If `V = ⟨g,u⟩` then
`E V = E V³ = 0`, `E V² = ‖u‖²`, `E V⁴ = 3‖u‖⁴`.)

RECIPE (all in `Submission.Discrepancy`; the same ideas are used in
`Submission/ExpQuad.lean`, which is imported and PROVED):

1. Let `X : Vec n → ℝ := fun g => vin g u` and `μ := stdGaussian (Vec n)`.

2. Moment values `μ[X ^ k] = ∫ g, (vin g u)^k ∂ μ` for k = 1..4 via the
   moment-generating function:
   - `iteratedDeriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) (k : ℕ) :
       iteratedDeriv k (mgf X μ) 0 = ∫ (g : Vec n), (X ^ k) g ∂ μ`
     (namespace `ProbabilityTheory`).
   - Show `mgf X μ = fun t : ℝ => Real.exp (‖u‖^2 * t^2 / 2)`:
     `mgf` unfolds to `∫ g, Real.exp (t * X g) ∂ μ` and
     `gauss_mgf n u t : (∫ g, Real.exp (t * vin g u) ∂ stdGaussian (Vec n)) =
       Real.exp (t ^ 2 * ‖u‖ ^ 2 / 2)` (from `Submission.F_gauss`; `ring` for
     `t^2*‖u‖^2/2 = ‖u‖^2*t^2/2`).
   - `0 ∈ interior (integrableExpSet X μ)`: show `integrableExpSet X μ = Set.univ`
     via `integrable_mgf_exp n u t` from `Submission.F_freshlin`, then `simp`.
   - Iterated derivatives at 0 of `t ↦ Real.exp (c * t^2 / 2)` are in the
     PROVED module `Submission.ExpQuad` (namespace `Submission.Discrepancy`):
       `iter1_eqf_zero c : ... 0 = 0`, `iter2_eqf_zero c : ... = c`,
       `iter3_eqf_zero c : ... = 0`, `iter4_eqf_zero c : ... = 3 * c^2`.
     Use with `c := ‖u‖^2`.  So:
       m1 : ∫ g, vin g u ∂μ = 0
       m2 : ∫ g, (vin g u)^2 ∂μ = ‖u‖^2
       m3 : ∫ g, (vin g u)^3 ∂μ = 0
       m4 : ∫ g, (vin g u)^4 ∂μ = 3 * ‖u‖^4
   CAREFUL: `iteratedDeriv_mgf_zero`'s RHS is `∫ (g : Vec n), (X ^ k) g ∂ μ`
   (pointwise power function `X ^ k`).

3. Integrability: prove
       hInt : ∀ k : ℕ, k ≤ 4 → Integrable (fun g : Vec n => (vin g u)^k) μ
   - Bound pointwise: for real `x`, `|x|^k ≤ |x|^4 + 1` when `k ≤ 4`, and
     `|x|^4 ≤ 24 * (Real.exp x + Real.exp (-x))` (a generous constant is fine;
     split on `0 ≤ x` and use e.g. `x^4 ≤ 24*Real.exp x`, the negative side by
     symmetry).  Use `Integrable.mono` with dominating function
     `fun g => 24 * (Real.exp (vin g u) + Real.exp (-(vin g u))) + 1`;
     integrability from `integrable_mgf_exp n u 1`, `integrable_mgf_exp n u (-1)`
     and constants (probability measure).  Measurability of `(vin g u)^k` via
     `(continuous_pow k).measurable.comp (measurable_vin n u)`.
   - Also `Integrable (fun g => (a + γ * vin g u)^4)` for the final step (bound
     `|a + γX|^4 ≤ 8*(a^4 + γ^4*|X|^4) ≤ 8a^4 + 8γ^4*(|X|^4+1)` etc., or
     `Integrable.mono` with the same dominating family).

4. Exact shifted integral (real):
       hshift : (∫ g, (a + γ * vin g u)^4 ∂ μ)
          = a^4 + 6*a^2*γ^2*‖u‖^2 + 3*γ^4*‖u‖^4
   - Expand the fourth power (pointwise, `ring`), rewrite the integral of the
     sum of the five monomials using `MeasureTheory.integral_add` /
     `MeasureTheory.integral_sub` (all pieces integrable), plug in m1..m4
     (odd moments vanish).  Constants integrate to themselves (probability
     measure; e.g. `simp` after `rw [lintegral_const]` if you go through
     lintegral, or `MeasureTheory.integral_const`).

5. Convert to the lintegral (ENNReal) equality:
       ∫⁻ g, ofReal ((a + γ * vin g u)^4) ∂ μ = ofReal (a^4 + 6*a^2*γ^2*‖u‖^2 + 3*γ^4*‖u‖^4)
   - integrand ≥ 0 everywhere (4th power): `ae_of_all`; integrable (step 3).
     Use `MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn`, rw
     [hshift], congr.

USEFUL FACTS (namespaces):
  - `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (as used in
    `Submission/F_freshlin.lean`).
  - `measurable_vin n u` (Submission.LMAux), `(continuous_pow k).measurable`.
  - `ae_of_all μ`, `MeasureTheory.Integrable.mono`.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- Third moment of a linear functional of the standard Gaussian vanishes. -/
lemma gauss_lin_mom3 (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, (vin g u) ^ 3 ∂(stdGaussian (Vec n))) = 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun g : Vec n => vin g u)
    (μ := (stdGaussian (Vec n))) (gauss_lin_memExpSet n u) 3
  calc
    (∫ g : Vec n, (vin g u) ^ 3 ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n, ((fun g : Vec n => vin g u) ^ 3) g ∂(stdGaussian (Vec n)) := rfl
    _ = iteratedDeriv 3 (mgf (fun g : Vec n => vin g u) (stdGaussian (Vec n))) 0 := h.symm
    _ = 0 := by
            rw [gauss_lin_mgf]
            exact iter3_eqf_zero (‖u‖ ^ 2)

/-- Fourth moment of a linear functional of the standard Gaussian. -/
lemma gauss_lin_mom4 (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, (vin g u) ^ 4 ∂(stdGaussian (Vec n))) = 3 * ‖u‖ ^ 4 := by
  have h := iteratedDeriv_mgf_zero (X := fun g : Vec n => vin g u)
    (μ := (stdGaussian (Vec n))) (gauss_lin_memExpSet n u) 4
  calc
    (∫ g : Vec n, (vin g u) ^ 4 ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n, ((fun g : Vec n => vin g u) ^ 4) g ∂(stdGaussian (Vec n)) := rfl
    _ = iteratedDeriv 4 (mgf (fun g : Vec n => vin g u) (stdGaussian (Vec n))) 0 := h.symm
    _ = 3 * ‖u‖ ^ 4 := by
            rw [gauss_lin_mgf]
            have hval := iter4_eqf_zero (‖u‖ ^ 2)
            exact hval.trans (by congr 1; ring)

/-- Quartic Gaussian step bound (lintegral form). -/
lemma gauss_quartic_lin (n : ℕ) (a γ : ℝ) (u : Vec n) :
    (∫⁻ g : Vec n, ENNReal.ofReal ((a + γ * vin g u) ^ 4) ∂(stdGaussian (Vec n))) =
      ENNReal.ofReal (a ^ 4 + 6 * a ^ 2 * γ ^ 2 * ‖u‖ ^ 2 + 3 * γ ^ 4 * ‖u‖ ^ 4) := by
  have hq : ∀ g : Vec n, (a + γ * vin g u) ^ 4
      = a ^ 4 + (4 * a ^ 3 * γ) * (vin g u) + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2
        + (4 * a * γ ^ 3) * (vin g u) ^ 3 + γ ^ 4 * (vin g u) ^ 4 := by
    intro g
    ring
  have hshift : (∫ g : Vec n, (a + γ * vin g u) ^ 4 ∂(stdGaussian (Vec n)))
      = a ^ 4 + 6 * a ^ 2 * γ ^ 2 * ‖u‖ ^ 2 + 3 * γ ^ 4 * ‖u‖ ^ 4 := by
    -- integral of the five-term sum
    have hX1 : Integrable (fun g : Vec n => (vin g u) ^ 1) (stdGaussian (Vec n)) := gauss_lin_int n u 1
    have hX2 : Integrable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) := gauss_lin_int n u 2
    have hX3 : Integrable (fun g : Vec n => (vin g u) ^ 3) (stdGaussian (Vec n)) := gauss_lin_int n u 3
    have hX4 : Integrable (fun g : Vec n => (vin g u) ^ 4) (stdGaussian (Vec n)) := gauss_lin_int n u 4
    have hc0 : Integrable (fun g : Vec n => a ^ 4) (stdGaussian (Vec n)) := by
      simpa using (MeasureTheory.integrable_const : Integrable (fun g : Vec n => a ^ 4)
        (stdGaussian (Vec n)))
    have hc1 : Integrable (fun g : Vec n => (4 * a ^ 3 * γ) * (vin g u)) (stdGaussian (Vec n)) := by
      simpa [pow_one] using hX1.const_mul (4 * a ^ 3 * γ)
    have hc2 : Integrable (fun g : Vec n => (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2) (stdGaussian (Vec n)) :=
      hX2.const_mul (6 * a ^ 2 * γ ^ 2)
    have hc3 : Integrable (fun g : Vec n => (4 * a * γ ^ 3) * (vin g u) ^ 3) (stdGaussian (Vec n)) :=
      hX3.const_mul (4 * a * γ ^ 3)
    have hc4 : Integrable (fun g : Vec n => γ ^ 4 * (vin g u) ^ 4) (stdGaussian (Vec n)) :=
      hX4.const_mul (γ ^ 4)
    have hs01 : Integrable (fun g : Vec n => a ^ 4 + (4 * a ^ 3 * γ) * (vin g u))
        (stdGaussian (Vec n)) := hc0.add hc1
    have hs012 : Integrable (fun g : Vec n => a ^ 4 + (4 * a ^ 3 * γ) * (vin g u)
        + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2) (stdGaussian (Vec n)) := hs01.add hc2
    have hs0123 : Integrable (fun g : Vec n => a ^ 4 + (4 * a ^ 3 * γ) * (vin g u)
        + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 + (4 * a * γ ^ 3) * (vin g u) ^ 3)
        (stdGaussian (Vec n)) := hs012.add hc3
    calc
      (∫ g : Vec n, (a + γ * vin g u) ^ 4 ∂(stdGaussian (Vec n)))
          = ∫ g : Vec n, a ^ 4 + (4 * a ^ 3 * γ) * (vin g u)
              + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 + (4 * a * γ ^ 3) * (vin g u) ^ 3
              + γ ^ 4 * (vin g u) ^ 4 ∂(stdGaussian (Vec n)) := by
              congr 1
              funext g
              rw [hq g]
      _ = (∫ g : Vec n, a ^ 4 + (4 * a ^ 3 * γ) * (vin g u)
            + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 + (4 * a * γ ^ 3) * (vin g u) ^ 3
            ∂(stdGaussian (Vec n)))
            + ∫ g : Vec n, γ ^ 4 * (vin g u) ^ 4 ∂(stdGaussian (Vec n)) := by
              rw [integral_add hs0123 hc4]
      _ = (∫ g : Vec n, a ^ 4 + (4 * a ^ 3 * γ) * (vin g u)
            + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 ∂(stdGaussian (Vec n)))
            + ∫ g : Vec n, (4 * a * γ ^ 3) * (vin g u) ^ 3 ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, γ ^ 4 * (vin g u) ^ 4 ∂(stdGaussian (Vec n)) := by
              rw [integral_add hs012 hc3]
      _ = (∫ g : Vec n, a ^ 4 + (4 * a ^ 3 * γ) * (vin g u) ∂(stdGaussian (Vec n)))
            + ∫ g : Vec n, (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, (4 * a * γ ^ 3) * (vin g u) ^ 3 ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, γ ^ 4 * (vin g u) ^ 4 ∂(stdGaussian (Vec n)) := by
              rw [integral_add hs01 hc2]
      _ = (∫ g : Vec n, a ^ 4 ∂(stdGaussian (Vec n)))
            + ∫ g : Vec n, (4 * a ^ 3 * γ) * (vin g u) ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, (4 * a * γ ^ 3) * (vin g u) ^ 3 ∂(stdGaussian (Vec n))
            + ∫ g : Vec n, γ ^ 4 * (vin g u) ^ 4 ∂(stdGaussian (Vec n)) := by
              rw [integral_add hc0 hc1]
      _ = a ^ 4 + 6 * a ^ 2 * γ ^ 2 * ‖u‖ ^ 2 + 3 * γ ^ 4 * ‖u‖ ^ 4 := by
              rw [MeasureTheory.integral_const_mul (4 * a ^ 3 * γ) (fun g : Vec n => vin g u)]
              rw [MeasureTheory.integral_const_mul (6 * a ^ 2 * γ ^ 2) (fun g : Vec n => (vin g u) ^ 2)]
              rw [MeasureTheory.integral_const_mul (4 * a * γ ^ 3) (fun g : Vec n => (vin g u) ^ 3)]
              rw [MeasureTheory.integral_const_mul (γ ^ 4) (fun g : Vec n => (vin g u) ^ 4)]
              rw [gauss_lin_mom1, gauss_lin_mom2, gauss_lin_mom3, gauss_lin_mom4]
              simp
              ring
  have hint : Integrable (fun g : Vec n => (a + γ * vin g u) ^ 4) (stdGaussian (Vec n)) := by
    have hX1 : Integrable (fun g : Vec n => |vin g u|) (stdGaussian (Vec n)) := by
      simpa using (integrable_pow_abs_of_mem_interior_integrableExpSet (gauss_lin_memExpSet n u) 1)
    have hX3 : Integrable (fun g : Vec n => |vin g u| ^ 3) (stdGaussian (Vec n)) := by
      simpa using (integrable_pow_abs_of_mem_interior_integrableExpSet (gauss_lin_memExpSet n u) 3)
    have hX2 : Integrable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) := gauss_lin_int n u 2
    have hX4 : Integrable (fun g : Vec n => (vin g u) ^ 4) (stdGaussian (Vec n)) := gauss_lin_int n u 4
    have hc0 : Integrable (fun g : Vec n => a ^ 4) (stdGaussian (Vec n)) := by
      simpa using (MeasureTheory.integrable_const : Integrable (fun g : Vec n => a ^ 4)
        (stdGaussian (Vec n)))
    have hdom : Integrable (fun g : Vec n => a ^ 4 + |4 * a ^ 3 * γ| * |vin g u|
        + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 + |4 * a * γ ^ 3| * |vin g u| ^ 3
        + γ ^ 4 * (vin g u) ^ 4) (stdGaussian (Vec n)) := by
      exact (((hc0.add (hX1.const_mul (|4 * a ^ 3 * γ|))).add (hX2.const_mul (6 * a ^ 2 * γ ^ 2))).add
        (hX3.const_mul (|4 * a * γ ^ 3|))).add (hX4.const_mul (γ ^ 4))
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact (measurable_shift_pow n u a γ 4).aestronglyMeasurable
    · filter_upwards with g
      have h2 : (4 * a ^ 3 * γ) * (vin g u) ≤ |4 * a ^ 3 * γ| * |vin g u| := by
        calc
          (4 * a ^ 3 * γ) * (vin g u) ≤ |(4 * a ^ 3 * γ) * (vin g u)| := le_abs_self _
          _ = |4 * a ^ 3 * γ| * |vin g u| := by rw [abs_mul]
      have h4 : (4 * a * γ ^ 3) * (vin g u) ^ 3 ≤ |4 * a * γ ^ 3| * |vin g u| ^ 3 := by
        calc
          (4 * a * γ ^ 3) * (vin g u) ^ 3 ≤ |(4 * a * γ ^ 3) * (vin g u) ^ 3| := le_abs_self _
          _ = |4 * a * γ ^ 3| * |(vin g u) ^ 3| := by rw [abs_mul]
          _ = |4 * a * γ ^ 3| * |vin g u| ^ 3 := by rw [abs_pow]
      have hmain : (a + γ * vin g u) ^ 4 ≤ a ^ 4 + |4 * a ^ 3 * γ| * |vin g u|
          + (6 * a ^ 2 * γ ^ 2) * (vin g u) ^ 2 + |4 * a * γ ^ 3| * |vin g u| ^ 3
          + γ ^ 4 * (vin g u) ^ 4 := by
        rw [hq g]
        nlinarith
      have hpow4 : ∀ y : ℝ, |y| ^ 4 = y ^ 4 := by
        intro y
        rw [show |y| ^ 4 = (|y| ^ 2) ^ 2 by ring]
        rw [show y ^ 4 = (y ^ 2) ^ 2 by ring]
        rw [sq_abs]
      rw [Real.norm_eq_abs]
      rw [abs_pow]
      rw [hpow4]
      exact hmain
  have hnn : 0 ≤ᵐ[stdGaussian (Vec n)] (fun g : Vec n => (a + γ * vin g u) ^ 4) :=
    ae_of_all _ (fun g => by positivity)
  have hlin := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [hshift] at hlin
  exact hlin.symm

end Discrepancy
