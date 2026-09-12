import Mathlib
import Submission.F_gauss
import Submission.F_freshlin
import Submission.LMProbs
import Submission.LMMeas
import Submission.ExpQuad

/-!
Gaussian step bound, quadratic part (child task).

The lemma below is fully proved in this module.

Meaning: for a standard Gaussian `g` on `Vec n = EuclideanSpace ℝ (Fin n)`
(`stdGaussian (Vec n)`), for all real `a γ` and `u : Vec n`:

    ∫⁻ g, ofReal ((a + γ * vin g u)^2) = ofReal (a^2 + γ^2 * ‖u‖^2)

i.e. `E (a + γ⟨g,u⟩)² = a² + γ²‖u‖²`.  (If `V = ⟨g,u⟩` then `E V = 0` and
`E V² = ‖u‖²`.)  This is the quadratic Gaussian step bound used by the
fourth-moment induction.

RECIPE (all in `Submission.Discrepancy`; the same ideas are used in
`Submission/ExpQuad.lean`, which is imported and PROVED):

1. Let `X : Vec n → ℝ := fun g => vin g u` and `μ := stdGaussian (Vec n)`.

2. Moment values `μ[X ^ k] = ∫ g, (vin g u)^k ∂ μ` for k = 1..4 via the
   moment-generating function:
   - `iteratedDeriv_mgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) (k : ℕ) :
       iteratedDeriv k (mgf X μ) 0 = ∫ (g : Vec n), (X ^ k) g ∂ μ`
     (namespace `ProbabilityTheory`).
   - Show `mgf X μ = fun t : ℝ => Real.exp (‖u‖^2 * t^2 / 2)`:
     `mgf` unfolds to the integral `∫ g, Real.exp (t * X g) ∂ μ` and
     `gauss_mgf n u t : (∫ g, Real.exp (t * vin g u) ∂ stdGaussian (Vec n)) =
       Real.exp (t ^ 2 * ‖u‖ ^ 2 / 2)` (from `Submission.F_gauss`; note the
     RHS `t^2 * ‖u‖^2 / 2` equals `‖u‖^2 * t^2 / 2` by `ring`).
   - `0 ∈ interior (integrableExpSet X μ)`: show `integrableExpSet X μ = Set.univ`
     using `integrable_mgf_exp (n) (u) (t)` from `Submission.F_freshlin`
     (`Integrable (fun g => Real.exp (t * vin g u)) (stdGaussian (Vec n))`);
     then `simp`.
   - The iterated derivatives at 0 of `t ↦ Real.exp (c * t^2 / 2)` are provided
     (PROVED) in `Submission.ExpQuad` (namespace `Submission.Discrepancy`):
       `iter1_eqf_zero c : iteratedDeriv 1 (fun t => Real.exp (c * t^2/2)) 0 = 0`
       `iter2_eqf_zero c : ... = c`
       `iter3_eqf_zero c : ... = 0`
       `iter4_eqf_zero c : ... = 3 * c^2`
     Use with `c := ‖u‖^2`.
   Hence:
       m1 : ∫ g, vin g u ∂μ = 0
       m2 : ∫ g, (vin g u)^2 ∂μ = ‖u‖^2
   (for the quadratic task you need m1, m2; odd/4th moments are the other
   child's task).
   CAREFUL: `iteratedDeriv_mgf_zero`'s RHS is written `∫ (g : Vec n), (X ^ k) g ∂μ`
   i.e. `(X ^ k)` is the pointwise power function; after you rewrite the mgf to
   `fun t => exp (‖u‖^2 * t^2 / 2)` the goal becomes an iterated-derivative of
   that function at 0 — close with the `ExpQuad` lemmas.

3. Integrability (needed for real integral additivity and for the final
   lintegral conversion): show
       hInt : ∀ k : ℕ, k ≤ 4 → Integrable (fun g : Vec n => (vin g u)^k) μ
   - Bound pointwise: for every real `x`, `|x|^k ≤ |x|^4 + 1` when `k ≤ 4`
     (split on `|x| ≤ 1`); then `|x|^4 ≤ 24 * (Real.exp x + Real.exp (-x))`
     (e.g. `x^4 ≤ 24 * Real.exp x` for `x ≥ 0` and symmetry; a generous
     constant is fine).  Use `Integrable.mono` (ae domination of `|f|` by an
     integrable function) with dominating function
     `fun g => 24 * (Real.exp (vin g u) + Real.exp (-(vin g u))) + 1`, whose
     integrability follows from `integrable_mgf_exp n u 1`,
     `integrable_mgf_exp n u (-1)` and integrability of constants on the
     probability measure `stdGaussian (Vec n)`.
   - measurability of the integrand: `(measurable_vin n u).pow`-style or
     `continuous_pow k).measurable.comp (measurable_vin n u)` (see
     `Submission.LMAux` for `measurable_vin`), or `fun_prop`.

4. Exact shifted integral (real):
       hshift : (∫ g, (a + γ * vin g u)^2 ∂ μ) = a^2 + γ^2 * ‖u‖^2
   - Expand `(a + γ * X g)^2 = a^2 + 2 * a * γ * (X g) + γ^2 * (X g)^2`
     (pointwise, `ring`), rewrite the integral of the sum using
     `MeasureTheory.integral_add` (integrable pieces from step 3; constants
     integrable since the measure is finite/probability), and plug in m1, m2.
     Note `∫` of a constant `c` over a probability measure is `c`
     (`simp`/`lintegral_const` route or `integral_const`).

5. Convert to the lintegral (ENNReal) equality:
       ∫⁻ g, ENNReal.ofReal ((a + γ * vin g u)^2) ∂ μ
         = ENNReal.ofReal (a^2 + γ^2 * ‖u‖^2)
   - The integrand is nonnegative (a square) and integrable (step 3, since
     `|(a+γX)^2| = (a+γX)^2 ≤ ...` dominated by integrable; or simply use
     `Integrable.mono` again).  Use
     `MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn` where
     `hfi : Integrable (fun g => (a + γ*vin g u)^2) μ` and
     `hnn : 0 ≤ᵐ[μ] fun g => (a + γ*vin g u)^2` (use `ae_of_all`), then rw
     [hshift] and congr.

USEFUL FACTS (namespaces):
  - `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (as used in
    `Submission/F_freshlin.lean` line ~25).
  - `integral_id_gaussianReal`, `mgf_id_gaussianReal` are NOT needed here.
  - `Fintype`, `Measurable` of inner products: `measurable_vin n u` and
    `continuous_pow k).measurable` or `(hf).pow` etc.
  - `ae_of_all μ` to build ae facts from pointwise ones.
  - `ENNReal.ofReal_add`, `ENNReal.ofReal_mul` need nonnegativity hypotheses.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- MGF membership for the linear functional `g ↦ vin g u`. -/
lemma gauss_lin_memExpSet (n : ℕ) (u : Vec n) :
    0 ∈ interior (integrableExpSet (fun g : Vec n => vin g u) (stdGaussian (Vec n))) := by
  have hset : integrableExpSet (fun g : Vec n => vin g u) (stdGaussian (Vec n)) = Set.univ := by
    ext t
    unfold integrableExpSet
    simp [integrable_mgf_exp n u t]
  rw [hset]
  simp

/-- The MGF of the linear functional `g ↦ vin g u` is `exp (‖u‖² t²/2)`. -/
lemma gauss_lin_mgf (n : ℕ) (u : Vec n) :
    mgf (fun g : Vec n => vin g u) (stdGaussian (Vec n))
      = fun t : ℝ => Real.exp (‖u‖ ^ 2 * t ^ 2 / 2) := by
  funext t
  unfold mgf
  rw [gauss_mgf]
  congr 1
  ring

/-- First moment of a linear functional of the standard Gaussian vanishes. -/
lemma gauss_lin_mom1 (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, vin g u ∂(stdGaussian (Vec n))) = 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun g : Vec n => vin g u)
    (μ := (stdGaussian (Vec n))) (gauss_lin_memExpSet n u) 1
  calc
    (∫ g : Vec n, vin g u ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n, ((fun g : Vec n => vin g u) ^ 1) g ∂(stdGaussian (Vec n)) := by
            congr 1
            funext g
            simp
    _ = iteratedDeriv 1 (mgf (fun g : Vec n => vin g u) (stdGaussian (Vec n))) 0 := h.symm
    _ = 0 := by
            rw [gauss_lin_mgf]
            exact iter1_eqf_zero (‖u‖ ^ 2)

/-- Second moment of a linear functional of the standard Gaussian. -/
lemma gauss_lin_mom2 (n : ℕ) (u : Vec n) :
    (∫ g : Vec n, (vin g u) ^ 2 ∂(stdGaussian (Vec n))) = ‖u‖ ^ 2 := by
  have h := iteratedDeriv_mgf_zero (X := fun g : Vec n => vin g u)
    (μ := (stdGaussian (Vec n))) (gauss_lin_memExpSet n u) 2
  calc
    (∫ g : Vec n, (vin g u) ^ 2 ∂(stdGaussian (Vec n)))
        = ∫ g : Vec n, ((fun g : Vec n => vin g u) ^ 2) g ∂(stdGaussian (Vec n)) := rfl
    _ = iteratedDeriv 2 (mgf (fun g : Vec n => vin g u) (stdGaussian (Vec n))) 0 := h.symm
    _ = ‖u‖ ^ 2 := by
            rw [gauss_lin_mgf]
            exact iter2_eqf_zero (‖u‖ ^ 2)

/-- Polynomials in a linear functional of a Gaussian are integrable. -/
lemma gauss_lin_int (n : ℕ) (u : Vec n) (k : ℕ) :
    Integrable (fun g : Vec n => (vin g u) ^ k) (stdGaussian (Vec n)) := by
  exact integrable_pow_of_mem_interior_integrableExpSet (gauss_lin_memExpSet n u) k

/-- Affine shift of a linear functional is measurable (powered). -/
lemma measurable_shift_pow (n : ℕ) (u : Vec n) (a γ : ℝ) (k : ℕ) :
    Measurable (fun g : Vec n => (a + γ * vin g u) ^ k) := by
  have hγ : Measurable (fun g : Vec n => γ * vin g u) := (measurable_vin n u).const_mul γ
  have hm : Measurable (fun g : Vec n => a + γ * vin g u) := by
    change Measurable ((fun _ : Vec n => a) + (fun g : Vec n => γ * vin g u))
    exact (measurable_const.add hγ)
  exact (continuous_pow k).measurable.comp hm

/-- Quadratic Gaussian step bound (lintegral form). -/
lemma gauss_quad_lin (n : ℕ) (a γ : ℝ) (u : Vec n) :
    (∫⁻ g : Vec n, ENNReal.ofReal ((a + γ * vin g u) ^ 2) ∂(stdGaussian (Vec n))) =
      ENNReal.ofReal (a ^ 2 + γ ^ 2 * ‖u‖ ^ 2) := by
  have hsq : ∀ g : Vec n, (a + γ * vin g u) ^ 2
      = a ^ 2 + (2 * a * γ) * (vin g u) + γ ^ 2 * (vin g u) ^ 2 := by
    intro g
    ring
  have hshift : (∫ g : Vec n, (a + γ * vin g u) ^ 2 ∂(stdGaussian (Vec n)))
      = a ^ 2 + γ ^ 2 * ‖u‖ ^ 2 := by
    have hX : Integrable (fun g : Vec n => vin g u) (stdGaussian (Vec n)) := by
      simpa [pow_one] using (gauss_lin_int n u 1)
    have hX2 : Integrable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) :=
      gauss_lin_int n u 2
    have hc : Integrable (fun g : Vec n => a ^ 2) (stdGaussian (Vec n)) := by
      simpa using (MeasureTheory.integrable_const : Integrable (fun g : Vec n => a ^ 2)
        (stdGaussian (Vec n)))
    have hcX : Integrable (fun g : Vec n => (2 * a * γ) * (vin g u)) (stdGaussian (Vec n)) :=
      hX.const_mul (2 * a * γ)
    have hcX2 : Integrable (fun g : Vec n => γ ^ 2 * (vin g u) ^ 2) (stdGaussian (Vec n)) :=
      hX2.const_mul (γ ^ 2)
    have hcc : Integrable (fun g : Vec n => a ^ 2 + (2 * a * γ) * (vin g u)) (stdGaussian (Vec n)) :=
      hc.add hcX
    calc
      (∫ g : Vec n, (a + γ * vin g u) ^ 2 ∂(stdGaussian (Vec n)))
          = ∫ g : Vec n, a ^ 2 + (2 * a * γ) * (vin g u) + γ ^ 2 * (vin g u) ^ 2 ∂(stdGaussian (Vec n)) := by
              congr 1
              funext g
              rw [hsq g]
      _ = (∫ g : Vec n, a ^ 2 + (2 * a * γ) * (vin g u) ∂(stdGaussian (Vec n)))
            + ∫ g : Vec n, γ ^ 2 * (vin g u) ^ 2 ∂(stdGaussian (Vec n)) := by
              rw [integral_add hcc hcX2]
      _ = a ^ 2 + γ ^ 2 * ‖u‖ ^ 2 := by
              rw [integral_add hc hcX]
              rw [MeasureTheory.integral_const_mul (2 * a * γ) (fun g : Vec n => vin g u)]
              rw [MeasureTheory.integral_const_mul (γ ^ 2) (fun g : Vec n => (vin g u) ^ 2)]
              rw [gauss_lin_mom1, gauss_lin_mom2]
              simp
  have hint : Integrable (fun g : Vec n => (a + γ * vin g u) ^ 2) (stdGaussian (Vec n)) := by
    have hXa : Integrable (fun g : Vec n => |vin g u|) (stdGaussian (Vec n)) := by
      simpa using (integrable_pow_abs_of_mem_interior_integrableExpSet (gauss_lin_memExpSet n u) 1)
    have hX2 : Integrable (fun g : Vec n => (vin g u) ^ 2) (stdGaussian (Vec n)) :=
      gauss_lin_int n u 2
    have hc1 : Integrable (fun g : Vec n => a ^ 2) (stdGaussian (Vec n)) := by
      simpa using (MeasureTheory.integrable_const : Integrable (fun g : Vec n => a ^ 2)
        (stdGaussian (Vec n)))
    have hdom : Integrable (fun g : Vec n =>
        a ^ 2 + |2 * a * γ| * |vin g u| + γ ^ 2 * (vin g u) ^ 2) (stdGaussian (Vec n)) :=
      (hc1.add (hXa.const_mul (|2 * a * γ|))).add (hX2.const_mul (γ ^ 2))
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact (measurable_shift_pow n u a γ 2).aestronglyMeasurable
    · filter_upwards with g
      have h1 : (2 * a * γ) * (vin g u) ≤ |2 * a * γ| * |vin g u| := by
        calc
          (2 * a * γ) * (vin g u) ≤ |(2 * a * γ) * (vin g u)| := le_abs_self _
          _ = |2 * a * γ| * |vin g u| := by rw [abs_mul]
      have hmain : (a + γ * vin g u) ^ 2 ≤
          a ^ 2 + |2 * a * γ| * |vin g u| + γ ^ 2 * (vin g u) ^ 2 := by
        rw [hsq g]
        nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a + γ * vin g u))] using hmain
  have hnn : 0 ≤ᵐ[stdGaussian (Vec n)] (fun g : Vec n => (a + γ * vin g u) ^ 2) :=
    ae_of_all _ (fun g => sq_nonneg _)
  have hlin := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [hshift] at hlin
  exact hlin.symm

end Discrepancy
