import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_sum_sum_nonneg`

The real inner product `B.realIP f g = ∫ x, Re(conj(f x) · g x)` of
`Work.BoseB4.BoxChi` is (the real part of) an `L²(ℂ)` inner product; hence its
Gram kernel is positive semidefinite:

`0 ≤ ∑ p, ∑ q, c p · c q · B.realIP (f p) (f q)`  for real coefficients `c`.

This is the quadratic-form positivity of the box inner product that the
localisation/bracketing arguments of the LHY bound use when they replace a
general (non-diagonal) overlap matrix by a nonnegative quadratic form.

The proof identifies the double sum with the integral of `‖Σ_p c_p f_p‖²`:

* **pointwise** (`normSq_sum_ofReal_mul`), the double sum of the integrands is
  `Complex.normSq (Σ_p (c p : ℂ) · f p x)`;
* **integrally** (`sum_integral_eq_integral_sum`), the finite sum of the
  integrals is the integral of the (pointwise, nonnegative) sum.

The integrability hypothesis `hint` is exactly what is needed to pull the two
finite sums out of the integral.
-/

open scoped BigOperators
open MeasureTheory

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `Complex.normSq z = Re(conj z · z)`. -/
lemma normSq_eq_conj_mul_re_ofReal (z : ℂ) :
    Complex.normSq z = ((starRingEnd ℂ) z * z).re := by
  simpa using congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))

/-- **Pointwise square completion.**  For a finite family `z : ι → ℂ` and real
coefficients `c`, the double sum of the pairwise real inner products is the
squared norm of the linear combination `Σ_i c_i z_i`:

`∑ i, ∑ j, c i · c j · Re(conj(z i) · z j) = normSq (Σ_i (c i : ℂ) · z i)`. -/
lemma normSq_sum_ofReal_mul {ι : Type*} [Fintype ι] (z : ι → ℂ) (c : ι → ℝ) :
    Complex.normSq (∑ i, (c i : ℂ) * z i)
      = ∑ i, ∑ j, c i * c j * ((starRingEnd ℂ) (z i) * z j).re := by
  rw [normSq_eq_conj_mul_re_ofReal]
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.sum_mul_sum]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A finite sum of integrals of integrable real functions is the integral of
the finite sum. -/
lemma sum_integral_eq_integral_sum {ι : Type*} [Fintype ι] (g : ι → ℝ³ → ℝ)
    (hg : ∀ i, Integrable (g i)) :
    (∑ i, ∫ x, g i x) = ∫ x, ∑ i, g i x := by
  simpa using (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hg i)).symm

/-- **The Gram quadratic form of `B.realIP` is nonnegative.**  For real
coefficients `c : ι → ℝ` and any finite family `f : ι → ℝ³ → ℂ` whose pairwise
integrands are integrable, `∑ p, ∑ q, c p · c q · B.realIP (f p) (f q) ≥ 0`. -/
theorem realIP_sum_sum_nonneg (B : Work.BoseB4.BoxData) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → EuclideanSpace ℝ (Fin 3) → ℂ) (c : ι → ℝ)
    (hint : ∀ p q : ι, MeasureTheory.Integrable
      fun x => ((starRingEnd ℂ) (f p x) * f q x).re) :
    0 ≤ ∑ p, ∑ q, c p * c q * B.realIP (f p) (f q) := by
  simp only [BoxData.realIP_apply]
  -- Pull the two finite sums out of the integral.
  have hswap : (∑ p, ∑ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re)
      = ∫ x, ∑ p, ∑ q, c p * c q * ((starRingEnd ℂ) (f p x) * f q x).re := by
    have h1 : ∀ p, (∑ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re)
        = ∫ x, ∑ q, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re := by
      intro p
      have hq : ∀ q, c p * c q * ∫ x, ((starRingEnd ℂ) (f p x) * f q x).re
          = ∫ x, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re := by
        intro q
        rw [MeasureTheory.integral_const_mul]
      rw [Finset.sum_congr rfl (fun q _ => hq q)]
      exact sum_integral_eq_integral_sum _
        (fun q => (hint p q).const_mul (c p * c q))
    have h2 := sum_integral_eq_integral_sum
      (fun p x => ∑ q, (c p * c q) * ((starRingEnd ℂ) (f p x) * f q x).re)
      (fun p => MeasureTheory.integrable_finsetSum Finset.univ
        (fun q _ => (hint p q).const_mul (c p * c q)))
    rw [Finset.sum_congr rfl (fun p _ => h1 p), h2]
  rw [hswap]
  -- Identify the integrand with the nonnegative `normSq` of the combination.
  rw [show (∫ x, ∑ p, ∑ q, c p * c q * ((starRingEnd ℂ) (f p x) * f q x).re)
      = ∫ x, Complex.normSq (∑ p, (c p : ℂ) * f p x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        (normSq_sum_ofReal_mul (fun p => f p x) c).symm))]
  exact MeasureTheory.integral_nonneg (fun x => Complex.normSq_nonneg _)

end Work.BoseB4
