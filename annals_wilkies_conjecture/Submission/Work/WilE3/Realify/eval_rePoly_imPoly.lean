/-
  Area E3, `Realify`: the fundamental evaluation identity for `rePoly`/`imPoly`.

  For a real assignment `gR : Sig k r → ℝ` and a complex polynomial `p`, evaluating `p` at the
  complexification of `gR` splits into the real and imaginary coefficientwise parts:
  `eval (gR : ℂ) p = (eval gR (rePoly p) : ℂ) + (eval gR (imPoly p) : ℂ) * I`.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs

namespace Work.WilE3.Realify

open MvPolynomial

variable {k r : ℕ}

/-- Splitting a complex multiple of a real number `t` into its real and imaginary parts. -/
lemma complex_mul_ofReal_re_im (c : ℂ) (t : ℝ) :
    c * (t : ℂ) = ((c.re * t : ℝ) : ℂ) + ((c.im * t : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- `Finsupp.prod` commutes with the coercion `ℝ → ℂ`. -/
lemma finsupp_prod_cast {σ : Type*} (m : σ →₀ ℕ) (g : σ → ℝ) :
    (m.prod fun i e => (g i : ℂ) ^ e) = ((m.prod fun i e => g i ^ e : ℝ) : ℂ) := by
  rw [Finsupp.prod, Finsupp.prod, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun i _ => by simp)

/-- Evaluation of a complex monomial at the complexification of a real assignment. -/
lemma eval_monomial_cast {σ : Type*} (gR : σ → ℝ) (m : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.eval (fun s => (gR s : ℂ)) (MvPolynomial.monomial m c)
      = ((c.re * (m.prod fun i e => gR i ^ e) : ℝ) : ℂ)
        + ((c.im * (m.prod fun i e => gR i ^ e) : ℝ) : ℂ) * Complex.I := by
  rw [MvPolynomial.eval_monomial, finsupp_prod_cast]
  exact complex_mul_ofReal_re_im c _

theorem eval_rePoly_imPoly {k r : ℕ} (gR : Sig k r → ℝ) (p : MvPolynomial (Sig k r) ℂ) :
    MvPolynomial.eval (fun s => (gR s : ℂ)) p
      = ((MvPolynomial.eval gR (rePoly p) : ℝ) : ℂ)
        + ((MvPolynomial.eval gR (imPoly p) : ℝ) : ℂ) * Complex.I := by
  have hL : MvPolynomial.eval (fun s => (gR s : ℂ)) p
      = ∑ m ∈ p.support, ((((p.coeff m).re * (m.prod fun i e => gR i ^ e) : ℝ) : ℂ)
          + ((((p.coeff m).im * (m.prod fun i e => gR i ^ e) : ℝ) : ℂ) * Complex.I)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun m _ => eval_monomial_cast gR m (p.coeff m))
  have hre : MvPolynomial.eval gR (rePoly p)
      = ∑ m ∈ p.support, (p.coeff m).re * (m.prod fun i e => gR i ^ e) := by
    rw [rePoly, map_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.eval_monomial])
  have him : MvPolynomial.eval gR (imPoly p)
      = ∑ m ∈ p.support, (p.coeff m).im * (m.prod fun i e => gR i ^ e) := by
    rw [imPoly, map_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.eval_monomial])
  rw [hL, hre, him, Finset.sum_add_distrib, Complex.ofReal_sum, Complex.ofReal_sum,
    Finset.sum_mul]

end Work.WilE3.Realify
