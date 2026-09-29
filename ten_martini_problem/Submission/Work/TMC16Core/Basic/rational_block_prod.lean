import Mathlib
import Submission.Work.TMC16Core.Defs

open Polynomial

namespace Work.TMC16Core.Basic

/-!
# The rational block product identity

For `p : ℤ`, `q : ℕ` with `q > 0` and `Nat.Coprime p.natAbs q`, and any real `x`,

`∏_{k=1}^{q} |sin (2 π (x + k p/(2q)))| = |sin (2 π q x)| * 2 / 2^q`.

The proof goes through the complex numbers.  Writing `ζ_j = exp (2 i (φ + π j p / q))`,
the polynomial identity `∏_{j<q} (X - η^j) = X^q - 1` for a primitive `q`-th root of
unity `η` gives `∏_{j<q} (v η^j - 1) = η^(∑ j) (v^q - 1)`; taking norms and using
`‖exp (i y) - 1‖ = 2 |sin (y/2)|` converts this to the trigonometric identity.
-/

/-- Evaluation of the product of `(X - η^j)` for a primitive root of unity `η`. -/
lemma roots_prod_primitive (q : ℕ) (hq : 0 < q) (η : ℂ) (hη : IsPrimitiveRoot η q)
    (v : ℂ) : ∏ j ∈ Finset.range q, (v - η ^ j) = v ^ q - 1 := by
  have h := X_pow_sub_C_eq_prod (ζ := η) (α := 1) (a := 1) hη hq (one_pow q)
  simp only [mul_one] at h
  have h2 := congrArg (fun p : ℂ[X] => Polynomial.eval v p) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod] at h2
  exact h2.symm

/-- The product `∏_{j<q} (v η^j - 1)` for a primitive `q`-th root of unity `η`. -/
lemma eta_pow_prod (q : ℕ) (hq : 0 < q) (η : ℂ) (hη : IsPrimitiveRoot η q) (v : ℂ) :
    ∏ j ∈ Finset.range q, (v * η ^ j - 1) =
      η ^ (∑ j ∈ Finset.range q, j) * (v ^ q - 1) := by
  have hne : η ≠ 0 := by
    intro h
    have hpow : η ^ q = 1 := hη.pow_eq_one
    rw [h, zero_pow hq.ne'] at hpow
    exact one_ne_zero hpow.symm
  have hstep : ∀ j, v * η ^ j - 1 = η ^ j * (v - (η⁻¹) ^ j) := by
    intro j
    rw [mul_sub, inv_pow, mul_inv_cancel₀ (pow_ne_zero j hne), mul_comm v (η ^ j)]
  rw [Finset.prod_congr rfl (fun j _ => hstep j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, roots_prod_primitive q hq η⁻¹ hη.inv v]

/-- `‖exp (2 i y) - 1‖ = 2 |sin y|`. -/
lemma norm_exp_two_mul_I_sub_one (y : ℝ) :
    ‖Complex.exp (Complex.I * (↑(2*y) : ℂ)) - 1‖ = 2 * |Real.sin y| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one (2*y)]
  rw [show (2*y)/2 = y by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- The exponential product `exp (i 2φ) * (exp (i 2t))^j = exp (i 2 (φ + j t))`. -/
lemma exp_mul_eta_pow (φ t : ℝ) (j : ℕ) :
    Complex.exp (Complex.I * (↑(2*φ) : ℂ)) * (Complex.exp (Complex.I * (↑(2*t) : ℂ)))^j
      = Complex.exp (Complex.I * (↑(2*(φ + (j:ℝ)*t)) : ℂ)) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The sine product over the full set of `q` equally spaced shifts `π j p / q`. -/
theorem sine_prod_range (q : ℕ) (hq : 0 < q) (p : ℤ) (hcop : Nat.Coprime p.natAbs q)
    (φ : ℝ) :
    ∏ j ∈ Finset.range q, |Real.sin (φ + (j:ℝ) * (Real.pi * (p:ℝ) / (q:ℝ)))| =
      |Real.sin ((q:ℝ) * φ)| * (2 / (2:ℝ)^q) := by
  have hqne : q ≠ 0 := hq.ne'
  have hcop' : IsCoprime p (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]; simpa using hcop
  set t : ℝ := Real.pi * (p:ℝ) / (q:ℝ) with ht
  set η : ℂ := Complex.exp (Complex.I * (↑(2*t) : ℂ)) with hηdef
  have hη : IsPrimitiveRoot η q := by
    have h := Complex.isPrimitiveRoot_exp_of_isCoprime p q hqne hcop'
    have harg : Complex.I * (↑(2*t) : ℂ) =
        2 * (↑Real.pi : ℂ) * Complex.I * ((↑p : ℂ)/(↑q : ℂ)) := by
      rw [ht]; push_cast; ring
    rw [hηdef, harg]; exact h
  set v : ℂ := Complex.exp (Complex.I * (↑(2*φ) : ℂ)) with hvdef
  have hterm : ∀ (j : ℕ), ‖v * η^j - 1‖ = 2 * |Real.sin (φ + (j:ℝ)*t)| := by
    intro j
    have he : v * η^j = Complex.exp (Complex.I * (↑(2*(φ + (j:ℝ)*t)) : ℂ)) := by
      rw [hvdef, hηdef]; exact exp_mul_eta_pow φ t j
    rw [he, norm_exp_two_mul_I_sub_one]
  have hvq : v^q = Complex.exp (Complex.I * (↑(2*((q:ℝ)*φ)) : ℂ)) := by
    rw [hvdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnorm_eta : ‖η ^ (∑ j ∈ Finset.range q, j)‖ = 1 := by
    rw [Complex.norm_pow,
      show ‖η‖ = 1 by rw [hηdef, Complex.norm_exp_I_mul_ofReal (2*t)], one_pow]
  have hsplit : ∏ j ∈ Finset.range q, (2 * |Real.sin (φ + (j:ℝ)*t)|) =
      (2:ℝ)^q * ∏ j ∈ Finset.range q, |Real.sin (φ + (j:ℝ)*t)| := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hL : (2:ℝ)^q * ∏ j ∈ Finset.range q, |Real.sin (φ + (j:ℝ)*t)| =
      2 * |Real.sin ((q:ℝ)*φ)| := by
    rw [← hsplit]
    calc ∏ j ∈ Finset.range q, (2 * |Real.sin (φ + (j:ℝ)*t)|)
        = ∏ j ∈ Finset.range q, ‖v*η^j - 1‖ := by
          apply Finset.prod_congr rfl; intro j _; rw [hterm j]
      _ = ‖∏ j ∈ Finset.range q, (v*η^j - 1)‖ := by rw [norm_prod]
      _ = ‖η^(∑ j ∈ Finset.range q, j) * (v^q - 1)‖ := by rw [eta_pow_prod q hq η hη v]
      _ = 2 * |Real.sin ((q:ℝ)*φ)| := by
            rw [Complex.norm_mul, hnorm_eta, one_mul, hvq, norm_exp_two_mul_I_sub_one]
  have key : ∏ j ∈ Finset.range q, |Real.sin (φ + (j:ℝ)*t)| =
      2 * |Real.sin ((q:ℝ)*φ)| / (2:ℝ)^q := by
    rw [eq_div_iff (pow_ne_zero q (by norm_num : (2:ℝ) ≠ 0)), mul_comm]
    exact hL
  rw [ht] at key
  rw [key]
  rw [show (2 * |Real.sin ((q:ℝ)*φ)|) / (2:ℝ)^q =
      |Real.sin ((q:ℝ)*φ)| * (2/(2:ℝ)^q) by ring_nf]

theorem rational_block_prod (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p.natAbs q) (x : ℝ) :
    ∏ k ∈ Finset.Icc 1 q,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
      |Real.sin (2 * Real.pi * ((q : ℝ) * x))| * (2 / (2 : ℝ) ^ q) := by
  set φ : ℝ := 2 * Real.pi * x + Real.pi * (p:ℝ) / (q:ℝ) with hφdef
  set t : ℝ := Real.pi * (p:ℝ) / (q:ℝ) with htdef
  have hreindex : ∏ k ∈ Finset.Icc 1 q,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
      ∏ j ∈ Finset.range q, |Real.sin (φ + (j:ℝ) * t)| := by
    rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := q)]
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    push_cast
    simp only [hφdef, htdef]
    field_simp
    ring_nf
  rw [hreindex, htdef]
  rw [sine_prod_range q hq p hcop φ]
  congr 1
  have hqφ : (q:ℝ)*φ = 2*Real.pi*((q:ℝ)*x) + (p:ℝ)*Real.pi := by
    rw [hφdef, htdef]; field_simp
  rw [hqφ, Real.sin_add_int_mul_pi (2*Real.pi*((q:ℝ)*x)) p, abs_mul, abs_neg_one_zpow, one_mul]

end Work.TMC16Core.Basic
