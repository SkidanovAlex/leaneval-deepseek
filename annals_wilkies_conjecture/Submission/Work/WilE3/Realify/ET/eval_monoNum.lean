import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE3.Realify.EvalMain

namespace Work.WilE3.Realify.ET

open Work.WilE3.Realify
open WilkiesDesign.E (EAChain)

/-! ## §1. Two complex-analysis normalisations -/

/-- The complex form of the half-angle relations `1 + i tan θ = e^{iθ}/cos θ` and
`1 + tan θ ^ 2 = 1 / cos θ ^ 2` (which is what makes the `tan`-substitution of the
realification work). -/
theorem one_add_I_tan_sq_aux (θ : ℝ) (h : Real.cos θ ≠ 0) :
    (1 + Complex.I * (Real.tan θ : ℂ)) ^ 2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) * ((1 + Real.tan θ ^ 2 : ℝ) : ℂ) := by
  have hreal : (1 + Real.tan θ ^ 2 : ℝ) = 1 / (Real.cos θ) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcos : Complex.cos (θ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]
    exact_mod_cast h
  have h1 : 1 + Complex.I * (Real.tan θ : ℂ)
      = (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) / Complex.cos (θ : ℂ) := by
    rw [Complex.ofReal_tan, eq_div_iff hcos, add_mul, one_mul, mul_assoc,
      Complex.tan_mul_cos hcos]
    ring
  have h2 : Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I]
  have hcast : ((1 / (Real.cos θ) ^ 2 : ℝ) : ℂ) = (Complex.cos (θ : ℂ) ^ 2)⁻¹ := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, ← Complex.ofReal_cos,
      one_div]
  rw [h1, h2, hreal, hcast, div_pow, ← Complex.exp_nat_mul, div_eq_mul_inv]
  congr 1
  congr 1
  push_cast
  ring

/-- A complex sum built from real data, in the two forms the realification steps between:
`∑ i, a i * (u i + i v i) + b` with the real and imaginary parts collected. -/
theorem ofReal_sum_add_mul_I_aux {ι : Type*} [Fintype ι] (a u v : ι → ℝ) (b : ℝ) :
    (((∑ i, a i * u i : ℝ) + b : ℂ)) + ((∑ i, a i * v i : ℝ) : ℂ) * Complex.I
      = ∑ i, (a i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I) + (b : ℂ) := by
  have hsplit : (∑ i, (a i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I))
      = ((∑ i, a i * u i : ℝ) : ℂ) + ((∑ i, a i * v i : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hsplit]
  ring

/-- The corner identity of the realification: `e^{i cc} · e^ℓ · (1 + i tan θ)^2` with
`θ = (ψ - cc)/2` is `e^{ℓ + iψ} · (1 + tan²θ)`. -/
theorem corner_aux (ψ ℓ cc ee : ℝ) (he : (ee : ℂ) = Complex.exp ((cc : ℂ) * Complex.I))
    (hc : Real.cos ((ψ - cc) / 2) ≠ 0) :
    (ee : ℂ) * ((Real.exp ℓ : ℝ) : ℂ)
        * (1 + 2 * Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)
            - ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ) ^ 2)
      = Complex.exp ((ℓ : ℂ) + (ψ : ℂ) * Complex.I)
        * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ) := by
  have hkey := one_add_I_tan_sq_aux ((ψ - cc) / 2) hc
  have hZ : (1 + 2 * Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)
      - ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ) ^ 2)
      = (1 + Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)) ^ 2 := by
    have hI : Complex.I ^ 2 = (-1 : ℂ) := by rw [sq, Complex.I_mul_I]
    calc (1 + 2 * Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)
          - ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ) ^ 2)
        = 1 + 2 * Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)
            + Complex.I ^ 2 * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ) ^ 2 := by
          rw [hI]; ring
      _ = (1 + Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)) ^ 2 := by ring
  have hY : ((Real.exp ℓ : ℝ) : ℂ) = Complex.exp (ℓ : ℂ) := Complex.ofReal_exp ℓ
  have harg : (((2 : ℝ) * ((ψ - cc) / 2) : ℝ) : ℂ) = (ψ : ℂ) - (cc : ℂ) := by
    push_cast
    ring
  have hp : (ee : ℂ) * Complex.exp ((((2 : ℝ) * ((ψ - cc) / 2) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ψ : ℂ) * Complex.I) := by
    rw [harg, he, ← Complex.exp_add]
    congr 1
    ring
  calc (ee : ℂ) * ((Real.exp ℓ : ℝ) : ℂ)
        * (1 + 2 * Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)
            - ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ) ^ 2)
      = (ee : ℂ) * ((Real.exp ℓ : ℝ) : ℂ)
          * (1 + Complex.I * ((Real.tan ((ψ - cc) / 2) : ℝ) : ℂ)) ^ 2 := by rw [hZ]
    _ = (ee : ℂ) * ((Real.exp ℓ : ℝ) : ℂ)
          * (Complex.exp ((((2 : ℝ) * ((ψ - cc) / 2) : ℝ) : ℂ) * Complex.I)
              * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ)) := by rw [hkey]
    _ = ((ee : ℂ) * Complex.exp ((((2 : ℝ) * ((ψ - cc) / 2) : ℝ) : ℂ) * Complex.I))
          * (((Real.exp ℓ : ℝ) : ℂ) * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ)) := by
        rw [mul_mul_mul_comm]
    _ = Complex.exp ((ψ : ℂ) * Complex.I)
          * (((Real.exp ℓ : ℝ) : ℂ) * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ)) := by
        rw [hp]
    _ = (Complex.exp (ℓ : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
          * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ) := by
        rw [hY]
        ring
    _ = Complex.exp ((ℓ : ℂ) + (ψ : ℂ) * Complex.I)
          * ((1 + Real.tan ((ψ - cc) / 2) ^ 2 : ℝ) : ℂ) := by rw [Complex.exp_add]

/-! ## §2. The evaluation identity -/

theorem eval_monoNum {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hm : ∀ j, m (Sum.inr j) ≤ N) :
    MvPolynomial.eval (fun s => (Work.WilE3.Realify.chainPt c cc u v s : ℂ))
        (Work.WilE3.Realify.monoNum (k := k) (r := r) N e m)
      = (∏ i : Fin k, ((u i : ℂ) + (v i : ℂ) * Complex.I) ^ (m (Sum.inl i)))
        * (∏ j : Fin r, (Complex.exp (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I)
              + (c.b j : ℂ))) ^ (m (Sum.inr j)))
        * ((Work.WilE3.Realify.Wval c cc v : ℝ) : ℂ) ^ N := by
  have h1 : MvPolynomial.eval (fun s => (chainPt c cc u v s : ℂ))
        (∏ i : Fin k, (cU i + cI * cV i) ^ (m (Sum.inl i)))
      = ∏ i : Fin k, ((u i : ℂ) + (v i : ℂ) * Complex.I) ^ (m (Sum.inl i)) := by
    simp only [map_prod, map_pow, map_add, map_mul, cU, cV, cI, MvPolynomial.eval_X,
      MvPolynomial.eval_C, chainPt_inl, mkPt_apply_castAdd, mkPt_apply_natAdd]
    apply Finset.prod_congr rfl
    intro i _
    ring
  have h2 : MvPolynomial.eval (fun s => (chainPt c cc u v s : ℂ))
        (∏ j : Fin r, ((MvPolynomial.C (e j : ℂ)) * cY j * cZ j) ^ (m (Sum.inr j)))
      = ∏ j : Fin r, (((e j : ℂ) * ((Real.exp (∑ i, c.a j i * u i + c.b j) : ℝ) : ℂ))
            * (1 + 2 * Complex.I * ((Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℝ) : ℂ)
              - ((Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℝ) : ℂ) ^ 2)) ^
            (m (Sum.inr j)) := by
    simp only [map_prod, map_pow, map_add, map_sub, map_mul, map_one, cY, cZ, cT, cI,
      MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_ofNat, chainPt_inr_castAdd,
      chainPt_inr_natAdd]
  have h3 : MvPolynomial.eval (fun s => (chainPt c cc u v s : ℂ))
        (∏ j : Fin r, (cW j) ^ (N - m (Sum.inr j)))
      = ∏ j : Fin r, (((1 + Real.tan ((∑ i, c.a j i * v i - cc j) / 2) ^ 2 : ℝ)) : ℂ) ^
            (N - m (Sum.inr j)) := by
    simp only [map_prod, map_pow, map_add, map_one, cW, cT, MvPolynomial.eval_X,
      chainPt_inr_natAdd, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  have hW : ((Wval c cc v : ℝ) : ℂ) ^ N
      = ∏ j : Fin r, (((1 + Real.tan ((∑ i, c.a j i * v i - cc j) / 2) ^ 2 : ℝ)) : ℂ) ^ N := by
    rw [Wval, Complex.ofReal_prod, ← Finset.prod_pow]
  rw [monoNum, MvPolynomial.eval_mul, MvPolynomial.eval_mul, h1, h2, h3, hW]
  have hkey :
      (∏ j : Fin r, (((e j : ℂ) * ((Real.exp (∑ i, c.a j i * u i + c.b j) : ℝ) : ℂ))
            * (1 + 2 * Complex.I * ((Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℝ) : ℂ)
              - ((Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℝ) : ℂ) ^ 2)) ^
            (m (Sum.inr j)))
        * (∏ j : Fin r, (((1 + Real.tan ((∑ i, c.a j i * v i - cc j) / 2) ^ 2 : ℝ)) : ℂ) ^
            (N - m (Sum.inr j)))
      = (∏ j : Fin r, (Complex.exp (∑ i, (c.a j i : ℂ) *
              ((u i : ℂ) + (v i : ℂ) * Complex.I) + (c.b j : ℂ))) ^ (m (Sum.inr j)))
        * (∏ j : Fin r, (((1 + Real.tan ((∑ i, c.a j i * v i - cc j) / 2) ^ 2 : ℝ)) : ℂ) ^ N) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hc := corner_aux (∑ i, c.a j i * v i) (∑ i, c.a j i * u i + c.b j) (cc j) (e j)
      (he j) (hcos j)
    have hco := ofReal_sum_add_mul_I_aux (c.a j) u v (c.b j)
    have hE : Complex.exp ((↑(∑ i, c.a j i * u i + c.b j))
          + ↑(∑ i, c.a j i * v i) * Complex.I)
        = Complex.exp (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I)
            + (c.b j : ℂ)) := by
      congr 1
      rw [Complex.ofReal_add]
      exact hco
    have hsub : m (Sum.inr j) + (N - m (Sum.inr j)) = N := Nat.add_sub_of_le (hm j)
    rw [hc, hE, mul_pow, mul_assoc, ← pow_add, hsub]
  rw [mul_assoc, hkey]
  ring

end Work.WilE3.Realify.ET
