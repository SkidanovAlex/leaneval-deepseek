import Mathlib

/-!
# Vocabulary for the fourth moment of the step-truncated Dirichlet polynomial

The sharp truncated approximate functional equation expresses `ζ(1/2+it)` (up to a bounded
factor) through the Dirichlet polynomial `Σ_{n ≤ N(t)} n^{-(1/2+it)}` with the height-dependent
truncation `N(t) = ⌊√(t/2π)⌋₊ + 1`.  To take a fourth moment of such an object one has to deal
with **step functions of `t` in the length of the sum**, which is what the definitions below
provide:

* `stepTerm n t` is `n^{-(1/2+it)}` for `t ≥ 2π(n-1)²` and `0` before, so that
  `Σ_{n ≤ M} stepTerm n t` realises the truncation at `N(t)` as soon as `M ≥ N(t)`;
* `stepPoly M t = Σ_{n ≤ M} stepTerm n t`;
* `stepPair m n t = stepTerm m t * stepTerm n t`, written as one indicator times one exponential;
* `pairBox M`, `pairProd p = p.1 * p.2` and `pairKernel T K K'`: the index-pair bookkeeping and
  the elementary kernel `T/K` (diagonal) or `2max(K,K')/(√(KK')|K-K'|)` (off-diagonal) that
  bounds the integral of a pair product.

The exponential form (rather than a complex power) is chosen so that products of two summands are
trivial: `exp(-i t log m) · exp(-i t log n) = exp(-i t log (mn))`.
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

noncomputable section

/-- The `n`-th summand of the step-truncated Dirichlet polynomial: `n^{-(1/2+it)}` for
`t ≥ 2π(n-1)²`, and `0` before. -/
def stepTerm (n : ℕ) (t : ℝ) : ℂ :=
  if 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
    ((Real.sqrt (n : ℝ) : ℂ))⁻¹ *
      Complex.exp (-(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)))
  else 0

/-- The step-truncated Dirichlet polynomial `Σ_{n ≤ M} stepTerm n t`. -/
def stepPoly (M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, stepTerm n t

/-- The product of two summands, written as a single indicator times one exponential. -/
def stepPair (m n : ℕ) (t : ℝ) : ℂ :=
  if 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
    ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹ *
      Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ)))
  else 0

/-- The product map on index pairs, used to group the quadruple sum. -/
def pairProd (p : ℕ × ℕ) : ℕ := p.1 * p.2

/-- The box of index pairs. -/
def pairBox (M : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)

/-- The elementary bound attached to a pair of products `(K, K')`: `T/K` on the diagonal and
`2·max(K,K')/(√(KK')|K-K'|)` off it.  (Lean's `x/0 = 0` makes the off-diagonal formula harmless on
the diagonal, so the two cases can also be added.) -/
def pairKernel (T : ℝ) (K K' : ℕ) : ℝ :=
  if K = K' then T / (K : ℝ)
  else 2 * max (K : ℝ) (K' : ℝ) / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|)

section Basic

lemma stepTerm_apply (n : ℕ) (t : ℝ) :
    stepTerm n t = if 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
      ((Real.sqrt (n : ℝ) : ℂ))⁻¹ *
        Complex.exp (-(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))) else 0 := rfl

lemma stepPair_apply (m n : ℕ) (t : ℝ) :
    stepPair m n t = if 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t
        ∧ 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
      ((Real.sqrt ((m : ℝ) * (n : ℝ)) : ℂ))⁻¹ *
        Complex.exp (-(Complex.I * ((t * Real.log ((m : ℝ) * (n : ℝ)) : ℝ) : ℂ))) else 0 := rfl

lemma pairProd_apply (p : ℕ × ℕ) : pairProd p = p.1 * p.2 := rfl

lemma pairBox_apply (M : ℕ) : pairBox M = (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) := rfl

lemma pairKernel_apply (T : ℝ) (K K' : ℕ) :
    pairKernel T K K' = if K = K' then T / (K : ℝ)
      else 2 * max (K : ℝ) (K' : ℝ) /
        (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|) := rfl

/-- For `1 ≤ a`, squaring `a - 1` is monotone. -/
lemma sq_sub_one_le_sq_sub_one {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (a - 1) ^ 2 ≤ (b - 1) ^ 2 := by
  have h1 : (0 : ℝ) ≤ a - 1 := by linarith
  have h2 : a - 1 ≤ b - 1 := by linarith
  exact pow_le_pow_left₀ h1 h2 2

/-- **Multiplicativity of the step functions**: the product of two summands is a single step
function with the two thresholds conjoined. -/
lemma stepTerm_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    stepTerm m t * stepTerm n t = stepPair m n t := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : ((Real.sqrt (m:ℝ) : ℂ))⁻¹ * ((Real.sqrt (n:ℝ) : ℂ))⁻¹
      = ((Real.sqrt ((m:ℝ)*(n:ℝ)) : ℂ))⁻¹ := by
    rw [Real.sqrt_mul (le_of_lt hm0), Complex.ofReal_mul, mul_inv]
  have hexp : Complex.exp (-(Complex.I * ((t * Real.log (m:ℝ) : ℝ) : ℂ)))
      * Complex.exp (-(Complex.I * ((t * Real.log (n:ℝ) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((t * Real.log ((m:ℝ)*(n:ℝ)) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    rw [Real.log_mul (ne_of_gt hm0) (ne_of_gt hn0)]
    push_cast
    ring
  rw [stepTerm_apply, stepTerm_apply, stepPair_apply]
  by_cases hmθ : 2 * Real.pi * ((m : ℝ) - 1) ^ 2 ≤ t
  · by_cases hnθ : 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t
    · rw [if_pos hmθ, if_pos hnθ, if_pos ⟨hmθ, hnθ⟩]
      calc ((Real.sqrt (m:ℝ) : ℂ))⁻¹ * Complex.exp (-(Complex.I * ((t * Real.log (m:ℝ) : ℝ) : ℂ)))
            * (((Real.sqrt (n:ℝ) : ℂ))⁻¹ * Complex.exp (-(Complex.I * ((t * Real.log (n:ℝ) : ℝ) : ℂ))))
          = (((Real.sqrt (m:ℝ) : ℂ))⁻¹ * ((Real.sqrt (n:ℝ) : ℂ))⁻¹)
            * (Complex.exp (-(Complex.I * ((t * Real.log (m:ℝ) : ℝ) : ℂ)))
               * Complex.exp (-(Complex.I * ((t * Real.log (n:ℝ) : ℝ) : ℂ)))) := by ring
        _ = ((Real.sqrt ((m:ℝ)*(n:ℝ)) : ℂ))⁻¹ *
            Complex.exp (-(Complex.I * ((t * Real.log ((m:ℝ)*(n:ℝ)) : ℝ) : ℂ))) := by
            rw [hsqrt, hexp]
    · rw [if_pos hmθ, if_neg hnθ, if_neg (fun h => hnθ h.2), mul_zero]
  · by_cases hnθ : 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t
    · rw [if_neg hmθ, if_pos hnθ, if_neg (fun h => hmθ h.1), zero_mul]
    · rw [if_neg hmθ, if_neg hnθ, if_neg (fun h => hmθ h.1), zero_mul]

/-- The summands have modulus `(√n)⁻¹ = n^{-1/2}`. -/
lemma norm_stepTerm_le (n : ℕ) (t : ℝ) : ‖stepTerm n t‖ ≤ ((Real.sqrt (n : ℝ))⁻¹) := by
  rw [stepTerm_apply]
  split_ifs with h
  · rw [norm_mul,
      show -(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))
        = ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n))]
  · simp

end Basic

end

end Work.ZeroDensity.Ingham
