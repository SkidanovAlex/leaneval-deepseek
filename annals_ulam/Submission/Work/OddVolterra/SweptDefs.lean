import Mathlib

/-!
# The swept Abel kernel

This file sets up the vocabulary for the differentiating-under-the-integral-sign
lemma

`iteratedDeriv k (fun u => ∫ σ in u..b, (σ - u)^p * A u σ) s
   = ∫ σ in s..b, iteratedDeriv k (fun u => (σ - u)^p * A u σ) s`

which states that for a `C^k` kernel `A` and a real exponent `p` with
`p - k > -1`, the `k`-th iterated derivative of the "swept" integral
`u ↦ ∫_σ in u..b, (σ-u)^p A u σ` may be taken under the integral sign: all the
boundary terms produced by the moving lower limit vanish because `(σ-u)^p` has
a zero of order `p > k-1` at the diagonal.

The mathematical content is the classical Leibniz formula for the `n`-th partial
`u`-derivative of the kernel:

`∂_u^n ((σ-u)^p A(u,σ)) = Σ_{i ≤ n} (-1)^i C(n,i) (p)_i (σ-u)^{p-i} ∂_1^{n-i} A(u,σ)`

with `(p)_i = p (p-1) ⋯ (p-i+1)` the falling factorial.  `ks` is the right-hand
side as a function of `(u,σ)`; `kt` is the same expression in the shifted
variable `t = σ - u`, which is the variable in which the singular factor
`t^{p-i}` sits at the *fixed* endpoint `t = 0`; `dkt` and `tkt` are its partial
derivatives with respect to `u` and `t`.
-/

noncomputable section

namespace Work.OddVolterra

/-- The falling factorial `p (p-1) ⋯ (p-n+1)`, i.e. `rff p 0 = 1` and
`rff p (n+1) = rff p n * (p - n)`. -/
def rff (p : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (p - j)

/-- The coefficient of the `i`-th term of the Leibniz expansion of the `n`-th
`u`-derivative of `(σ-u)^p A(u,σ)`: `(-1)^i C(n,i) (p)_i`. -/
def lcoef (n i : ℕ) (p : ℝ) : ℝ := (n.choose i : ℝ) * (-1 : ℝ) ^ i * rff p i

/-- The `j`-th derivative of `A` in its first variable, the second variable held
fixed at `σ`. -/
def pder (A : ℝ → ℝ → ℝ) (j : ℕ) (u σ : ℝ) : ℝ :=
  iteratedDeriv j (fun x : ℝ => A x σ) u

/-- The derivative in the second variable of the `j`-th first-variable partial
derivative of `A`. -/
def qder (A : ℝ → ℝ → ℝ) (j : ℕ) (u σ : ℝ) : ℝ :=
  deriv (fun σ' : ℝ => pder A j u σ') σ

/-- The Leibniz expansion of the `n`-th partial `u`-derivative of
`(σ - u)^p * A u σ`, in the variable `σ`. -/
def ks (A : ℝ → ℝ → ℝ) (p : ℝ) (n : ℕ) (u σ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), lcoef n i p * (σ - u) ^ (p - i) * pder A (n - i) u σ

/-- The same expansion in the shifted variable `t = σ - u`. -/
def kt (A : ℝ → ℝ → ℝ) (p : ℝ) (n : ℕ) (u t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), lcoef n i p * t ^ (p - i) * pder A (n - i) u (u + t)

/-- The `u`-derivative of `kt`, written out. -/
def dkt (A : ℝ → ℝ → ℝ) (p : ℝ) (n : ℕ) (u t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), lcoef n i p * t ^ (p - i) *
    (pder A (n - i + 1) u (u + t) + qder A (n - i) u (u + t))

/-- The `t`-derivative of `kt`, written out. -/
def tkt (A : ℝ → ℝ → ℝ) (p : ℝ) (n : ℕ) (u t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), lcoef n i p *
    ((p - i) * t ^ (p - i - 1) * pder A (n - i) u (u + t) +
      t ^ (p - i) * qder A (n - i) u (u + t))

@[simp] lemma rff_zero (p : ℝ) : rff p 0 = 1 := by simp [rff]

lemma rff_succ (p : ℝ) (n : ℕ) : rff p (n + 1) = rff p n * (p - n) := by
  simp [rff, Finset.prod_range_succ]

lemma lcoef_zero (n : ℕ) (p : ℝ) : lcoef n 0 p = 1 := by simp [lcoef]

lemma kt_eq_ks (A : ℝ → ℝ → ℝ) (p : ℝ) (n : ℕ) (u t : ℝ) :
    kt A p n u t = ks A p n u (u + t) := by
  unfold kt ks
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show u + t - u = t by ring]

lemma kt_zero (A : ℝ → ℝ → ℝ) (p : ℝ) (u t : ℝ) :
    kt A p 0 u t = t ^ p * A u (u + t) := by
  simp [kt, lcoef, pder]

/-- For `p > n` the expansion `kt A p n u t` vanishes at `t = 0`. -/
lemma kt_at_zero {A : ℝ → ℝ → ℝ} {p : ℝ} {n : ℕ} (hn : (n : ℝ) < p) (u : ℝ) :
    kt A p n u 0 = 0 := by
  unfold kt
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : (i : ℝ) ≤ n := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpos : p - i ≠ 0 := by linarith
  simp [Real.zero_rpow hpos]

end Work.OddVolterra

end
