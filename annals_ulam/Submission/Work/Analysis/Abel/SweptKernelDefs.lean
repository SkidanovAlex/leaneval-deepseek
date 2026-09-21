import Mathlib

/-!
# The swept Abel kernel: definitions

Vocabulary for the differentiating-under-the-integral-sign lemma

`iteratedDeriv k (fun u => ∫ σ in u..b, (σ - u)^p * A u σ) s
   = ∫ σ in s..b, iteratedDeriv k (fun u => (σ - u)^p * A u σ) s`

The `j`-th partial `u`-derivative of the kernel `(σ-u)^p A(u,σ)` is given by the
Leibniz expansion

`∂_u^j ((σ-u)^p A(u,σ)) = Σ_{i ≤ j} (-1)^i C(j,i) (p)_i (σ-u)^{p-i} ∂_u^{j-i} A(u,σ)`

with `(p)_i = p (p-1) ⋯ (p-i+1)` the falling factorial (`rff p i`) and
`∂_u^m A(x,σ) = iteratedDeriv m (fun x => A x σ) x` (`pder A m x σ`).
`ks A p j x σ` is that expansion evaluated at `u = x`.
-/

namespace Work.Analysis.Abel

noncomputable section

/-- The falling factorial `p (p-1) ⋯ (p-j+1)`, i.e. `rff p 0 = 1` and
`rff p (j+1) = rff p j * (p - j)`. -/
def rff (p : ℝ) (j : ℕ) : ℝ := ∏ m ∈ Finset.range j, (p - m)

/-- The coefficient `(-1)^i C(j,i) (p)_i` of the `i`-th term of the Leibniz
expansion of the `j`-th `u`-derivative of `(σ-u)^p A(u,σ)`. -/
def lcoef (j i : ℕ) (p : ℝ) : ℝ := (j.choose i : ℝ) * (-1 : ℝ) ^ i * rff p i

/-- The `j`-th iterated derivative of `A` in its **first** variable, the second
variable held fixed at `σ`. -/
def pder (A : ℝ → ℝ → ℝ) (j : ℕ) (u σ : ℝ) : ℝ := iteratedDeriv j (fun x : ℝ => A x σ) u

/-- The Leibniz expansion of `∂_u^j ((σ - u)^p * A u σ)` evaluated at `u = x`. -/
def ks (A : ℝ → ℝ → ℝ) (p : ℝ) (j : ℕ) (x σ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), lcoef j i p * (σ - x) ^ (p - i) * pder A (j - i) x σ

@[simp] lemma rff_zero (p : ℝ) : rff p 0 = 1 := by simp [rff]

lemma rff_succ (p : ℝ) (j : ℕ) : rff p (j + 1) = rff p j * (p - j) := by
  simp [rff, Finset.prod_range_succ]

@[simp] lemma lcoef_zero (j : ℕ) (p : ℝ) : lcoef j 0 p = 1 := by simp [lcoef]

@[simp] lemma pder_zero (A : ℝ → ℝ → ℝ) (u σ : ℝ) : pder A 0 u σ = A u σ := by
  simp [pder]

/-- The Pascal-type identity satisfied by the Leibniz coefficients. -/
lemma lcoef_succ (j i : ℕ) (p : ℝ) :
    lcoef (j + 1) (i + 1) p = lcoef j (i + 1) p - lcoef j i p * (p - i) := by
  unfold lcoef
  rw [Nat.choose_succ_succ, rff_succ p i, pow_succ]
  push_cast
  ring

@[simp] lemma ks_zero (A : ℝ → ℝ → ℝ) (p x σ : ℝ) : ks A p 0 x σ = (σ - x) ^ p * A x σ := by
  simp [ks, lcoef, pder]

/-- The derivative of `pder A j · σ` in the first variable is `pder A (j+1)`:
this is `iteratedDeriv_succ`. -/
lemma deriv_pder (A : ℝ → ℝ → ℝ) (j : ℕ) (u σ : ℝ) :
    deriv (fun u' : ℝ => pder A j u' σ) u = pder A (j + 1) u σ := by
  simp only [pder, iteratedDeriv_succ]

/-- `n + 1/2` is never an integer, so `0 ^ (n + 1/2 - i) = 0` for every `i : ℕ`. -/
lemma half_ne_nat (n i : ℕ) : ((n : ℝ) + 1 / 2) - (i : ℝ) ≠ 0 := by
  intro h
  have h2 : (2 : ℝ) * (n : ℝ) + 1 = 2 * (i : ℝ) := by linarith
  have hZ : (2 * (n : ℤ) + 1 : ℤ) = 2 * (i : ℤ) := by exact_mod_cast h2
  omega

/-- **The kernel of the swept integral has vanishing diagonal.** -/
lemma ks_self (A : ℝ → ℝ → ℝ) (p : ℝ) {j : ℕ}
    (h : ∀ i : ℕ, p - (i : ℝ) ≠ 0) (x : ℝ) :
    ks A p j x x = 0 := by
  simp only [ks]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sub_self]
  simp [Real.zero_rpow (h i)]

end

end Work.Analysis.Abel
