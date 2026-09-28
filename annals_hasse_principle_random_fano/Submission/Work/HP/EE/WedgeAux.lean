import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.WedgeDefs
import Submission.Work.HP.VW.multinomial_veronese
import Submission.Work.HP.tau_basic

/-!
# Auxiliary lemmas for `Work.HP.EE.wedgeNorm_veronese`

Multinomial-weighted identities for the Veronese map `ν = ν_{d,n}`:

* `weight_sum_sq`  : `∑_m (multinomial m) · ν(u)_m² = (∑_i u_i²)^d = ‖u‖^{2d}`;
* `weight_sum_mul` : `∑_m (multinomial m) · ν(u)_m ν(v)_m = (∑_i u_i v_i)^d = ⟨u,v⟩^d`;
* `weight_le`      : each multinomial coefficient is at most `(n+1)^d`.

These express the fibrewise sums over the monomials `ξ^m` in terms of the norm and the inner
product of the underlying vectors, and they are what converts the (unweighted) Veronese Gram
determinant into a quantity that can be bounded below.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.EE

open Work.HP (monWeight veronese Mon)

/-- The multinomial expansion of the fibre norm: the sum of the squared monomial values
weighted by the multinomial coefficients of the exponents is `(∑_i u_i²)^d`. -/
lemma weight_sum_sq (d n : ℕ) (u : Fin (n + 1) → ℝ) :
    ∑ m : Mon d n, (monWeight d n m : ℝ) * (veronese d n u m) ^ 2
      = (∑ i, (u i) ^ 2) ^ d := by
  have h1 : ∑ m : Mon d n, (monWeight d n m : ℝ) * (veronese d n u m)^2
      = ∑ m : Mon d n, (monWeight d n m : ℝ) * ∏ i, (u i ^ 2) ^ (m.1 i : ℕ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    show (∏ i, u i ^ ((m.1 i : Fin (d+1)) : ℕ))^2 = ∏ i, (u i ^ 2) ^ (m.1 i : ℕ)
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => by rw [← pow_mul, ← pow_mul, mul_comm])
  rw [h1, ← Work.HP.VW.multinomial_veronese d n (fun i => u i ^ 2)]

/-- The multinomial expansion of the fibre inner product: `∑_m (multinomial m) ν(u)_m ν(v)_m
= (∑_i u_i v_i)^d = ⟨u,v⟩^d`. -/
lemma weight_sum_mul (d n : ℕ) (u v : Fin (n + 1) → ℝ) :
    ∑ m : Mon d n, (monWeight d n m : ℝ) * veronese d n u m * veronese d n v m
      = (∑ i, u i * v i) ^ d := by
  have h1 : ∑ m : Mon d n, (monWeight d n m : ℝ) * veronese d n u m * veronese d n v m
      = ∑ m : Mon d n, (monWeight d n m : ℝ) * ∏ i, (u i * v i) ^ (m.1 i : ℕ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hfac : veronese d n u m * veronese d n v m = ∏ i, (u i * v i) ^ (m.1 i : ℕ) := by
      show (∏ i, u i ^ ((m.1 i : Fin (d+1)) : ℕ)) * (∏ i, v i ^ ((m.1 i : Fin (d+1)) : ℕ))
          = ∏ i, (u i * v i) ^ (m.1 i : ℕ)
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => (mul_pow _ _ _).symm)
    rw [mul_assoc, hfac]
  rw [h1, ← Work.HP.VW.multinomial_veronese d n (fun i => u i * v i)]

/-- Each multinomial coefficient of a degree-`d` exponent vector is at most `(n+1)^d`. -/
lemma weight_le (d n : ℕ) (m : Mon d n) :
    (monWeight d n m : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
  have h1 : (monWeight d n m : ℝ) ≤ ∑ m' : Mon d n, (monWeight d n m' : ℝ) :=
    Finset.single_le_sum (fun m' _ => Nat.cast_nonneg _) (Finset.mem_univ m)
  have h2 : ∑ m' : Mon d n, (monWeight d n m' : ℝ) = ((n : ℝ) + 1) ^ d := by
    have h := weight_sum_sq d n (fun _ : Fin (n+1) => (1:ℝ))
    simp only [Work.HP.veronese] at h
    simpa using h
  linarith

end Work.HP.EE
