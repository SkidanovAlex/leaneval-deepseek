import Mathlib

namespace Work.WilE8.Poly

open Polynomial

/-- For a polynomial `p` over `ℕ` and `D ≥ 1`, the evaluation at `D` is bounded by
the sum of coefficients (`p.eval 1`) times `D` raised to the (natural) degree. -/
theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {D : ℕ} (hD : 1 ≤ D) :
    p.eval D ≤ p.eval 1 * D ^ p.natDegree := by
  have h1 : p.eval 1 = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k := by
    rw [eval_eq_sum_range]; simp
  rw [eval_eq_sum_range, h1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ p.natDegree := by
    simp only [Finset.mem_range] at hk; omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD hk')

theorem exists_dom {ι : Type*} [Fintype ι] (p : ι → Polynomial ℕ) :
    ∃ (c e : ℕ), ∀ D : ℕ, 1 ≤ D → ∀ i, (p i).eval D ≤ c * D ^ e := by
  refine ⟨∑ i, (p i).eval 1, ∑ i, (p i).natDegree, ?_⟩
  intro D hD i
  have h1 : (p i).eval D ≤ (p i).eval 1 * D ^ (p i).natDegree :=
    eval_le_eval_one_mul_pow (p i) hD
  have h2 : (p i).natDegree ≤ ∑ j, (p j).natDegree :=
    Finset.single_le_sum (f := fun j => (p j).natDegree)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (p i).eval 1 ≤ ∑ j, (p j).eval 1 :=
    Finset.single_le_sum (f := fun j => (p j).eval 1)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  calc (p i).eval D ≤ (p i).eval 1 * D ^ (p i).natDegree := h1
    _ ≤ (p i).eval 1 * D ^ (∑ j, (p j).natDegree) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD h2)
    _ ≤ (∑ j, (p j).eval 1) * D ^ (∑ j, (p j).natDegree) :=
        Nat.mul_le_mul_right _ h3

end Work.WilE8.Poly
