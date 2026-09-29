import Mathlib
import Submission.Work.RedProj.Defs

namespace Work.RedProj

open scoped BigOperators

theorem monomial_eval (n m : ℕ) (hm : m ≤ n) (u v : ℂ) :
    monomial n m (fun _ => (u, v)) = u ^ m * v ^ (n - m) := by
  rw [monomial_apply_apply]
  rw [Fin.prod_univ_eq_prod_range (fun k => if k < m then u else v) n]
  rw [Finset.prod_ite]
  congr 1
  · rw [show {x ∈ Finset.range n | x < m} = Finset.range m from ?_,
      Finset.prod_const, Finset.card_range]
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · rw [show {x ∈ Finset.range n | ¬ x < m} = Finset.Ico m n from ?_,
      Finset.prod_const, Nat.card_Ico]
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega

end Work.RedProj
