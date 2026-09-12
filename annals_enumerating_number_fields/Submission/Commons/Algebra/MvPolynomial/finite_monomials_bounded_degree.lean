import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finsupp.Order

namespace Commons.Algebra.MvPolynomial

theorem finite_monomials_bounded_degree (r d : ℕ) :
    Finite {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d} := by
  classical
  let f : {s : Fin r →₀ ℕ // s.sum (fun _ k => k) ≤ d} → (Fin r → Fin (d + 1)) :=
    fun s i => ⟨s.1 i,
      Nat.lt_succ_of_le (le_trans (Finsupp.single_eval_le_sum (g := fun x => x) s.1
        (by simp) (fun x => Nat.zero_le x) i) s.2)⟩
  refine Finite.of_injective f ?_
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact Fin.ext_iff.mp (congr_fun hab i)

end Commons.Algebra.MvPolynomial