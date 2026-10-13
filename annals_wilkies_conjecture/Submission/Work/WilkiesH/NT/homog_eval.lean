import Mathlib
import Submission.Work.WilkiesH.NT.HomogDefs

namespace Work.WilkiesH.NT

/-- `Finsupp.prod` of a power, taken over `Finsupp.cons k m`, splits into the contribution of the
new first coordinate and the product over the tail. -/
lemma prod_cons_pow {N : Type*} [CommMonoid N] {n : ℕ}
    (k : ℕ) (m : Fin n →₀ ℕ) (g : Fin (n + 1) → N) :
    (Finsupp.cons k m).prod (fun j e => g j ^ e)
      = g 0 ^ k * m.prod (fun i e => g i.succ ^ e) := by
  rw [Finsupp.prod_pow, Finsupp.prod_pow, Fin.prod_univ_succ]
  simp

/-- Evaluation of a homogenized monomial: the new variable contributes the factor `c ^ k`, and the
remaining variables contribute the ordinary monomial evaluation. -/
lemma eval_monomial_cons {R : Type*} [CommSemiring R] {n : ℕ} (c : R) (x : Fin n → R)
    (k : ℕ) (m : Fin n →₀ ℕ) (a : R) :
    MvPolynomial.eval (Fin.cons c x) (MvPolynomial.monomial (Finsupp.cons k m) a)
      = a * c ^ k * ∏ i ∈ m.support, x i ^ m i := by
  rw [MvPolynomial.eval_monomial, prod_cons_pow]
  simp only [Fin.cons_zero, Fin.cons_succ, Finsupp.prod]
  ring

theorem homog_eval {K : Type*} [Field K] {n d : ℕ} (P : MvPolynomial (Fin n) ℤ) (x : Fin n → K) :
    (Work.WilkiesH.NT.homog (K := K) P d).eval (Fin.cons 1 x)
      = (P.map (Int.castRingHom K)).eval x := by
  unfold homog
  rw [MvPolynomial.eval_sum, MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial_cons]
  simp

end Work.WilkiesH.NT
