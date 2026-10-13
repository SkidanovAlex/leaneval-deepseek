import Mathlib

namespace Work.DSM5b.HCF

universe u

/-- **A product of powers of elements of an ideal lies in the corresponding ideal power**:
for `t : ι → R` with all `t i ∈ J`, the monomial `∏_i t_i^{a_i}` (a `Finsupp.prod` over
`a : ι →₀ ℕ`) lies in `J ^ a.degree` where `a.degree = ∑_i a_i`.  Route: induct on `a` using
`Finsupp.induction`, `J^m * J^n = J^{m+n}` and `Ideal.pow_mem_pow`. -/
theorem prod_pow_mem_pow {ι : Type*} {R : Type u} [CommRing R] (J : Ideal R) (t : ι → R)
    (ht : ∀ i, t i ∈ J) (a : ι →₀ ℕ) :
    a.prod (fun i k => t i ^ k) ∈ J ^ a.degree := by
  classical
  rw [Finsupp.prod, Finsupp.degree_apply]
  have h := SetLike.prod_pow_mem_graded (A := fun n : ℕ => J ^ n) (F := a.support)
    (i := fun _ => (1 : ℕ)) (n := fun i => a i) (g := t) (fun i _ => by simpa using ht i)
  simpa using h

end Work.DSM5b.HCF
