import Mathlib
import Submission.Work.FUS.AutFacts.mulAut_cyclic_eq_one_of_odd

namespace Work.FUS

/-- For a finite cyclic group `A` of order `2 ^ k`, the automorphism group
`A ≃* A` has cardinality `Nat.totient (2 ^ k)`, which divides `2 ^ k`; hence it
is a 2-group. -/
theorem isPGroup_mulAut_cyclic {A : Type*} [Group A] [Finite A] (hcyc : IsCyclic A) (k : ℕ)
    (hcard : Nat.card A = 2 ^ k) : IsPGroup 2 (A ≃* A) := by
  refine IsPGroup.of_card_dvd_pow (n := k) ?_
  rw [@IsCyclic.card_mulAut A _ _ hcyc, hcard]
  exact Work.FUS.AutFacts.totient_two_pow_dvd k

end Work.FUS
