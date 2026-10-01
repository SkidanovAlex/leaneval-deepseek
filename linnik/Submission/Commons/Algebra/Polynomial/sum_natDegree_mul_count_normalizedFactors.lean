import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- For a monic polynomial `p` over a field, the sum of `deg Q * multiplicity Q` over the
distinct monic irreducible factors `Q` of `p` equals `deg p`. -/
theorem sum_natDegree_mul_count_normalizedFactors {F : Type*} [Field F] [DecidableEq F]
    (p : Polynomial F) (hp : p.Monic) :
    (∑ Q ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        Q.natDegree * (UniqueFactorizationMonoid.normalizedFactors p).count Q) = p.natDegree := by
  have hp0 : p ≠ 0 := hp.ne_zero
  -- `p` is the product of its normalized (monic) irreducible factors.
  have hprod : (UniqueFactorizationMonoid.normalizedFactors p).prod = p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors p
    rw [hp.leadingCoeff, Polynomial.C_1, one_mul] at h
    exact h
  -- every normalized factor of `p` is monic
  have hmonic : ∀ f ∈ UniqueFactorizationMonoid.normalizedFactors p, f.Monic := by
    intro f hf
    exact ((Polynomial.mem_normalizedFactors_iff (p := f) (q := p) hp0).mp hf).2.1
  -- rewrite the weighted sum over the distinct factors as a sum over the multiset
  calc ∑ Q ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        Q.natDegree * (UniqueFactorizationMonoid.normalizedFactors p).count Q
      = ∑ Q ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        (UniqueFactorizationMonoid.normalizedFactors p).count Q • Q.natDegree := by
        refine Finset.sum_congr rfl fun Q _ => ?_
        rw [Nat.nsmul_eq_mul, mul_comm]
    _ = ((UniqueFactorizationMonoid.normalizedFactors p).map Polynomial.natDegree).sum :=
        (Finset.sum_multiset_map_count (UniqueFactorizationMonoid.normalizedFactors p)
          Polynomial.natDegree).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors p).prod.natDegree :=
        (Polynomial.natDegree_multiset_prod_of_monic
          (t := UniqueFactorizationMonoid.normalizedFactors p) hmonic).symm
    _ = p.natDegree := by rw [hprod]

end Commons.Algebra.Polynomial