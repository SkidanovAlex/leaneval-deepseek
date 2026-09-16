import Mathlib
import Submission.Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

namespace Commons.Algebra.Polynomial



/-- **Multiplicity bookkeeping for a monic divisor.** If `E` is monic and every monic irreducible
divisor `r` of `E` divides a fixed `b`, then `E` divides `b ^ E.natDegree`.

Proof: `E` is a product `∏ i, r i ^ e i` of powers of monic irreducibles (its `factors`), each
`r i ∣ b` gives `r i ^ e i ∣ b ^ e i`, so `E ∣ b ^ (∑ e i)`; and `∑ e i ≤ E.natDegree`
(`Polynomial.natDegree_prod_le` + `natDegree_pow` + multiplicativity, or
`Polynomial.sum_natDegree_eq_natDegree` on the factorisation). -/
theorem dvd_pow_natDegree_of_forall_monic_irreducible_dvd {K : Type*} [Field K] {E b : Polynomial K}
    (hE : E.Monic)
    (hb : ∀ r : Polynomial K, r.Monic → Irreducible r → r ∣ E → r ∣ b) :
    E ∣ b ^ E.natDegree := by
  classical
  set s := UniqueFactorizationMonoid.normalizedFactors E with hs
  have hE0 : E ≠ 0 := hE.ne_zero
  -- Each normalized factor is monic, irreducible and divides `E`.
  have hfac : ∀ r ∈ s.toFinset, r.Monic ∧ Irreducible r ∧ r ∣ E := by
    intro r hr
    have hmem : r ∈ UniqueFactorizationMonoid.normalizedFactors E :=
      hs ▸ Multiset.mem_toFinset.mp hr
    have := (_root_.Polynomial.mem_normalizedFactors_iff (p := r) (q := E) hE0).mp hmem
    exact ⟨this.2.1, this.1, this.2.2⟩
  -- `E` is the product of its distinct normalized factors raised to their multiplicities.
  have hprod : (∏ r ∈ s.toFinset, r ^ s.count r) = E := by
    rw [← Finset.prod_multiset_count s, hs]
    exact Commons.FieldTheory.Polynomial.prod_normalizedFactors_of_monic E hE
  -- The sum of the multiplicities is at most the degree of `E`.
  have hsum := Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors E hE
  rw [← hs] at hsum
  have hle : (∑ r ∈ s.toFinset, s.count r) ≤ E.natDegree := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro r hr
    have hpos : 1 ≤ r.natDegree := (hfac r hr).2.1.natDegree_pos
    calc s.count r = 1 * s.count r := (one_mul _).symm
      _ ≤ r.natDegree * s.count r := Nat.mul_le_mul_right _ hpos
  -- `E` divides `b ^ (∑ multiplicities)`.
  have hstep1 : E ∣ b ^ (∑ r ∈ s.toFinset, s.count r) := by
    rw [← hprod]
    calc (∏ r ∈ s.toFinset, r ^ s.count r)
        ∣ (∏ r ∈ s.toFinset, b ^ s.count r) := by
          apply Finset.prod_dvd_prod_of_dvd
          intro r hr
          exact pow_dvd_pow_of_dvd
            (hb r (hfac r hr).1 (hfac r hr).2.1 (hfac r hr).2.2) (s.count r)
      _ = b ^ (∑ r ∈ s.toFinset, s.count r) :=
          Finset.prod_pow_eq_pow_sum s.toFinset (fun r => s.count r) b
  exact hstep1.trans (pow_dvd_pow b hle)

end Commons.Algebra.Polynomial
