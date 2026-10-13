import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.perfChartRing_pow_p_mem_iff
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.frobenius_surjective_away
import Submission.Work.DSM5b.frobenius_injective_away
import Submission.Work.DSM5b.sum_pow_p_away

/-!
# DSM5b — auxiliary lemmas for `Work.DSM5b.phiPC_properties`

These are the elementary ring-theoretic pieces used by the proof of
`Work.DSM5b.phiPC_properties` (the Frobenius `p`-th power map of the explicit perfected chart
Čech complex `PCX`/`PCd` of `Submission/Work/DSM5b/PerfComplexDefs.lean`).  They are kept in a
separate module so that the file of the target theorem consists of the statement alone.

* `neg_one_pow_prime`, `neg_one_pow_pow_prime`: in a commutative ring of characteristic the prime
  `p`, the signs `(-1) ^ i` are fixed by the `p`-th power map.  This is what allows the
  componentwise `p`-th power map to pass through the alternating signs of the differential `PCd`.
* `sum_smul_pow_p_away`: Freshman's dream for the signed sum `∑ i, (-1)^i • u i` in a localisation
  away from an element of such a ring (the localisation has `(p : ·) = 0` even though it carries no
  `CharP` instance; additivity of the `p`-th power map there is `sum_pow_p_away`).
* `rho_phiPC_val`: the restriction maps `rho` of the perfected chart rings are ring homomorphisms,
  hence commute with the componentwise `p`-th power map.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

/-- In a commutative ring of characteristic the prime `p`, `(-1) ^ p = -1` (for `p = 2` this is
`1 = -1` in characteristic `2`). -/
lemma neg_one_pow_prime (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] :
    (-1 : R) ^ p = -1 := by
  rcases Nat.Prime.eq_two_or_odd' (Fact.out : p.Prime) with h | h
  · subst h
    have h2 : (2 : R) = 0 := by simpa using CharP.cast_eq_zero R 2
    have hone : (1 : R) = -1 := by
      apply eq_neg_of_add_eq_zero_right
      rw [← two_mul]
      simpa using h2
    rw [pow_two, neg_mul_neg, one_mul]
    exact hone
  · exact Odd.neg_one_pow h

/-- The signs `(-1) ^ i` are fixed by the `p`-th power map in characteristic `p`. -/
lemma neg_one_pow_pow_prime (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] (i : ℕ) :
    ((-1 : R) ^ i) ^ p = (-1 : R) ^ i := by
  rw [← pow_mul, mul_comm i p, pow_mul, neg_one_pow_prime p]

/-- Freshman's dream for the signed sum: in a localisation `R[1/f]` of a ring of characteristic
`p`, the `p`-th power map is additive (`sum_pow_p_away`) and fixes the coefficients `(-1)^i`
(`neg_one_pow_pow_prime`), so it distributes over `∑ i, (-1)^i • u i`. -/
lemma sum_smul_pow_p_away (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] (f : R)
    (n : ℕ) (u : Fin n → Localization.Away f) :
    (∑ i : Fin n, algebraMap R (Localization.Away f) ((-1 : R) ^ (i : ℕ)) * u i) ^ p =
      ∑ i : Fin n, algebraMap R (Localization.Away f) ((-1 : R) ^ (i : ℕ)) * (u i) ^ p := by
  refine Eq.trans (sum_pow_p_away p f (α := Fin n) Finset.univ
    (fun i => algebraMap R (Localization.Away f) ((-1 : R) ^ (i : ℕ)) * u i)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← map_pow, neg_one_pow_pow_prime p]

/-- The localisation maps `rho` between perfected chart rings commute with the componentwise
`p`-th power map `phiPC`. -/
lemma rho_phiPC_val (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (m : ℕ) (z : PCX p t m)
    (σ : Fin (m + 1) → ι) {T : Finset ι} (h : tupRng σ ⊆ T) :
    ((rho p t h (phiPC p t m z σ) : perfChartRing p t T) : Localization.Away (tS t T)) =
      (((rho p t h (z σ) : perfChartRing p t T)) : Localization.Away (tS t T)) ^ p := by
  rw [rho_coe, rho_coe, phiPC_apply, map_pow]

end Work.DSM5b
