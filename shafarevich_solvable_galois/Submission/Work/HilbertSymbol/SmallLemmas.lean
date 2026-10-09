/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Small auxiliary lemmas for the Hilbert-symbol computations
-/
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

theorem intUnitOf_neg_one_pow (k : ℕ) : intUnitOf ((-1 : ℤ) ^ k) = (-1 : ℤˣ) ^ k := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, h.neg_one_pow]; simp [intUnitOf]
  · rw [h.neg_one_pow, h.neg_one_pow]; simp [intUnitOf]

theorem prime_div_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p / 2 = (p - 1) / 2 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two h2
  omega

theorem legendreSym_eq_one_or_neg_one' {p : ℕ} [Fact p.Prime] {m : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) :
    legendreSym p m = 1 ∨ legendreSym p m = -1 := by
  rw [legendreSym]
  exact quadraticChar_dichotomy (by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd])

theorem legendreSym_eq_one_or_neg_one {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    legendreSym p q = 1 ∨ legendreSym p q = -1 := by
  refine legendreSym_eq_one_or_neg_one' (m := (q : ℤ)) ?_
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp
    (by exact_mod_cast h))

theorem intUnitOf_legendreSym_mul {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    intUnitOf (legendreSym p q) * intUnitOf (legendreSym q p)
      = intUnitOf (legendreSym p q * legendreSym q p) :=
  (intUnitOf_mul (legendreSym_eq_one_or_neg_one hpq)
    (legendreSym_eq_one_or_neg_one hpq.symm)).symm

theorem legendreSym_quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p
      = (-1) ^ (((p - 1) / 2 : ℕ) * ((q - 1) / 2 : ℕ)) := by
  rw [mul_comm, legendreSym.quadratic_reciprocity hp hq hpq, prime_div_two Fact.out hp,
    prime_div_two Fact.out hq]

end Work.HilbertSymbol
