import Mathlib

namespace Work.WilE3.Lib

theorem card_nthRootsFinset_complex {N : ℕ} (hN : N ≠ 0) (ε : ℂ) (hε : ε ≠ 0) :
    (Polynomial.nthRootsFinset N ε).card = N := by
  classical
  -- An `N`-th primitive root of unity exists in `ℂ`.
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hN
  -- `Polynomial.nthRootsFinset N ε` is the underlying Finset of the multiset `nthRoots N ε`.
  rw [Polynomial.nthRootsFinset_def,
    -- The multiset of `N`-th roots of `ε` has no repetitions (it is the orbit of one root
    -- under multiplication by powers of `ζ`), so passing to the Finset does not change the count.
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hε), hζ.card_nthRoots]
  -- `ℂ` is algebraically closed, so `ε` has an `N`-th root.
  rw [ite_eq_left (IsAlgClosed.exists_pow_nat_eq ε (Nat.pos_of_ne_zero hN))]

end Work.WilE3.Lib
