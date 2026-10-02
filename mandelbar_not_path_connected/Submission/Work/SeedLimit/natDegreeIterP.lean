import Mathlib
import Submission.Work.FBif.IterPoly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

/-- **The degree of the polynomial of the `n`-th iterate.**  `Work.FBif.iterP c n` is the polynomial
with `(iterP c n).eval = (T_c)^[n]` on the even iterates (`Work.FBif.iterP_ten_eval`), and it has
degree `2 ^ n`: `iterP c 0 = X` has degree `1`, and
`iterP c (n+1) = (iterP c n).map star ^ 2 + C c` squares the degree
(`Polynomial.natDegree_map`, `Polynomial.natDegree_pow`, and the degree of a sum with a constant
term, the leading degree being `≥ 2`).

This is the polynomial-degree witness needed to apply `Work.FatouParabolic.FatouParabolicInput` to
the holomorphic return map `(Tsq c)^[5] = (T_c)^[10] = fun z => (iterP c 10).eval z` of the
period-`5` cycle (degree `1024 ≥ 2`), which is step NC6 of
`NOTES_LEAD_mandelbar_noncusp.md` §5.1. -/
theorem natDegreeIterP (c : ℂ) (n : ℕ) : (Work.FBif.iterP c n).natDegree = 2 ^ n := by
  induction n with
  | zero => simp [Work.FBif.iterP]
  | succ n ih =>
    rw [Work.FBif.iterP]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_pow, Polynomial.natDegree_map, ih, pow_succ, Nat.mul_comm]
    · rw [Polynomial.natDegree_C, Polynomial.natDegree_pow, Polynomial.natDegree_map, ih]
      positivity

end Work.SeedLimit
