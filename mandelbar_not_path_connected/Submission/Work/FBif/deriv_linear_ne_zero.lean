import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- For a polynomial `P` of degree at least `3` and a nonzero constant `ε`, the linear
polynomial `2X + ε P'` is not the zero polynomial.  Indeed `P'` has degree `natDegree P - 1 ≥ 2`,
so the term `ε P'` cannot cancel the degree-one term `2X`; formally, the coefficient of
`2X + ε P'` at index `natDegree P - 1` equals `ε * P.leadingCoeff * P.natDegree ≠ 0`. -/
theorem deriv_linear_ne_zero {P : Polynomial ℂ} (hdeg : 3 ≤ P.natDegree) {ε : ℂ}
    (hε : ¬ (ε = 0)) :
    ¬ (Polynomial.C 2 * Polynomial.X + Polynomial.C ε * P.derivative = 0) := by
  intro h
  -- `3 ≤ P.natDegree` forces `P ≠ 0`.
  have hP_ne : P ≠ 0 := by
    intro hP; rw [hP] at hdeg; simp at hdeg
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  -- Look at the coefficient of `2X + ε P'` at index `n = P.natDegree - 1`.
  set n : ℕ := P.natDegree - 1 with hn_def
  have hn1 : n + 1 = P.natDegree := by rw [hn_def]; omega
  have hn_ne1 : n ≠ 1 := by rw [hn_def]; omega
  have hnc : (n : ℂ) + 1 = (P.natDegree : ℂ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hn1]
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff n) h
  simp only [Polynomial.coeff_zero] at hcoeff
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative, Polynomial.coeff_X, if_neg (Ne.symm hn_ne1),
      hn1, Polynomial.coeff_natDegree, hnc] at hcoeff
  -- The coefficient is `ε * P.leadingCoeff * P.natDegree`, a product of nonzero factors.
  have hnd : (P.natDegree : ℂ) ≠ 0 := by
    have : P.natDegree ≠ 0 := by omega
    exact_mod_cast this
  have hne : ε * (P.leadingCoeff * (P.natDegree : ℂ)) ≠ 0 :=
    mul_ne_zero hε (mul_ne_zero hlc hnd)
  simp only [mul_zero, zero_add] at hcoeff
  exact hne hcoeff

end Work.FBif
