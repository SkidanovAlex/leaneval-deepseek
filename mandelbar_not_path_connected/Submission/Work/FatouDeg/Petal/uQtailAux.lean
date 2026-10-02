import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

theorem uQtailAux (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ)
    (hcoef : ∀ j : ℕ, j < m - 1 → ((upoly G) * (Qpoly m G)).coeff j = if j = 0 then 1 else 0) :
    ∃ B : Polynomial ℂ, upoly G * Qpoly m G - 1
        - Polynomial.C (((upoly G) * (Qpoly m G)).coeff (m - 1)) * Polynomial.X ^ (m - 1)
        = Polynomial.X ^ m * B := by
  have hdvd : Polynomial.X ^ m ∣ upoly G * Qpoly m G - 1
      - Polynomial.C (((upoly G) * (Qpoly m G)).coeff (m - 1)) * Polynomial.X ^ (m - 1) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have hdle : d ≤ m - 1 := by omega
    rcases lt_or_eq_of_le hdle with hlt | heq
    · rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, ite_eq_right (by omega : d ≠ m - 1), hcoef d hlt]
      by_cases hd0 : d = 0 <;> simp [hd0]
    · subst heq
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_self, ite_eq_right (by omega : m - 1 ≠ 0)]
      ring
  obtain ⟨B, hB⟩ := hdvd
  exact ⟨B, hB⟩

end Work.FatouDeg.Petal
