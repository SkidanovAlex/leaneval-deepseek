import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSPB1.Basic

/-!
# `ϖ_k` is not a unit when `p` is not a unit

For a perfectoid datum `P : DSMap.PerfectoidData p C` the pseudo-uniformizer `ϖ_k` is a
`p`-power root tower of `ϖ_0` (`P.root`), and `ϖ_0 ^ p = p * v` for a unit `v` (`P.unit`).
Iterating the root tower gives `ϖ_k ^ (p ^ k) = ϖ_0` (`Work.DSPB1.varpi_pow_iterate_zero`).

If `ϖ_k` were a unit, then so would be `ϖ_0 = ϖ_k ^ (p ^ k)`, hence `ϖ_0 ^ p = p * v` and so
`p = ϖ_0 ^ p * v⁻¹` would be a unit, contradicting `Fact ¬IsUnit (p : C)`.
-/

namespace Work.DSPB1.Varpi

/-- The pseudo-uniformizer `ϖ_k` of a `DSMap.PerfectoidData` is not a unit, provided `p` is not
a unit in the coefficient ring. -/
theorem varpi_not_isUnit {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)] (k : ℕ) : ¬ IsUnit (P.ϖ k) := by
  intro hu
  -- `ϖ_k ^ (p ^ k) = ϖ_0`, so `ϖ_0` is a unit.
  have hpow : P.ϖ k ^ p ^ k = P.ϖ 0 := Work.DSPB1.varpi_pow_iterate_zero P k
  have hu0 : IsUnit (P.ϖ 0) := by
    rw [← hpow]
    exact hu.pow (p ^ k)
  -- `ϖ_0 ^ p = p * v` with `v` a unit, so `p` is a unit.
  obtain ⟨v, hv⟩ := P.unit
  have hpunit : IsUnit (p : C) := by
    have hp : (p : C) = P.ϖ 0 ^ p * ↑(v⁻¹) := by
      rw [hv, mul_assoc, Units.mul_inv, mul_one]
    rw [hp]
    exact IsUnit.mul (hu0.pow p) v⁻¹.isUnit
  exact (Fact.out : ¬ IsUnit (p : C)) hpunit

end Work.DSPB1.Varpi
