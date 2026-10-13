import Mathlib
import Submission.Work.DSM1p.Basic

namespace Work.DSM1p.Perfectoid

/-- Each pseudo-uniformizer `ϖ k` of a `DSMap.PerfectoidData` is a non-zerodivisor.

`ϖ 0 ^ p = p * v` with `v` a unit shows `ϖ 0` is a non-zerodivisor (as `p` is one, and a
unit is one, and `IsSMulRegular.pow_iff` strips the `p`-th power), and the root relations
`ϖ (k+1) ^ p = ϖ k` propagate this up the tower. -/
theorem varpi_isSMulRegular {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (P : DSMap.PerfectoidData p A) (k : ℕ) : IsSMulRegular A (P.ϖ k) := by
  have hp : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have h0 : IsSMulRegular A (P.ϖ 0) := by
    obtain ⟨v, hv⟩ := P.unit
    have hpv : IsSMulRegular A ((p : A) * (v : A)) :=
      P.torsionFree.mul (Units.isSMulRegular (M := A) v)
    rw [← hv] at hpv
    exact (IsSMulRegular.pow_iff (M := A) (n := p) hp).mp hpv
  induction k with
  | zero => exact h0
  | succ k ih =>
    have : IsSMulRegular A (P.ϖ (k + 1) ^ p) := by rw [P.root k]; exact ih
    exact (IsSMulRegular.pow_iff (M := A) (n := p) hp).mp this

theorem varpi_smul_eq_zero_iff {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]
    (P : DSMap.PerfectoidData p A) (k : ℕ) (x : A) :
    P.ϖ k * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact varpi_isSMulRegular P k
      (show (P.ϖ k) • x = (P.ϖ k) • (0 : A) by
        rw [smul_eq_mul, smul_zero, h])
  · intro h
    rw [h, mul_zero]

end Work.DSM1p.Perfectoid
