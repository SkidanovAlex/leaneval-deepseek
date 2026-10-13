import Mathlib
import Submission.Work.DSMap.Map

/-!
# `Work.DSPB1.Varpi.varpi_ne_zero`

The pseudo-uniformizer `ϖ_k` of a `DSMap.PerfectoidData` is non-zero.

The only inputs are the defining data of `PerfectoidData`:
* `P.root : ϖ_{k+1}^p = ϖ_k`,
* `P.unit : ϖ_0^p = p * v` for a unit `v`,
* `P.torsionFree : IsSMulRegular C (p : C)` (`p` is not a zero divisor in `C`),
together with the hypothesis `Fact ¬IsUnit (p : C)`.

Argument:
* `IsSMulRegular C (p : C)` together with `¬IsUnit (p : C)` forces `(p : C) ≠ 0`: if `p = 0`
  then `IsSMulRegular C 0` makes `C` a subsingleton, in which case `(p : C) * 0 = 1`, i.e. `p`
  is a unit, a contradiction;
* `ϖ_0^p = p * v` with `v` a unit and `(p : C) ≠ 0` forces `ϖ_0 ≠ 0`;
* iterating `P.root` gives `ϖ_k^{p^k} = ϖ_0`, so `ϖ_k = 0` forces `ϖ_0 = 0`.
-/

namespace Work.DSPB1.Varpi

section Varpi

variable {p : ℕ} {C : Type*} [CommRing C]

/-- `ϖ_{k+n}^{p^n} = ϖ_k`: the tower of `p`-power roots of the pseudo-uniformizer. -/
theorem varpi_pow_add (P : DSMap.PerfectoidData p C) (k n : ℕ) :
    P.ϖ (k + n) ^ p ^ n = P.ϖ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc P.ϖ (k + (n + 1)) ^ p ^ (n + 1)
        = (P.ϖ (k + n + 1) ^ p) ^ p ^ n := by
          rw [Nat.add_succ, pow_succ', pow_mul]
      _ = P.ϖ (k + n) ^ p ^ n := by rw [P.root (k + n)]
      _ = P.ϖ k := ih

/-- `ϖ_n^{p^n} = ϖ_0`. -/
theorem varpi_pow_self (P : DSMap.PerfectoidData p C) (n : ℕ) :
    P.ϖ n ^ p ^ n = P.ϖ 0 := by
  simpa using varpi_pow_add P 0 n

end Varpi

theorem varpi_ne_zero {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)] (k : ℕ) : P.ϖ k ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  -- `p` is not zero in `C`
  have hpz : (p : C) ≠ 0 := by
    intro hp0
    have hreg : IsSMulRegular C (0 : C) := hp0 ▸ P.torsionFree
    have hsingle : Subsingleton C := ⟨fun a b => hreg (by simp)⟩
    exact (Fact.out : ¬ IsUnit (p : C))
      ⟨(1 : Cˣ), hsingle.elim (1 : C) (p : C)⟩
  -- `ϖ_0 ≠ 0`
  have h0 : P.ϖ 0 ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := P.unit
    have hvz : (↑v : C) * (p : C) = 0 := by
      rw [mul_comm, ← hv, h, zero_pow hp]
    exact hpz ((Units.mul_right_eq_zero v).mp hvz)
  -- `ϖ_k = 0` would force `ϖ_0 = 0`
  intro hk
  have hpow := varpi_pow_self P k
  rw [hk, zero_pow (pow_ne_zero k hp)] at hpow
  exact h0 hpow.symm

end Work.DSPB1.Varpi
