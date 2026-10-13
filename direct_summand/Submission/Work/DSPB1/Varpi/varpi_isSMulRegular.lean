import Mathlib
import Submission.Work.DSMap.Map

/-!
# The pseudo-uniformizer `ϖ k` is a non-zero-divisor

For a `DSMap.PerfectoidData p C` — a `p`-torsion-free ring `C` together with a compatible
system of `p`-power roots `P.ϖ` of a pseudo-uniformizer, satisfying
`P.ϖ (k+1) ^ p = P.ϖ k` (`P.root`) and `P.ϖ 0 ^ p = p * v` for a unit `v` (`P.unit`) — every
element `P.ϖ k` is a non-zero-divisor on `C`.

The proof is by induction on `k`: `P.ϖ 0 ^ p = p * v` is the product of the `p`-torsion-free
element `p` with the unit `v`, hence `P.ϖ 0 ^ p` and therefore `P.ϖ 0` is regular; and regularity
is preserved upward along the root system by `IsSMulRegular.pow_iff`.
-/

namespace Work.DSPB1.Varpi

theorem varpi_isSMulRegular {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    (P : DSMap.PerfectoidData p C) (k : ℕ) : IsSMulRegular C (P.ϖ k) := by
  obtain ⟨v, hv⟩ := P.unit
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h0 : IsSMulRegular C (P.ϖ 0) := by
    have hvp : IsSMulRegular C ((p : C) * (v : C)) :=
      P.torsionFree.mul (Units.isSMulRegular C v)
    rw [← hv] at hvp
    exact (IsSMulRegular.pow_iff hp).mp hvp
  induction k with
  | zero => exact h0
  | succ k ih =>
      exact (IsSMulRegular.pow_iff (a := P.ϖ (k + 1)) hp).mp (by rw [P.root k]; exact ih)

end Work.DSPB1.Varpi
