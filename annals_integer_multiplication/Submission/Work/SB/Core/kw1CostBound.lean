import Mathlib
import Submission.Work.SB.Core.Kw1StageDefs

namespace Work.SB.Core

/-- Arithmetic bound for the cost of the `kw1` map stage.

Writing `S = N.size` and `C = (L + S + 1) * (S + 1)`, the two ingredients are
`L + S + 3 + S + 2 ≤ 5 * (L + S + 1)` and `S + 2 ≤ 2 * (S + 1)` (giving the `10 * K0` term),
and `L + S + 3 + S + 2 + 1 ≤ 6 * (L + S + 1)` (giving the `6 * K1` term); the trailing `+ K1`
is absorbed by `C ≥ 1`. -/
theorem kw1CostBound {K0 K1 M N L : ℕ} (hMN : M ≤ N) :
    M * (Work.SB.Core.kw1ElemCost K0 N L + K1 * (Work.SB.Core.kw1SizeOut N L + 1)) + K1
      ≤ (10 * K0 + 6 * K1 + 1) * (N + 1) * (L + N.size + 1) * (N.size + 1) := by
  rw [Work.SB.Core.kw1ElemCost, Work.SB.Core.kw1SizeOut]
  have hC1 : 1 ≤ (L + N.size + 1) * (N.size + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hX : L + N.size + 3 + N.size + 2 ≤ 5 * (L + N.size + 1) := by omega
  have hY : N.size + 2 ≤ 2 * (N.size + 1) := by omega
  have hXY := Nat.mul_le_mul hX hY
  have hK0 : K0 * (L + N.size + 3 + N.size + 2) * (N.size + 2)
      ≤ 10 * K0 * ((L + N.size + 1) * (N.size + 1)) := by
    rw [Nat.mul_assoc]
    calc K0 * ((L + N.size + 3 + N.size + 2) * (N.size + 2))
        ≤ K0 * ((5 * (L + N.size + 1)) * (2 * (N.size + 1))) := Nat.mul_le_mul_left _ hXY
      _ = 10 * K0 * ((L + N.size + 1) * (N.size + 1)) := by ring
  have hZ : L + N.size + 3 + N.size + 2 + 1 ≤ 6 * (L + N.size + 1) := by omega
  have hZt : L + N.size + 3 + N.size + 2 + 1
      ≤ 6 * (L + N.size + 1) * (N.size + 1) :=
    le_trans hZ (Nat.le_mul_of_pos_right _ (by omega))
  have hK1 : K1 * (L + N.size + 3 + N.size + 2 + 1)
      ≤ 6 * K1 * ((L + N.size + 1) * (N.size + 1)) := by
    calc K1 * (L + N.size + 3 + N.size + 2 + 1)
        ≤ K1 * (6 * (L + N.size + 1) * (N.size + 1)) := Nat.mul_le_mul_left _ hZt
      _ = 6 * K1 * ((L + N.size + 1) * (N.size + 1)) := by ring
  have hinner : K0 * (L + N.size + 3 + N.size + 2) * (N.size + 2)
      + K1 * (L + N.size + 3 + N.size + 2 + 1)
      ≤ (10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1)) := by linarith
  have hmul : M * (K0 * (L + N.size + 3 + N.size + 2) * (N.size + 2)
      + K1 * (L + N.size + 3 + N.size + 2 + 1))
      ≤ N * ((10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1))) :=
    le_trans (Nat.mul_le_mul_right _ hMN) (Nat.mul_le_mul_left _ hinner)
  have hK1le : K1 ≤ (10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1)) :=
    le_trans (by omega : K1 ≤ 10 * K0 + 6 * K1) (Nat.le_mul_of_pos_right _ hC1)
  calc M * (K0 * (L + N.size + 3 + N.size + 2) * (N.size + 2)
        + K1 * (L + N.size + 3 + N.size + 2 + 1)) + K1
      ≤ N * ((10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1)))
        + (10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1)) := by linarith
    _ = (N + 1) * ((10 * K0 + 6 * K1) * ((L + N.size + 1) * (N.size + 1))) := by ring
    _ = (10 * K0 + 6 * K1) * ((N + 1) * ((L + N.size + 1) * (N.size + 1))) := by ring
    _ ≤ (10 * K0 + 6 * K1 + 1) * ((N + 1) * ((L + N.size + 1) * (N.size + 1))) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (10 * K0 + 6 * K1 + 1) * (N + 1) * (L + N.size + 1) * (N.size + 1) := by ring

end Work.SB.Core
