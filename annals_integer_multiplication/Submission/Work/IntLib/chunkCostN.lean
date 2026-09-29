import Mathlib
import Submission.Work.IntLib.chunkDefs

namespace Work.IntLib

/-- Pure arithmetic core of the cost bound for the `chunk` word.

With `P = N*(b+1)`, `T = X + N*(b+1) + Bz + Nz` the three cost branches
(`n1`, `n2` with its inner loop cost `Cloop`, and `n3`) are all bounded by
linear expressions in `T`, `(KC+134)*P` and `KC`, and their sum fits under
`4*(KC+1000)*T`. -/
theorem chunkCostN_arith (b N KC X Bz Nz n n1 n2 n3 Cl : ℕ)
    (hb : 1 ≤ b) (hN : 1 ≤ N)
    (h1 : n1 ≤ 264 * (X + Bz + Nz + N * (b + 1) + 1))
    (h2 : n2 ≤ 164 * (X + Bz + Nz + N * (b + 1) + 1) + Cl)
    (h3 : Cl ≤ (KC + 134) * (N * (b + 1)) + 2)
    (h4 : n3 ≤ 5 * (N * (b + 3) + X + Bz + Nz + X + 1 + (b + 1) + 0 + 1 + 0 + 22))
    (htot : n ≤ n1 + n2 + n3 + 12) :
    n ≤ 4 * (KC + 1000) * (X + N * (b + 1) + Bz + Nz) := by
  have hb1 : 2 ≤ b + 1 := by omega
  have hP2 : 2 ≤ N * (b + 1) := by nlinarith [Nat.mul_le_mul hN hb1]
  have h2N : 2 * N ≤ N * (b + 1) := by nlinarith [Nat.mul_le_mul_left N hb1]
  have hbP : b + 1 ≤ N * (b + 1) := by
    have := Nat.le_mul_of_pos_left (b + 1) (by omega : 0 < N)
    simpa using this
  nlinarith [h1, h2, h3, h4, htot, hP2, h2N, hbP]

theorem chunkCostN (x b N KC : ℕ) (hb : 1 ≤ b) (hN : 1 ≤ N) (n n1 n2 n3 Cloop : ℕ)
    (h1 : n1 ≤ 264 * (HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) + HvdH.isz (N : ℤ) + N * (b + 1) + 1))
    (h2 : n2 ≤ 164 * (HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) + HvdH.isz (N : ℤ) + N * (b + 1) + 1) + Cloop)
    (h3 : Cloop ≤ (KC + 134) * (N * (b + 1)) + 2)
    (h4 : n3 ≤ 5 * (N * (b + 3) + HvdH.isz (x : ℤ) + HvdH.isz (b : ℤ) + HvdH.isz (N : ℤ)
      + HvdH.isz (x : ℤ) + 1 + (b + 1) + 0 + 1 + 0 + 22))
    (htot : n ≤ n1 + n2 + n3 + 12) :
    n ≤ 4 * (KC + 1000) * (HvdH.isz (x : ℤ) + N * (b + 1) + HvdH.isz (b : ℤ) + HvdH.isz (N : ℤ)) := by
  exact chunkCostN_arith b N KC (HvdH.isz (x : ℤ)) (HvdH.isz (b : ℤ)) (HvdH.isz (N : ℤ))
    n n1 n2 n3 Cloop hb hN h1 h2 h3 h4 htot

end Work.IntLib
