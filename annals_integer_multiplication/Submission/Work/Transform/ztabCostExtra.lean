import Mathlib
import Submission.Work.Transform.ztabCost

namespace Work.Transform

/-- **Extra cost arithmetic for the `ζ`-table word (`dup` and two `roll 2` stages).**

Three further stages of the assembly of `Work.Transform.ztabWord` (after the stretch `ztabStretch`
has produced the stretched table `Bs` of length `k*r = T` and before/around the conjugation
`Work.Transform.conjVecWord`):

* `KernelLib.dup` on the stretched table, cost `Kdup * (vsz Bs + 1)`;
* `KernelLib.roll 2` to bring `int p` (the third value) above the two copies of `Bs`,
  cost `3 * Kroll * (vsz Bs + vsz Bs + isz p + 1)`;
* `KernelLib.roll 2` to bring `Bs` (the third value) above the conjugate `Bs'`,
  cost `3 * Kroll * (vsz Bs' + isz p + vsz Bs + 1)`.

With `vsz Bs ≤ k * (Cs + 2)` and `vsz Bs' ≤ k * (Cs + 2)` (both are consequences of `InDiscVec` and
`Cs = cvecSz p r = r*(2p+8) + r + 1`) and `isz p ≤ p + 2`, the three costs are at most the left
hand side below, which is claimed to be within `Kb2 * (T*p² + r*(p+1)^Kb2 + 1) + Kb2` for
`Kb2 = 1000*(Kdup + Kroll + 100) + 1000` (using `k*r = T` so that
`k*(Cs+2) = T*(2p+8) + T + 3k ≤ T*p²` for `p ≥ 100`). -/
theorem ztabCostExtra (p r T k Cs Kdup Kroll Kb2 : ℕ)
    (hp : 100 ≤ p) (hr : 2 ≤ r) (hk : 1 ≤ k) (hkr : k * r = T)
    (hCs : Cs = r * (2 * p + 8) + r + 1)
    (hKb2 : Kb2 = 1000 * (Kdup + Kroll + 100) + 1000) :
    Kdup * (k * (Cs + 2) + 1)
      + 3 * Kroll * (2 * (k * (Cs + 2)) + (p + 2) + 1)
      + 3 * Kroll * (2 * (k * (Cs + 2)) + (p + 2) + 1)
    ≤ Kb2 * (T * p ^ 2 + r * (p + 1) ^ Kb2 + 1) + Kb2 := by
  -- `T = k*r` with `k ≥ 1`, `r ≥ 2`: it dominates `r`, `k` and every `k`-multiple of `Cs`.
  have hrT : r ≤ T := by rw [← hkr]; exact Nat.le_mul_of_pos_left r hk
  have hT2 : 2 ≤ T := le_trans hr hrT
  have hkT : k ≤ T := by rw [← hkr]; exact Nat.le_mul_of_pos_right k (by omega)
  -- `k*(Cs+2) = T*(2p+8) + T + 3k ≤ T*p²`
  have hkCs2 : k * (Cs + 2) ≤ T * p ^ 2 := by
    have hkey : k * (Cs + 2) = T * (2 * p + 8) + T + 3 * k := by rw [hCs, ← hkr]; ring
    rw [hkey]
    have h1 : T * (2 * p + 8) + T + 3 * k ≤ T * (2 * p + 12) := by nlinarith [hkT]
    have h2 : T * (2 * p + 12) ≤ T * p ^ 2 := Nat.mul_le_mul_left T (by nlinarith [hp])
    omega
  -- the linear leftover `p + 3` is also below `T*p²`
  have hpp3 : p + 3 ≤ T * p ^ 2 := by nlinarith [hT2, hp]
  -- the common budget `W` of the right hand side
  set W := T * p ^ 2 + r * (p + 1) ^ Kb2 + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have hTp2W : T * p ^ 2 ≤ W := by omega
  have hkCs2W : k * (Cs + 2) ≤ W := le_trans hkCs2 hTp2W
  have hpp3W : p + 3 ≤ W := le_trans hpp3 hTp2W
  -- the three stages, each with a small coefficient in front
  have hA : k * (Cs + 2) + 1 ≤ 2 * W := by omega
  have hB : 2 * (k * (Cs + 2)) + (p + 2) + 1 ≤ 3 * W := by omega
  have p1 : Kdup * (k * (Cs + 2) + 1) ≤ Kdup * (2 * W) := Nat.mul_le_mul_left Kdup hA
  have p2 : 3 * Kroll * (2 * (k * (Cs + 2)) + (p + 2) + 1) ≤ 3 * Kroll * (3 * W) :=
    Nat.mul_le_mul_left (3 * Kroll) hB
  -- the accumulated coefficient is still below `Kb2`
  have hK : 2 * Kdup + 18 * Kroll ≤ Kb2 := by omega
  have hEq : Kdup * (2 * W) + 3 * Kroll * (3 * W) + 3 * Kroll * (3 * W)
      = (2 * Kdup + 18 * Kroll) * W := by ring
  have hfinal : (2 * Kdup + 18 * Kroll) * W ≤ Kb2 * W := Nat.mul_le_mul_right W hK
  linarith [p1, p2, hEq, hfinal]

end Work.Transform
