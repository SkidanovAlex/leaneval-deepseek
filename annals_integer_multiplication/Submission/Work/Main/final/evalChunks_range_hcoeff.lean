import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.chunks.evalChunks_hcoeff

namespace Work.Main.final

open Work.Main

/-- The coefficients of the product of the two truncated chunk polynomials vanish beyond degree
`2N - 2`: for `m ≥ 2N - 1` every term of the defining sum has `pchunk y b N (m - i) = 0`. -/
theorem hcoeff_eq_zero_of_le {x y b N m : ℕ} (hm : 2 * N - 1 ≤ m) :
    Work.Main.hcoeff x y b N m = 0 := by
  unfold Work.Main.hcoeff
  apply Finset.sum_eq_zero
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have him : i ≤ m := by omega
  have hy0 : Work.Main.pchunk y b N (m - i) = 0 := by
    unfold Work.Main.pchunk
    rw [if_neg (by omega)]
  rw [if_pos him, hy0, mul_zero]

/-- Evaluated at `2 ^ b`, the coefficients of the product of the chunk polynomials of `x` and `y`
recover `x * y`, for any list length `S ≥ 2N - 1`. -/
theorem evalChunks_range_hcoeff {x y b N S : ℕ} (hb : 1 ≤ b) (hx : x < 2 ^ (b * N))
    (hy : y < 2 ^ (b * N)) (hS : 2 * N - 1 ≤ S) :
    HvdH.evalChunks ((List.range S).map (fun m => Work.Main.hcoeff x y b N m)) b = x * y := by
  have hkey : HvdH.evalChunks ((List.range S).map (fun m => Work.Main.hcoeff x y b N m)) b
      = HvdH.evalChunks ((List.range (2 * N - 1)).map (fun m => Work.Main.hcoeff x y b N m)) b := by
    rw [Work.Main.chunks.evalChunksRangeMap, Work.Main.chunks.evalChunksRangeMap]
    have htail : (∑ i ∈ Finset.range (S - (2 * N - 1)),
        Work.Main.hcoeff x y b N ((2 * N - 1) + i) * 2 ^ (b * ((2 * N - 1) + i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcoeff_eq_zero_of_le (Nat.le_add_right _ _), zero_mul]
    rw [(Nat.add_sub_of_le hS).symm, Finset.sum_range_add, htail, add_zero]
  rw [hkey]
  exact Work.Main.chunks.evalChunks_hcoeff hb hx hy

end Work.Main.final
