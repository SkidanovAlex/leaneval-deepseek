import Submission.CertSsumAll

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# An evaluation-friendly form of the packed contraction

`pw u = ∑_i u_i · BP^i` and `blk X Y R = (X·Y·Kwz R / BP^50) % BP` are written with `Nat.pow`
and with the `Kwz` sum over `Finset.range`; evaluation then recomputes `BP^i` and `Kwz R`
repeatedly.  Here we give the same objects with shifts (`<<<`, `>>>`) and with a *list* of the
`51` values of `Kwz`, so that the final numeric verification of the certificate costs a single
`decide` over the table `ssumTableL`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem shift_eq_mul_BP (z i : ℕ) : z <<< (2048 * i) = z * BP ^ i := by
  rw [Nat.shiftLeft_eq, BP, ← pow_mul]

/-- `pw` with shifts instead of powers. -/
def pwS (u : List ℕ) : ℕ := (u.zipIdx.map (fun p => p.1 <<< (2048 * p.2))).sum

theorem pwS_eq (u : List ℕ) : pwS u = pw u := by
  unfold pwS pw
  exact congrArg List.sum (List.map_congr_left (fun p _ => shift_eq_mul_BP p.1 p.2))

/-- The `51` values of the packed kernel `Kwz`. -/
def KwzL : List ℕ := (List.range 51).map Kwz

theorem KwzL_getD (R : ℕ) (hR : R < 51) : KwzL.getD R 0 = Kwz R := by
  unfold KwzL
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hR),
    List.getElem_map, List.getElem_range (by rw [List.length_range]; exact hR)]

/-- The block extraction with shifts and the kernel table. -/
def blkS (X Y R : ℕ) : ℕ := ((X * Y * KwzL.getD R 0) >>> 102400) % (1 <<< 2048)

theorem blkS_eq (X Y R : ℕ) (hR : R < 51) : blkS X Y R = blk X Y R := by
  unfold blkS blk
  rw [KwzL_getD R hR, Nat.shiftRight_eq_div_pow,
    show (2 : ℕ) ^ 102400 = BP ^ 50 from by rw [BP, ← pow_mul],
    show (1 : ℕ) <<< 2048 = BP from by rw [Nat.shiftLeft_eq, BP]; norm_num]

/-- The packed contraction with shifts and the kernel table. -/
def contPackS (v v' : List ℤ) (R : ℕ) : ℤ :=
  ((blkS (pwS (vpos v)) (pwS (vpos v')) R : ℕ) : ℤ)
    - ((blkS (pwS (vpos v)) (pwS (vneg v')) R : ℕ) : ℤ)
    - ((blkS (pwS (vneg v)) (pwS (vpos v')) R : ℕ) : ℤ)
    + ((blkS (pwS (vneg v)) (pwS (vneg v')) R : ℕ) : ℤ)

theorem contPackS_eq (v v' : List ℤ) (R : ℕ) (hR : R < 51) :
    contPackS v v' R = contPack v v' R := by
  unfold contPackS contPack
  rw [pwS_eq, pwS_eq, pwS_eq, pwS_eq, blkS_eq _ _ _ hR, blkS_eq _ _ _ hR,
    blkS_eq _ _ _ hR, blkS_eq _ _ _ hR]

end Commons.NumberTheory.MaynardSieve
