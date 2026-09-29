import Mathlib
import Submission.Work.SB.BW2.Defs

namespace Work.SB.BW2

open HvdH

/-! ## Size arithmetic used by `degSize`

`BIG N L = (N+1)*(L+N.size+1)*(N.size+1)` and `S A m B = isz A + isz m + isz B`, where
`isz z = z.natAbs.size + 2`.  The facts collected here say that `BIG` dominates `N+1` (hence
`A*B+1` as soon as `A*B ≤ N`), that `BIG` dominates `(N.size+1)^2`, and that an integer of
absolute value `≤ N` has `isz ≤ N.size + 2`. -/

/-- `BIG N L ≥ N+1`. -/
private theorem succ_le_BIG (N L : ℕ) : N + 1 ≤ BIG N L := by
  simp only [BIG]
  calc N + 1 = (N + 1) * 1 * 1 := by ring
    _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- `BIG` is never zero. -/
private theorem one_le_BIG (N L : ℕ) : 1 ≤ BIG N L :=
  le_trans (Nat.le_add_left 1 N) (succ_le_BIG N L)

/-- `BIG N L ≥ (N.size + 1)^2`. -/
private theorem size_sq_le_BIG (N L : ℕ) : (N.size + 1) * (N.size + 1) ≤ BIG N L := by
  simp only [BIG]
  calc (N.size + 1) * (N.size + 1) = 1 * (N.size + 1) * (N.size + 1) := by ring
    _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (le_refl _)

/-- `n.size ≤ n`. -/
private theorem size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.mpr (by simpa using Nat.lt_two_pow_self (n := n))

/-- The `isz` of `A : ℤ` is one of the three summands of `S A m B`. -/
private theorem iszA_le_S (A m B : ℕ) : isz (A : ℤ) ≤ S A m B := by
  simp only [S]; omega

/-- The `isz` of `B : ℤ` is one of the three summands of `S A m B`. -/
private theorem iszB_le_S (A m B : ℕ) : isz (B : ℤ) ≤ S A m B := by
  simp only [S]; omega

/-- An integer `k ≤ N` has `isz ≤ N.size + 2`. -/
private theorem isz_nat_le_succ_size (k N : ℕ) (h : k ≤ N) : isz (k : ℤ) ≤ N.size + 2 := by
  have h1 : k.size ≤ N.size := Nat.size_le_size h
  simp only [isz, Int.natAbs_natCast]
  omega

theorem degSize (A B N L m : ℕ) (hAB : A * B ≤ N) :
    1 ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B ∧
    HvdH.isz (A : ℤ) ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B ∧
    HvdH.isz (B : ℤ) ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B ∧
    HvdH.isz (A : ℤ) * HvdH.isz (B : ℤ)
      ≤ 4 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.isz ((A * B : ℕ) : ℤ) ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    A * B + 1 ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B := by
  have hB1 : 1 ≤ BIG N L := one_le_BIG N L
  have hBN : N + 1 ≤ BIG N L := succ_le_BIG N L
  have hsA : isz (A : ℤ) ≤ S A m B := iszA_le_S A m B
  have hsB : isz (B : ℤ) ≤ S A m B := iszB_le_S A m B
  -- the product `A*B` is not larger than `N`, so its size fits twice into `BIG + S`
  have hsz : isz ((A * B : ℕ) : ℤ) ≤ 2 * (BIG N L + S A m B) := by
    have h1 : (A * B).size ≤ N.size := Nat.size_le_size hAB
    have h2 : N.size ≤ N := size_le_self N
    simp only [isz, Int.natAbs_natCast]
    omega
  -- the two factors of `A*B` either are small (`0`) or bounded by `N`
  have hab : isz (A : ℤ) * isz (B : ℤ) ≤ 4 * (BIG N L + S A m B) := by
    by_cases hA0 : A = 0
    · simp only [hA0, isz, S, Int.natAbs_natCast, Nat.size_zero]
      omega
    · by_cases hB0 : B = 0
      · simp only [hB0, isz, S, Int.natAbs_natCast, Nat.size_zero]
        omega
      · have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr hA0
        have hB1' : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB0
        have hAle : A ≤ N := by
          calc A = A * 1 := (Nat.mul_one A).symm
            _ ≤ A * B := Nat.mul_le_mul_left A hB1'
            _ ≤ N := hAB
        have hBle : B ≤ N := by
          calc B = 1 * B := (Nat.one_mul B).symm
            _ ≤ A * B := Nat.mul_le_mul_right B hA1
            _ ≤ N := hAB
        have ha : isz (A : ℤ) ≤ N.size + 2 := isz_nat_le_succ_size A N hAle
        have hb : isz (B : ℤ) ≤ N.size + 2 := isz_nat_le_succ_size B N hBle
        have hmul : isz (A : ℤ) * isz (B : ℤ) ≤ (N.size + 2) * (N.size + 2) :=
          Nat.mul_le_mul ha hb
        have hsq : (N.size + 2) * (N.size + 2) ≤ 4 * ((N.size + 1) * (N.size + 1)) := by
          nlinarith [Nat.zero_le N.size]
        have hsqB : 4 * ((N.size + 1) * (N.size + 1)) ≤ 4 * BIG N L :=
          Nat.mul_le_mul_left 4 (size_sq_le_BIG N L)
        calc isz (A : ℤ) * isz (B : ℤ)
            ≤ (N.size + 2) * (N.size + 2) := hmul
          _ ≤ 4 * ((N.size + 1) * (N.size + 1)) := hsq
          _ ≤ 4 * BIG N L := hsqB
          _ ≤ 4 * (BIG N L + S A m B) := by omega
  refine ⟨?_, ?_, ?_, hab, hsz, ?_⟩
  · omega
  · omega
  · omega
  · omega

end Work.SB.BW2
