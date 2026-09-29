import Mathlib
import Submission.Work.Resample.auPiWord
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auPrepDefs

/-!
# `Work.Resample.auKDefs`: the window-centre values `auK s t k`, `auK s t (k+1)`

The word `auKWord` computes the two window centres `auK s t k = ⌊(2ks+t)/(2t)⌋` and
`auK s t (k+1)` from the three integers `k, s, t`, by dividing `2ks + t` and `(2ks+t) + 2s`
by `2t`.

This module fixes the intermediate *integer* values of that program (`kE`, `kP`, `kA0`, `kD`,
`kA1`, `kQ0`, `kQ1`), identifies them with the natural-number expressions of the definition
(`kQ0 s t k = ↑(auK s t k)`, `kQ1 s t k = ↑(auK s t (k+1))`), and collects the size bounds
(`isz _ ≤ SZ p`) and the cost-absorption lemmas used by the two words.

The size/cost toolkit (`SB`, `SZ`, `le_SB_one/two/three/sq/roll`, `vsz_mem_le*`) is the one of
`Work.Resample.AuPiKit` (in `auPiWord.lean`): `SZ p = 8p+8` is a uniform bit-size bound and
`SB p KS = KS·(SZ p + 8)²` a uniform one-step cost bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx
open Work.Resample.AuPiKit

/-! ## The intermediate values -/

/-- `2s` -/
def kE (s : ℕ) : ℤ := (2 : ℤ) * (s : ℤ)

/-- `k·(2s) = 2ks` -/
def kP (s k : ℕ) : ℤ := (k : ℤ) * kE s

/-- `2ks + t` -/
def kA0 (s t k : ℕ) : ℤ := kP s k + (t : ℤ)

/-- `2t` -/
def kD (t : ℕ) : ℤ := (2 : ℤ) * (t : ℤ)

/-- `(2ks + t) + 2s` -/
def kA1 (s t k : ℕ) : ℤ := kA0 s t k + kE s

/-- `⌊(2ks+t)/(2t)⌋ = auK s t k` -/
def kQ0 (s t k : ℕ) : ℤ := Int.tdiv (kA0 s t k) (kD t)

/-- `⌊(2ks+2s+t)/(2t)⌋ = auK s t (k+1)` -/
def kQ1 (s t k : ℕ) : ℤ := Int.tdiv (kA1 s t k) (kD t)

/-! ## The values as natural numbers -/

theorem kE_eq (s : ℕ) : kE s = ((2 * s : ℕ) : ℤ) := by
  simp only [kE]; push_cast; ring

theorem kD_eq (t : ℕ) : kD t = ((2 * t : ℕ) : ℤ) := by
  simp only [kD]; push_cast; ring

theorem kP_eq (s k : ℕ) : kP s k = ((2 * k * s : ℕ) : ℤ) := by
  simp only [kP, kE]; push_cast; ring

theorem kA0_eq (s t k : ℕ) : kA0 s t k = ((2 * k * s + t : ℕ) : ℤ) := by
  simp only [kA0, kP, kE]; push_cast; ring

theorem kA1_eq (s t k : ℕ) : kA1 s t k = ((2 * (k + 1) * s + t : ℕ) : ℤ) := by
  simp only [kA1, kA0, kP, kE]; push_cast; ring

/-- The first output: `Int.tdiv (2ks+t) (2t)` is the natural quotient `⌊(2ks+t)/(2t)⌋ = auK s t k`. -/
theorem kQ0_eq (s t k : ℕ) (ht : 1 ≤ t) : kQ0 s t k = ((auK s t k : ℕ) : ℤ) := by
  rw [kQ0, kA0_eq, kD_eq, ← natCast_div_eq_tdiv (2 * k * s + t) (by omega : 1 ≤ 2 * t)]
  rfl

/-- The second output: `Int.tdiv (2ks+2s+t) (2t) = auK s t (k+1)`. -/
theorem kQ1_eq (s t k : ℕ) (ht : 1 ≤ t) : kQ1 s t k = ((auK s t (k + 1) : ℕ) : ℤ) := by
  rw [kQ1, kA1_eq, kD_eq, ← natCast_div_eq_tdiv (2 * (k + 1) * s + t) (by omega : 1 ≤ 2 * t)]
  rfl

/-! ## Size bounds -/

/-- `isz z ≤ SZ p` from `z.natAbs < 2^q`, `q + 2 ≤ SZ p`. -/
theorem isz_le_SZ_of_natAbs_lt {p q : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ q)
    (hq : q + 2 ≤ SZ p) : isz z ≤ SZ p :=
  le_trans (isz_le_of_natAbs_lt h) hq

/-- `4·2^{2p} = 2^{2p+2}`. -/
theorem four_mul_two_pow (p : ℕ) : (4 : ℕ) * 2 ^ (2 * p) = 2 ^ (2 * p + 2) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  ring

/-- `isz (n : ℤ) ≤ SZ p` for a value below `4·2^{2p}`. -/
theorem isz_natCast_le_four {p n : ℕ} (h : n < 4 * 2 ^ (2 * p)) : isz ((n : ℤ)) ≤ SZ p := by
  refine isz_le_SZ_of_natAbs_lt (q := 2 * p + 2) ?_ (by simp only [SZ]; omega)
  rw [Int.natAbs_natCast, ← four_mul_two_pow p]
  exact h

/-- Sums of bounded terms: `A < 2X`, `B ≤ X`, `C ≤ X` give `A+B+C < 4X`. -/
theorem add3_lt_four_mul {X A B C : ℕ} (hA : A < 2 * X) (hB : B ≤ X) (hC : C ≤ X) :
    A + B + C < 4 * X := by omega

/-- `A < 2X`, `B ≤ X` give `A+B < 4X`. -/
theorem add2_lt_four_mul {X A B : ℕ} (hA : A < 2 * X) (hB : B ≤ X) :
    A + B < 4 * X := by omega

/-- **All size bounds for the window-centre word** at once. -/
theorem auKSizes (p s t k : ℕ) (hp : 100 ≤ p) (ht : 1 ≤ t) (htp : t < 2 ^ p) (hst : s < t)
    (hkt : k < t) :
    isz ((k : ℤ)) ≤ SZ p ∧ isz ((s : ℤ)) ≤ SZ p ∧ isz ((t : ℤ)) ≤ SZ p ∧
    isz (kE s) ≤ SZ p ∧ isz (kP s k) ≤ SZ p ∧ isz (kA0 s t k) ≤ SZ p ∧
    isz (kD t) ≤ SZ p ∧ isz (kA1 s t k) ≤ SZ p ∧ isz (kQ0 s t k) ≤ SZ p ∧
    isz (kQ1 s t k) ≤ SZ p := by
  have hk2p : k < 2 ^ p := lt_trans hkt htp
  have hs2p : s < 2 ^ p := lt_trans hst htp
  set X : ℕ := 2 ^ (2 * p) with hX
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_two_pow
  have h2pX : 2 ^ p ≤ X := by
    rw [hX]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkX : k ≤ X := le_trans (le_of_lt hk2p) h2pX
  have hsX : s ≤ X := le_trans (le_of_lt hs2p) h2pX
  have htX : t ≤ X := le_trans (le_of_lt htp) h2pX
  have h2sX : 2 * s ≤ X := by
    have h1 : 2 * s < 2 * 2 ^ p := Nat.mul_lt_mul_of_pos_left hs2p (by norm_num)
    have h2 : 2 * 2 ^ p = 2 ^ (p + 1) := by rw [pow_succ]; ring
    have h3 : (2 : ℕ) ^ (p + 1) ≤ X := by
      rw [hX]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2tX : 2 * t ≤ X := by
    have h1 : 2 * t < 2 * 2 ^ p := Nat.mul_lt_mul_of_pos_left htp (by norm_num)
    have h2 : 2 * 2 ^ p = 2 ^ (p + 1) := by rw [pow_succ]; ring
    have h3 : (2 : ℕ) ^ (p + 1) ≤ X := by
      rw [hX]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hksX : k * s < X := by
    have h1 : k * s ≤ 2 ^ p * s := Nat.mul_le_mul_right s (le_of_lt hk2p)
    have h2 : 2 ^ p * s < 2 ^ p * 2 ^ p :=
      Nat.mul_lt_mul_of_pos_left hs2p (Nat.two_pow_pos p)
    have h3 : (2 : ℕ) ^ p * 2 ^ p = X := by rw [hX, ← pow_add]; congr 1; omega
    omega
  have h2ksX : 2 * (k * s) < 2 * X := Nat.mul_lt_mul_of_pos_left hksX (by norm_num)
  have h4X : (4 : ℕ) * X = 2 ^ (2 * p + 2) := by rw [hX]; exact four_mul_two_pow p
  have hfour : ∀ n : ℕ, n < 4 * X → isz ((n : ℤ)) ≤ SZ p := by
    intro n hn
    exact isz_natCast_le_four (by rw [← hX]; exact hn)
  have hq : ∀ A D : ℕ, A < 4 * X → isz (Int.tdiv (A : ℤ) (D : ℤ)) ≤ SZ p := by
    intro A D hA
    refine isz_le_SZ_of_natAbs_lt (q := 2 * p + 2) ?_ (by simp only [SZ]; omega)
    rw [Int.natAbs_tdiv, Int.natAbs_natCast]
    rw [hX, four_mul_two_pow] at hA
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hA
  have hP4 : 2 * k * s < 4 * X := by
    have h1 : 2 * k * s = 2 * (k * s) := by ring
    rw [h1]; omega
  have hA04 : 2 * k * s + t < 4 * X := by
    have h1 : 2 * k * s = 2 * (k * s) := by ring
    rw [h1]; exact add2_lt_four_mul h2ksX htX
  have hA14 : 2 * (k + 1) * s + t < 4 * X := by
    have h1 : 2 * (k + 1) * s + t = 2 * (k * s) + 2 * s + t := by ring
    rw [h1]; exact add3_lt_four_mul h2ksX h2sX htX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hfour k (by omega)
  · exact hfour s (by omega)
  · exact hfour t (by omega)
  · rw [kE_eq]; exact hfour (2 * s) (by omega)
  · rw [kP_eq]; exact hfour (2 * k * s) hP4
  · rw [kA0_eq]; exact hfour (2 * k * s + t) hA04
  · rw [kD_eq]; exact hfour (2 * t) (by omega)
  · rw [kA1_eq]; exact hfour (2 * (k + 1) * s + t) hA14
  · rw [kQ0, kA0_eq, kD_eq]; exact hq (2 * k * s + t) (2 * t) hA04
  · rw [kQ1, kA1_eq, kD_eq]; exact hq (2 * (k + 1) * s + t) (2 * t) hA14

/-! ## Cost lemmas -/

/-- A product of two bounded sizes costs at most `SB p KS`. -/
theorem le_SB_mul {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ SZ p) (hv : v ≤ SZ p) :
    K * u * v ≤ SB p KS := by
  rw [SB]
  have h2 : u * v ≤ SZ p * SZ p := Nat.mul_le_mul hu hv
  have h3 : SZ p * SZ p ≤ (SZ p + 8) ^ 2 := by
    nlinarith [Nat.zero_le (SZ p), sq_nonneg ((SZ p : ℤ))]
  calc K * u * v = K * (u * v) := by ring
    _ ≤ KS * (SZ p * SZ p) := Nat.mul_le_mul hK h2
    _ ≤ KS * (SZ p + 8) ^ 2 := Nat.mul_le_mul_left _ h3

/-- Four cost terms of the shape `Kᵢ (p+1)^{Kᵢ}` are absorbed by one `K (p+1)^K`. -/
theorem cost4 {K1 K2 K3 K4 p : ℕ} :
    K1 * (p + 1) ^ K1 + (K2 * (p + 1) ^ K2 + (K3 * (p + 1) ^ K3 + K4 * (p + 1) ^ K4)) ≤
      (16 * (K1 + K2 + K3 + K4) + 20) *
        (p + 1) ^ (16 * (K1 + K2 + K3 + K4) + 20) := by
  have hB : 1 ≤ p + 1 := Nat.succ_le_succ (Nat.zero_le p)
  set M : ℕ := 4 * (K1 + K2 + K3 + K4) + 5 with hM
  have hK1 : K1 ≤ M := by omega
  have hK2 : K2 ≤ M := by omega
  have hK3 : K3 ≤ M := by omega
  have hK4 : K4 ≤ M := by omega
  have e1 : K1 * (p + 1) ^ K1 ≤ M * (p + 1) ^ M :=
    Nat.mul_le_mul hK1 (Nat.pow_le_pow_right hB (by omega))
  have e2 : K2 * (p + 1) ^ K2 ≤ M * (p + 1) ^ M :=
    Nat.mul_le_mul hK2 (Nat.pow_le_pow_right hB (by omega))
  have e3 : K3 * (p + 1) ^ K3 ≤ M * (p + 1) ^ M :=
    Nat.mul_le_mul hK3 (Nat.pow_le_pow_right hB (by omega))
  have e4 : K4 * (p + 1) ^ K4 ≤ M * (p + 1) ^ M :=
    Nat.mul_le_mul hK4 (Nat.pow_le_pow_right hB (by omega))
  have hsum := add_le_add e1 (add_le_add e2 (add_le_add e3 e4))
  have h4 : 4 * (M * (p + 1) ^ M) =
      M * (p + 1) ^ M + (M * (p + 1) ^ M + (M * (p + 1) ^ M + M * (p + 1) ^ M)) := by ring
  have h5 : 4 * (M * (p + 1) ^ M) ≤ (4 * M) * (p + 1) ^ (4 * M) := by
    rw [show (4 : ℕ) * (M * (p + 1) ^ M) = (4 * M) * (p + 1) ^ M by ring]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (by omega))
  have h6 : 16 * (K1 + K2 + K3 + K4) + 20 = 4 * M := by omega
  rw [h6]
  exact le_trans (le_trans hsum (le_of_eq h4.symm)) h5

end Work.Resample
