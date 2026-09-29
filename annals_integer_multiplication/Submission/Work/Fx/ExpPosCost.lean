import Mathlib

set_option autoImplicit false

namespace Work.Fx

/-!
# Cost bookkeeping for the positive exponential field

Every step of the word is charged the uniform bound `CRT = KSm * (10^12 * N^KE)` where
`N` bounds the sizes (`2000 * N` for every intermediate value, `3000 * N` for a window).
-/

theorem ep40 {N : ℕ} (hN : 30000 ≤ N) : 8000 * N ≤ N ^ 2 := by
  calc 8000 * N ≤ N * N := Nat.mul_le_mul (by omega) (le_refl N)
    _ = N ^ 2 := (pow_two N).symm

theorem ep400 {N : ℕ} (hN : 30000 ≤ N) : 16000000 * N ^ 2 ≤ N ^ 4 := by
  have h2000 : 4000 ≤ N := by omega
  have h4M : 16000000 ≤ N ^ 2 := by
    calc 16000000 = 4000 * 4000 := by norm_num
      _ ≤ N * N := Nat.mul_le_mul h2000 h2000
      _ = N ^ 2 := (pow_two N).symm
  calc 16000000 * N ^ 2 ≤ N ^ 2 * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) h4M
    _ = N ^ 4 := by ring

theorem ep32 {N : ℕ} (hN : 30000 ≤ N) : 32 * N ^ 2 ≤ N ^ 4 := by
  have h32 : 32 ≤ N ^ 2 := by
    calc 32 = 4 * 8 := by norm_num
      _ ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      _ = N ^ 2 := (pow_two N).symm
  calc 32 * N ^ 2 ≤ N ^ 2 * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) h32
    _ = N ^ 4 := by ring

theorem epCostMul {N KSm KE CRT a b Kc : ℕ} (hN : 30000 ≤ N) (hKE : 4 ≤ KE)
    (hCRT : CRT = KSm * (1000000000000 * N ^ KE)) (hK : Kc ≤ KSm)
    (ha : a ≤ 4000 * N) (hb : b ≤ 4000 * N) : Kc * a * b ≤ CRT := by
  rw [hCRT]
  have h1 : 16000000 * N ^ 2 ≤ N ^ KE :=
    le_trans (ep400 hN) (Nat.pow_le_pow_right (by omega) hKE)
  calc Kc * a * b ≤ KSm * (4000 * N) * (4000 * N) := Nat.mul_le_mul (Nat.mul_le_mul hK ha) hb
    _ = KSm * (16000000 * N ^ 2) := by ring
    _ ≤ KSm * N ^ KE := Nat.mul_le_mul_left KSm h1
    _ ≤ KSm * (1000000000000 * N ^ KE) := Nat.mul_le_mul_left KSm (Nat.le_mul_of_pos_left _ (by norm_num))

theorem epCostLin {N KSm KE CRT a b Kc : ℕ} (hN : 30000 ≤ N) (hKE : 4 ≤ KE)
    (hCRT : CRT = KSm * (1000000000000 * N ^ KE)) (hK : Kc ≤ KSm)
    (ha : a ≤ 4000 * N) (hb : b ≤ 4000 * N) : Kc * (a + b) ≤ CRT := by
  rw [hCRT]
  have h1 : 8000 * N ≤ N ^ KE :=
    le_trans (ep40 hN) (Nat.pow_le_pow_right (by omega) (by omega))
  calc Kc * (a + b) ≤ KSm * (8000 * N) := Nat.mul_le_mul hK (by omega)
    _ ≤ KSm * N ^ KE := Nat.mul_le_mul_left KSm h1
    _ ≤ KSm * (1000000000000 * N ^ KE) := Nat.mul_le_mul_left KSm (Nat.le_mul_of_pos_left _ (by norm_num))

theorem epCostPick {N KSm KE CRT a b Kc : ℕ} (hN : 30000 ≤ N) (hKE : 4 ≤ KE)
    (hCRT : CRT = KSm * (1000000000000 * N ^ KE)) (hK : Kc ≤ KSm) (ha : a + 1 ≤ 16)
    (hb : b ≤ N * N) : Kc * a * (b + 1) ≤ CRT := by
  rw [hCRT]
  have h1 : 32 * N ^ 2 ≤ N ^ KE :=
    le_trans (ep32 hN) (Nat.pow_le_pow_right (by omega) hKE)
  have hb' : b + 1 ≤ 2 * N ^ 2 := by
    have h : 1 ≤ N ^ 2 := by nlinarith
    nlinarith
  calc Kc * a * (b + 1) ≤ KSm * 16 * (2 * N ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) hb'
    _ = KSm * (32 * N ^ 2) := by ring
    _ ≤ KSm * N ^ KE := Nat.mul_le_mul_left KSm h1
    _ ≤ KSm * (1000000000000 * N ^ KE) := Nat.mul_le_mul_left KSm (Nat.le_mul_of_pos_left _ (by norm_num))

theorem epCostSmall {N KSm KE CRT a Kc : ℕ} (hN : 30000 ≤ N) (hKE : 4 ≤ KE)
    (hCRT : CRT = KSm * (1000000000000 * N ^ KE)) (hK : Kc ≤ KSm) (ha : a ≤ 4000 * N) :
    Kc * a ≤ CRT := by
  rw [hCRT]
  have h1 : 4000 * N ≤ N ^ KE :=
    le_trans (le_trans (Nat.mul_le_mul_right N (by omega : 4000 ≤ 8000)) (ep40 hN))
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc Kc * a ≤ KSm * (4000 * N) := Nat.mul_le_mul hK ha
    _ ≤ KSm * N ^ KE := Nat.mul_le_mul_left KSm h1
    _ ≤ KSm * (1000000000000 * N ^ KE) := Nat.mul_le_mul_left KSm (Nat.le_mul_of_pos_left _ (by norm_num))

theorem epCostPow {N KSm KE CRT Kc Q : ℕ} (hN : 30000 ≤ N) (hKE : 4 ≤ KE)
    (hCRT : CRT = KSm * (1000000000000 * N ^ KE)) (hK : Kc ≤ KE) (hKS : KE ≤ KSm) (hQ : Q + 1 ≤ N) :
    Kc * (Q + 1) ^ Kc ≤ CRT := by
  rw [hCRT]
  have h1 : (Q + 1) ^ Kc ≤ N ^ KE :=
    le_trans (Nat.pow_le_pow_left hQ Kc) (Nat.pow_le_pow_right (by omega) hK)
  calc Kc * (Q + 1) ^ Kc ≤ KSm * N ^ KE := Nat.mul_le_mul (le_trans hK hKS) h1
    _ ≤ KSm * (1000000000000 * N ^ KE) := Nat.mul_le_mul_left KSm (Nat.le_mul_of_pos_left _ (by norm_num))

/-- The final cost comparison, with `T` the number of steps. -/
theorem epCostTotal {B N KSm KE K T : ℕ} (hB : 1 ≤ B) (hN : N ≤ 1002 * B) (hKE : 2 ≤ KE)
    (hK : K = T * KSm * 1000000000000 * 1002 ^ KE + KE + 1) :
    T * (KSm * (1000000000000 * N ^ KE)) ≤ K * B ^ K := by
  have h1 : N ^ KE ≤ (1002 * B) ^ KE := Nat.pow_le_pow_left hN KE
  have h2 : (1002 * B) ^ KE = 1002 ^ KE * B ^ KE := Nat.mul_pow 1002 B KE
  have h3 : B ^ KE ≤ B ^ K := Nat.pow_le_pow_right hB (by omega)
  have h4 : T * KSm * 1000000000000 * 1002 ^ KE ≤ K := by rw [hK]; omega
  calc T * (KSm * (1000000000000 * N ^ KE))
      = T * KSm * 1000000000000 * N ^ KE := by ring
    _ ≤ T * KSm * 1000000000000 * (1002 ^ KE * B ^ KE) := by
        apply Nat.mul_le_mul_left
        rw [← h2]
        exact h1
    _ = (T * KSm * 1000000000000 * 1002 ^ KE) * B ^ KE := by ring
    _ ≤ K * B ^ KE := Nat.mul_le_mul_right _ h4
    _ ≤ K * B ^ K := Nat.mul_le_mul_left K h3

end Work.Fx
