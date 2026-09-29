import Mathlib
import Submission.Work.Resample.buZDefs

/-!
# Size estimates and semantics of the `buZ` word intermediates

The intermediate values of the `buZ` word (`Work.Resample.buZW`) all fit the uniform size bound
`buSZ p`, and the composite value `buZZ` computed by the word is the paper's exponent
`buZ p α s t ℓ h`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-- The denominator `2s` of the `β` quotients is positive. -/
theorem buZE_pos {s : ℕ} (hs : 0 < s) : 0 < buZE s := by
  unfold buZE
  have h3 : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
  linarith

/-- The final divisor `s²` is nonzero. -/
theorem buZS2_ne_zero {s : ℕ} (hs : 0 < s) : buZS2 s ≠ 0 := by
  unfold buZS2
  have h3 : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
  intro h
  nlinarith [h, h3]

/-- All intermediate values of the `buZ` word fit the uniform size bound. -/
theorem buZSizes (p α s t : ℕ) (ℓ h : ℤ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ))
    (hh : h.natAbs ≤ egM p α) :
    isz (buZU1 t ℓ) ≤ buSZ p ∧ isz (buZV t h) ≤ buSZ p ∧ isz (buZU2 t ℓ h) ≤ buSZ p ∧
    isz (buZD1 t ℓ) ≤ buSZ p ∧ isz (buZE s) ≤ buSZ p ∧ isz (buZA1 t ℓ s) ≤ buSZ p ∧
    isz (buZQ1 t ℓ s) ≤ buSZ p ∧ isz (buZR1 t ℓ s) ≤ buSZ p ∧ isz (buZB1 t ℓ s) ≤ buSZ p ∧
    isz (buZD2 t ℓ h) ≤ buSZ p ∧ isz (buZA2 t ℓ h s) ≤ buSZ p ∧ isz (buZQ2 t ℓ h s) ≤ buSZ p ∧
    isz (buZR2 t ℓ h s) ≤ buSZ p ∧ isz (buZB2 t ℓ h s) ≤ buSZ p ∧ isz (buZA t ℓ h s) ≤ buSZ p ∧
    isz (buZSq t ℓ h s) ≤ buSZ p ∧ isz (buZB2sq t ℓ h s) ≤ buSZ p ∧ isz (buZN t ℓ h s) ≤ buSZ p ∧
    isz (buZA2c α) ≤ buSZ p ∧ isz (buZA2N t ℓ h s α) ≤ buSZ p ∧ isz (buZP p t ℓ h s α) ≤ buSZ p ∧
    isz (buZS2 s) ≤ buSZ p := by
  have hsp : s < 2 ^ p := lt_trans hst htp
  have hαp' : α < p := by nlinarith
  have ht2 : (t : ℤ).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact le_of_lt htp
  have hs2 : (s : ℤ).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact le_of_lt hsp
  have hα2 : (α : ℤ).natAbs ≤ 2 ^ p := by
    rw [Int.natAbs_natCast]
    exact le_of_lt (lt_of_lt_of_le hαp' (le_of_lt (Nat.lt_two_pow_self (n := p))))
  have hℓ2 : ℓ.natAbs ≤ 2 ^ p := by
    have h1 := natAbs_le_of ℓ (s : ℤ) (by positivity) (by omega) (le_of_lt hℓs)
    rw [Int.natAbs_natCast] at h1
    exact le_trans h1 (le_of_lt hsp)
  have hh2 : h.natAbs ≤ 2 ^ p := by
    refine le_trans hh (le_trans (egM_le p α) ?_)
    have := Nat.lt_two_pow_self (n := p); omega
  have nU1 : (buZU1 t ℓ).natAbs ≤ 2 ^ (2 * p) := by
    unfold buZU1
    exact le_trans (buZ_na_mul ht2 hℓ2) (buZ_pow_mono (by omega))
  have nV : (buZV t h).natAbs ≤ 2 ^ (2 * p) := by
    unfold buZV
    exact le_trans (buZ_na_mul ht2 hh2) (buZ_pow_mono (by omega))
  have nU2 : (buZU2 t ℓ h).natAbs ≤ 2 ^ (2 * p + 1) := by
    unfold buZU2
    exact le_trans (buZ_na_add nU1 nV) (buZ_pow_mono (by omega))
  have nD1 : (buZD1 t ℓ).natAbs ≤ 2 ^ (2 * p + 1) := by
    unfold buZD1
    exact le_trans (buZ_na_add nU1 nU1) (buZ_pow_mono (by omega))
  have hEpos : 0 < buZE s := buZE_pos (by omega)
  have nE : (buZE s).natAbs ≤ 2 ^ (p + 1) := by
    unfold buZE
    exact le_trans (buZ_na_add hs2 hs2) (buZ_pow_mono (by omega))
  have nA1 : (buZA1 t ℓ s).natAbs ≤ 2 ^ (2 * p + 2) := by
    unfold buZA1
    exact le_trans (buZ_na_add nD1 hs2) (buZ_pow_mono (by omega))
  have nQ1 : (buZQ1 t ℓ s).natAbs ≤ 2 ^ (2 * p + 3) := by
    unfold buZQ1
    exact buZ_na_fdiv nA1 hEpos
  have nR1 : (buZR1 t ℓ s).natAbs ≤ 2 ^ (3 * p + 3) := by
    unfold buZR1
    exact le_trans (buZ_na_mul hs2 nQ1) (buZ_pow_mono (by omega))
  have nB1 : (buZB1 t ℓ s).natAbs ≤ 2 ^ (3 * p + 4) := by
    unfold buZB1
    exact le_trans (buZ_na_sub nU1 nR1) (buZ_pow_mono (by omega))
  have nD2 : (buZD2 t ℓ h).natAbs ≤ 2 ^ (2 * p + 2) := by
    unfold buZD2
    exact le_trans (buZ_na_add nU2 nU2) (buZ_pow_mono (by omega))
  have nA2 : (buZA2 t ℓ h s).natAbs ≤ 2 ^ (2 * p + 3) := by
    unfold buZA2
    exact le_trans (buZ_na_add nD2 hs2) (buZ_pow_mono (by omega))
  have nQ2 : (buZQ2 t ℓ h s).natAbs ≤ 2 ^ (2 * p + 4) := by
    unfold buZQ2
    exact buZ_na_fdiv nA2 hEpos
  have nR2 : (buZR2 t ℓ h s).natAbs ≤ 2 ^ (3 * p + 4) := by
    unfold buZR2
    exact le_trans (buZ_na_mul hs2 nQ2) (buZ_pow_mono (by omega))
  have nB2 : (buZB2 t ℓ h s).natAbs ≤ 2 ^ (3 * p + 5) := by
    unfold buZB2
    exact le_trans (buZ_na_sub nU2 nR2) (buZ_pow_mono (by omega))
  have nAa : (buZA t ℓ h s).natAbs ≤ 2 ^ (3 * p + 5) := by
    unfold buZA
    exact le_trans (buZ_na_add nB1 nV) (buZ_pow_mono (by omega))
  have nSq : (buZSq t ℓ h s).natAbs ≤ 2 ^ (6 * p + 10) := by
    unfold buZSq
    exact le_trans (buZ_na_mul nAa nAa) (buZ_pow_mono (by omega))
  have nB2sq : (buZB2sq t ℓ h s).natAbs ≤ 2 ^ (6 * p + 10) := by
    unfold buZB2sq
    exact le_trans (buZ_na_mul nB2 nB2) (buZ_pow_mono (by omega))
  have nN : (buZN t ℓ h s).natAbs ≤ 2 ^ (6 * p + 11) := by
    unfold buZN
    exact le_trans (buZ_na_sub nSq nB2sq) (buZ_pow_mono (by omega))
  have nA2c : (buZA2c α).natAbs ≤ 2 ^ p := by
    unfold buZA2c
    have h1 : ((α : ℤ) * (α : ℤ)).natAbs = α * α := by rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [h1]
    have h2 : α * α < 2 ^ p := by
      have h3 := hαp
      rw [pow_two] at h3
      exact lt_of_lt_of_le h3 (le_of_lt (Nat.lt_two_pow_self (n := p)))
    exact le_of_lt h2
  have nA2N : (buZA2N t ℓ h s α).natAbs ≤ 2 ^ (7 * p + 11) := by
    unfold buZA2N
    exact le_trans (buZ_na_mul nN nA2c) (buZ_pow_mono (by omega))
  have nPi : (auPi p).natAbs ≤ 2 ^ (6 * p + 205) := natAbs_auPi_le p
  have nP : (buZP p t ℓ h s α).natAbs ≤ 2 ^ (13 * p + 216) := by
    unfold buZP
    exact le_trans (buZ_na_mul nPi nA2N) (buZ_pow_mono (by omega))
  have nS2 : (buZS2 s).natAbs ≤ 2 ^ (2 * p) := by
    unfold buZS2
    exact le_trans (buZ_na_mul hs2 hs2) (buZ_pow_mono (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact buZ_isz_le (A := 2 * p) (by simp only [buZBnd]; omega) nU1
  · exact buZ_isz_le (A := 2 * p) (by simp only [buZBnd]; omega) nV
  · exact buZ_isz_le (A := 2 * p + 1) (by simp only [buZBnd]; omega) nU2
  · exact buZ_isz_le (A := 2 * p + 1) (by simp only [buZBnd]; omega) nD1
  · exact buZ_isz_le (A := p + 1) (by simp only [buZBnd]; omega) nE
  · exact buZ_isz_le (A := 2 * p + 2) (by simp only [buZBnd]; omega) nA1
  · exact buZ_isz_le (A := 2 * p + 3) (by simp only [buZBnd]; omega) nQ1
  · exact buZ_isz_le (A := 3 * p + 3) (by simp only [buZBnd]; omega) nR1
  · exact buZ_isz_le (A := 3 * p + 4) (by simp only [buZBnd]; omega) nB1
  · exact buZ_isz_le (A := 2 * p + 2) (by simp only [buZBnd]; omega) nD2
  · exact buZ_isz_le (A := 2 * p + 3) (by simp only [buZBnd]; omega) nA2
  · exact buZ_isz_le (A := 2 * p + 4) (by simp only [buZBnd]; omega) nQ2
  · exact buZ_isz_le (A := 3 * p + 4) (by simp only [buZBnd]; omega) nR2
  · exact buZ_isz_le (A := 3 * p + 5) (by simp only [buZBnd]; omega) nB2
  · exact buZ_isz_le (A := 3 * p + 5) (by simp only [buZBnd]; omega) nAa
  · exact buZ_isz_le (A := 6 * p + 10) (by simp only [buZBnd]; omega) nSq
  · exact buZ_isz_le (A := 6 * p + 10) (by simp only [buZBnd]; omega) nB2sq
  · exact buZ_isz_le (A := 6 * p + 11) (by simp only [buZBnd]; omega) nN
  · exact buZ_isz_le (A := p) (by simp only [buZBnd]; omega) nA2c
  · exact buZ_isz_le (A := 7 * p + 11) (by simp only [buZBnd]; omega) nA2N
  · exact buZ_isz_le (A := 13 * p + 216) (by simp only [buZBnd]; omega) nP
  · exact buZ_isz_le (A := 2 * p) (by simp only [buZBnd]; omega) nS2

/-- The value computed by the `buZ` word is the paper's working-scale exponent. -/
theorem buZZ_eq_buZ (p α s t : ℕ) (ℓ h : ℤ) (hs : 0 < s) :
    buZZ p α s t ℓ h = buZ p α s t ℓ h := by
  have hb1 : buZB1 t ℓ s = buBeta s t ℓ := by
    rw [buBeta_eq s t hs ℓ]
    unfold buZB1 buZR1 buZQ1 buZA1 buZD1 buZU1 buZE
    have hX : (t : ℤ) * ℓ + (t : ℤ) * ℓ + (s : ℤ) = 2 * ((t : ℤ) * ℓ) + (s : ℤ) := by ring
    have hY : (s : ℤ) + (s : ℤ) = 2 * (s : ℤ) := by ring
    rw [hX, hY]
    ring
  have hb2 : buZB2 t ℓ h s = buBeta s t (ℓ + h) := by
    rw [buBeta_eq s t hs (ℓ + h)]
    unfold buZB2 buZR2 buZQ2 buZA2 buZD2 buZU2 buZU1 buZV buZE
    have hX : ((t : ℤ) * ℓ + (t : ℤ) * h) + ((t : ℤ) * ℓ + (t : ℤ) * h) + (s : ℤ)
        = 2 * ((t : ℤ) * (ℓ + h)) + (s : ℤ) := by ring
    have hY : (s : ℤ) + (s : ℤ) = 2 * (s : ℤ) := by ring
    rw [hX, hY]
    ring
  have hA : buZA t ℓ h s = (t : ℤ) * h + buBeta s t ℓ := by
    unfold buZA buZV
    rw [hb1]
    ring
  have hSq : buZSq t ℓ h s = ((t : ℤ) * h + buBeta s t ℓ) ^ 2 := by
    unfold buZSq
    rw [hA]
    ring
  have hB2sq : buZB2sq t ℓ h s = (buBeta s t (ℓ + h)) ^ 2 := by
    unfold buZB2sq
    rw [hb2]
    ring
  have hN : buZN t ℓ h s = buN s t ℓ h := by
    unfold buZN buN
    rw [hSq, hB2sq]
  have hP : buZP p t ℓ h s α = auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h) := by
    unfold buZP buZA2N buZA2c
    rw [hN]
    ring
  have hS2 : buZS2 s = (s : ℤ) ^ 2 := by unfold buZS2; ring
  rw [buZZ, buZ, hP, hS2]

end Work.Resample
