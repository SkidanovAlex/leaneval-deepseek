import Mathlib
import Submission.Work.KronP.kdefs
import Submission.Work.Fx.norm_tdiv_sub_div_lt
import Submission.Work.Fx.norm_fxC_sub
import Submission.Work.Fx.mulSFieldMath

/-!
# Truncation of a fixed-point complex number (paper §2.2, input to Lemma 2.5)

Given `p, r` with `r = 2 ^ (Nat.clog 2 r)`, a complex number `Z` with `4^p Z = D0 + i D1`
(`D0, D1 : ℤ`) and `‖Z‖ ≤ r`, the componentwise truncating division of `(D0, D1)` by
`2^(p + clog 2 r) = 2^p·r` yields a point of the fixed-point disc `C̃◦` that approximates
`Z/r` with error `< 2` in the fixed-point metric `2^p ‖·‖`.

The error estimate is `√2 < 2`: truncating towards zero moves each coordinate by `< 1`
(`Work.Fx.norm_tdiv_sub_div_lt`), rescaled by `2^p` this is exactly the displacement of the
fixed-point point `fxC`; and cropping the modulus from `≥ 4^p r` back to `2^p s` (`s = 2^(p+k)`)
keeps the point inside the disc because truncation never increases the square
(`Work.Fx.tdivSqMulLe`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KronP

open HvdH

/-- Squared modulus of a point of the plane given by two integers. -/
private theorem sq_norm_cplx_int (a b : ℤ) :
    ‖(((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I)‖ ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

theorem truncApprox {p r : ℕ} (hrpow : r = 2 ^ (Nat.clog 2 r))
    {Z : ℂ} {D0 D1 : ℤ} (hex : (4 : ℂ) ^ p * Z = (D0 : ℂ) + (D1 : ℂ) * Complex.I)
    (hZ : ‖Z‖ ≤ (r : ℝ)) :
    HvdH.inDisc p (Int.tdiv D0 ((2 : ℤ) ^ (p + Nat.clog 2 r)),
        Int.tdiv D1 ((2 : ℤ) ^ (p + Nat.clog 2 r))) ∧
      (2 : ℝ) ^ p * ‖HvdH.fxC p (Int.tdiv D0 ((2 : ℤ) ^ (p + Nat.clog 2 r)),
          Int.tdiv D1 ((2 : ℤ) ^ (p + Nat.clog 2 r))) - ((r : ℂ))⁻¹ * Z‖ < 2 := by
  set k : ℕ := Nat.clog 2 r
  have hrk : r = 2 ^ k := hrpow
  have hr1 : 1 ≤ r := by rw [hrpow]; exact Nat.one_le_two_pow
  have hrpos : 0 < r := hr1
  set s : ℕ := 2 ^ (p + k) with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
  have hsZ : (s : ℤ) = (2 : ℤ) ^ (p + k) := by rw [hsdef]; push_cast; ring
  have hrR : (r : ℝ) = (2 : ℝ) ^ k := by rw [hrk]; push_cast; ring
  have hrC : (r : ℂ) = (2 : ℂ) ^ k := by rw [hrk]; push_cast; ring
  have hkey : (s : ℝ) = (2 : ℝ) ^ p * (r : ℝ) := by
    rw [hsdef]; push_cast; rw [pow_add, ← hrR]
  have hkeyC : (s : ℂ) = (2 : ℂ) ^ p * (r : ℂ) := by
    rw [hsdef]; push_cast; rw [pow_add, ← hrC]
  have h2p : (2 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4p : (4 : ℂ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hrc : (r : ℂ) ≠ 0 := by rw [hrC]; exact pow_ne_zero _ (by norm_num)
  have hsC : (s : ℂ) ≠ 0 := by rw [hkeyC]; exact mul_ne_zero h2p hrc
  have h4rC : (4 : ℂ) ^ p * (r : ℂ) = (2 : ℂ) ^ p * (s : ℂ) := by
    have h4c : (4 : ℂ) ^ p = (2 : ℂ) ^ p * (2 : ℂ) ^ p := by
      rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_pow]
    rw [h4c, hkeyC]; ring
  have hex' : (4 : ℂ) ^ p * Z = ((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I := by
    rw [hex]; push_cast; ring
  rw [← hsZ]
  set w0 : ℤ := Int.tdiv D0 (s : ℤ) with hw0
  set w1 : ℤ := Int.tdiv D1 (s : ℤ) with hw1
  refine ⟨?_, ?_⟩
  · -- truncation stays inside the disc
    show w0 ^ 2 + w1 ^ 2 ≤ 4 ^ p
    have hU := Work.Fx.tdivSqMulLe D0 (s : ℤ)
    have hV := Work.Fx.tdivSqMulLe D1 (s : ℤ)
    have hU2 : (w0 : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D0 : ℝ) ^ 2 := by
      rw [hw0]; exact_mod_cast hU
    have hV2 : (w1 : ℝ) ^ 2 * (s : ℝ) ^ 2 ≤ (D1 : ℝ) ^ 2 := by
      rw [hw1]; exact_mod_cast hV
    have hW : ‖((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I‖ ≤ (4 : ℝ) ^ p * (r : ℝ) := by
      have h1 : ‖((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I‖ = ‖(4 : ℂ) ^ p * Z‖ := by
        rw [hex']
      rw [h1, norm_mul, norm_pow, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hZ (by positivity)
    have heq : ((4 : ℝ) ^ p * (r : ℝ)) ^ 2 = (4 : ℝ) ^ p * (s : ℝ) ^ 2 := by
      have h4c : (4 : ℝ) ^ p = (2 : ℝ) ^ p * (2 : ℝ) ^ p := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      rw [h4c, hkey]; ring
    have hDsum : (D0 : ℝ) ^ 2 + (D1 : ℝ) ^ 2 ≤ (4 : ℝ) ^ p * (s : ℝ) ^ 2 := by
      have h1 : (D0 : ℝ) ^ 2 + (D1 : ℝ) ^ 2 ≤ ((4 : ℝ) ^ p * (r : ℝ)) ^ 2 := by
        rw [← sq_norm_cplx_int D0 D1]
        exact pow_le_pow_left₀ (norm_nonneg _) hW 2
      rwa [heq] at h1
    have hsum : (s : ℝ) ^ 2 * ((w0 : ℝ) ^ 2 + (w1 : ℝ) ^ 2) ≤ (s : ℝ) ^ 2 * (4 : ℝ) ^ p := by
      nlinarith [hU2, hV2, hDsum]
    exact_mod_cast (le_of_mul_le_mul_left hsum (pow_pos hsR 2))
  · -- truncation error
    have hZinv : Z = ((4 : ℂ) ^ p)⁻¹ * (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I) := by
      rw [← hex', inv_mul_cancel_left₀ h4p Z]
    have hinv : (r : ℂ)⁻¹ * ((4 : ℂ) ^ p)⁻¹ = ((2 : ℂ) ^ p)⁻¹ * ((s : ℂ)⁻¹) := by
      have h := congrArg (fun z : ℂ => z⁻¹) h4rC
      rw [mul_inv_rev, mul_inv_rev] at h
      rw [h]; ring
    have hcoef : (2 : ℂ) ^ p * (r : ℂ)⁻¹ * ((4 : ℂ) ^ p)⁻¹ = (s : ℂ)⁻¹ := by
      rw [show (2 : ℂ) ^ p * (r : ℂ)⁻¹ * ((4 : ℂ) ^ p)⁻¹
            = (2 : ℂ) ^ p * ((r : ℂ)⁻¹ * ((4 : ℂ) ^ p)⁻¹) by ring, hinv,
          ← mul_assoc, mul_inv_cancel₀ h2p, one_mul]
    have hZ2 : (2 : ℂ) ^ p * ((r : ℂ)⁻¹ * Z)
        = (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I) / (s : ℂ) := by
      rw [hZinv, div_eq_mul_inv]
      rw [show (2 : ℂ) ^ p * ((r : ℂ)⁻¹ * (((4 : ℂ) ^ p)⁻¹
              * (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I)))
            = (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I)
              * ((2 : ℂ) ^ p * (r : ℂ)⁻¹ * ((4 : ℂ) ^ p)⁻¹) by ring, hcoef]
    have hsplit : (2 : ℂ) ^ p * (((w0 : ℂ) + (w1 : ℂ) * Complex.I) / (2 : ℂ) ^ p)
        = (w0 : ℂ) + (w1 : ℂ) * Complex.I := by field_simp
    have hmul : (2 : ℂ) ^ p * (HvdH.fxC p (w0, w1) - (r : ℂ)⁻¹ * Z)
        = (w0 : ℂ) + (w1 : ℂ) * Complex.I
          - (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I) / (s : ℂ) := by
      rw [HvdH.fxC, mul_sub, hsplit, hZ2]
    have hnorm : (2 : ℝ) ^ p * ‖HvdH.fxC p (w0, w1) - (r : ℂ)⁻¹ * Z‖
        = ‖(w0 : ℂ) + (w1 : ℂ) * Complex.I
          - (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I) / (s : ℂ)‖ := by
      rw [← hmul, norm_mul,
        show ‖((2 : ℂ) ^ p)‖ = (2 : ℝ) ^ p from by rw [Complex.norm_pow]; norm_num]
    have hsqrt : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have h := Work.Fx.norm_tdiv_sub_div_lt (A := D0) (B := D1) (b := s) hspos
    rw [← hw0, ← hw1] at h
    rw [hnorm]
    have h2 : ‖(w0 : ℂ) + (w1 : ℂ) * Complex.I
        - (((D0 : ℝ) : ℂ) + ((D1 : ℝ) : ℂ) * Complex.I) / (s : ℂ)‖ < Real.sqrt 2 := by
      convert h using 2 <;> push_cast <;> ring
    linarith [h2, hsqrt]

end Work.KronP
