import Mathlib
import Submission.Work.Fx.norm_tdiv_sub_div_lt
import Submission.Work.Fx.mulSFieldMath

/-!
# `CisTrunc`: truncation of a fixed-point point, and its rescaled error

Auxiliary lemma of the `Fx` area (an input to `FxLib.cis`, paper Lemma 2.12).
Given `p ≥ 100`, integers `U, V` and complex numbers `A, E` with

* `‖A‖ ≤ 1 - 32·2^{-(p+60)}`   (the point `A` is strictly inside the unit disc),
* `‖(U + iV)/2^{p+60} - A‖ ≤ 4·2^{-(p+60)}`,
* `‖A - E‖ ≤ 67·2^{-(p+60)}`,

the truncated Gaussian integer `(u, v) = (U tdiv 2^60, V tdiv 2^60)`

* still lies in the disc `u² + v² ≤ 4^p` (`= 2^{2p}`), because truncation towards zero only
  decreases the modulus: `|u|·2^60 ≤ |U|`, `|v|·2^60 ≤ |V|`, while
  `U² + V² ≤ (2^{p+60} - 28)²`;
* and satisfies `‖(u + iv)/2^p - E‖ < 2/2^p`, since
  `2^p‖(u+iv)/2^p - E‖ ≤ ‖(u+iv) - 2^p z‖ + 4/2^60 + 67/2^60 < √2 + 71/2^60 < 2`
  where `z = (U + iV)/2^{p+60}`.

The three helper lemmas below are the independent arithmetic pieces.
-/

set_option autoImplicit false

namespace Work.Fx

/-- Truncating by `2^60` moves the point `2^p·z`, `z = (U+iV)/2^{p+60}`, to the Gaussian integer
`u + iv`, `u = U.tdiv 2^60`, `v = V.tdiv 2^60`: the displacement is `< √2`. -/
theorem TdivScaleNormDiff (p : ℕ) (U V : ℤ) :
    ‖(((Int.tdiv U (2 ^ 60) : ℤ) : ℂ) + ((Int.tdiv V (2 ^ 60) : ℤ) : ℂ) * Complex.I)
      - (2 : ℂ) ^ p * (((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖
      < Real.sqrt 2 := by
  have h := norm_tdiv_sub_div_lt (A := U) (B := V) (b := 2^60)
    (by norm_num : (0:ℕ) < 2^60)
  have hpt : ((U:ℂ) + (V:ℂ)*Complex.I) = (((U:ℝ):ℂ) + ((V:ℝ):ℂ)*Complex.I) := by
    push_cast; ring
  have ht : (2:ℤ)^60 = (((2^60:ℕ)):ℤ) := (Int.natCast_pow 2 60).symm
  have hpow : (2:ℂ)^60 = (((2^60:ℕ)):ℂ) := by rw [Nat.cast_pow]; norm_num
  have key : (2:ℂ)^p * (((U:ℂ)+(V:ℂ)*Complex.I) / (2:ℂ)^(p+60))
      = ((U:ℂ)+(V:ℂ)*Complex.I)/((2:ℂ)^60) := by
    rw [pow_add]; field_simp
  rw [key, hpow, hpt, ht]
  exact h

/-- **Radius bound.** If the fixed-point point `z = (U+iV)/2^{p+60}` has modulus `≤ 1 - 28/2^{p+60}`,
then `U² + V² ≤ (2^{p+60} - 28)²`: multiply `‖z‖ ≤ 1 - 28/2^{p+60}` by `2^{p+60}` and square. -/
theorem ZcNormSqBound (p : ℕ) (U V : ℤ)
    (h : ‖(((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60))‖ ≤ 1 - 28 / (2 : ℝ) ^ (p + 60)) :
    (U : ℝ) ^ 2 + (V : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (p + 60) - 28) ^ 2 := by
  have hc : (0:ℝ) < (2:ℝ)^(p+60) := by positivity
  have hnd : ‖(((U:ℂ)+(V:ℂ)*Complex.I) / (2:ℂ)^(p+60))‖
      = ‖((U:ℂ)+(V:ℂ)*Complex.I)‖ / (2:ℝ)^(p+60) := by
    rw [norm_div, Complex.norm_pow]; norm_num
  rw [hnd] at h
  have h1 : ‖((U:ℂ)+(V:ℂ)*Complex.I)‖ ≤ (2:ℝ)^(p+60) - 28 := by
    have h2 := (div_le_iff₀ hc).mp h
    rwa [show (1 - 28/(2:ℝ)^(p+60)) * (2:ℝ)^(p+60) = (2:ℝ)^(p+60) - 28 from by
      field_simp] at h2
  have hv : ((U:ℂ)+(V:ℂ)*Complex.I) = ((U:ℝ):ℂ) + ((V:ℝ):ℂ)*Complex.I := by push_cast; ring
  have huv : ‖((U:ℂ)+(V:ℂ)*Complex.I)‖^2 = (U:ℝ)^2 + (V:ℝ)^2 := by
    rw [hv, Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [← huv]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- **Truncation preserves the disc.** If `U² + V² ≤ (2^{p+60} - 28)²` then the truncated point
`(U tdiv 2^60, V tdiv 2^60)` satisfies `u² + v² ≤ 4^p`. -/
theorem TdivDiscSq (p : ℕ) (U V : ℤ)
    (h : (U : ℝ) ^ 2 + (V : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (p + 60) - 28) ^ 2) :
    (Int.tdiv U (2 ^ 60)) ^ 2 + (Int.tdiv V (2 ^ 60)) ^ 2 ≤ 4 ^ p := by
  have hU := tdivSqMulLe U ((2:ℤ)^60)
  have hV := tdivSqMulLe V ((2:ℤ)^60)
  have hU2 : (((Int.tdiv U (2^60)) : ℤ) : ℝ)^2 * (2:ℝ)^120 ≤ (U:ℝ)^2 := by
    have hc : (((Int.tdiv U (2^60)) : ℤ) : ℝ)^2 * ((2:ℝ)^60)^2 ≤ (U:ℝ)^2 := by exact_mod_cast hU
    rwa [show ((2:ℝ)^60)^2 = (2:ℝ)^120 from by rw [← pow_mul]] at hc
  have hV2 : (((Int.tdiv V (2^60)) : ℤ) : ℝ)^2 * (2:ℝ)^120 ≤ (V:ℝ)^2 := by
    have hc : (((Int.tdiv V (2^60)) : ℤ) : ℝ)^2 * ((2:ℝ)^60)^2 ≤ (V:ℝ)^2 := by exact_mod_cast hV
    rwa [show ((2:ℝ)^60)^2 = (2:ℝ)^120 from by rw [← pow_mul]] at hc
  have h2 : ((((Int.tdiv U (2^60)) : ℤ) : ℝ)^2 + (((Int.tdiv V (2^60)) : ℤ) : ℝ)^2) * (2:ℝ)^120
      ≤ (U:ℝ)^2 + (V:ℝ)^2 := by linarith
  have ha28 : ((2:ℝ)^(p+60) - 28)^2 < ((2:ℝ)^(p+60))^2 := by
    have hge : (28:ℝ) < (2:ℝ)^(p+60) := by
      have h3 : (2:ℝ)^60 ≤ (2:ℝ)^(p+60) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (28:ℝ) < 2^60 := by norm_num
      linarith
    nlinarith
  have heq : ((2:ℝ)^(p+60))^2 = (4:ℝ)^p * (2:ℝ)^120 := by
    have hl : ((2:ℝ)^(p+60))^2 = (2:ℝ)^(2*p+120) := by
      rw [← pow_mul]; congr 1; ring
    have hr : (4:ℝ)^p * (2:ℝ)^120 = (2:ℝ)^(2*p+120) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, ← pow_add]
    rw [hl, hr]
  have hlt : ((((Int.tdiv U (2^60)) : ℤ) : ℝ)^2 + (((Int.tdiv V (2^60)) : ℤ) : ℝ)^2) * (2:ℝ)^120
      < (4:ℝ)^p * (2:ℝ)^120 := by
    nlinarith [h2, h, ha28, heq]
  have hreal : (((Int.tdiv U (2^60)) : ℤ) : ℝ)^2 + (((Int.tdiv V (2^60)) : ℤ) : ℝ)^2 < (4:ℝ)^p :=
    lt_of_mul_lt_mul_right hlt (by positivity : (0:ℝ) ≤ (2:ℝ)^120)
  have hZ : (((Int.tdiv U (2^60))^2 + (Int.tdiv V (2^60))^2 : ℤ) : ℝ) < ((4:ℤ)^p : ℝ) := by
    push_cast
    exact hreal
  exact_mod_cast (le_of_lt hZ)

theorem CisTrunc (p : ℕ) (hp : 100 ≤ p) (U V : ℤ) (E A : ℂ)
    (hA : ‖A‖ ≤ 1 - 32 / (2 : ℝ) ^ (p + 60))
    (hZA : ‖((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) - A‖ ≤ 4 / (2 : ℝ) ^ (p + 60))
    (hAE : ‖A - E‖ ≤ 67 / (2 : ℝ) ^ (p + 60)) :
    (Int.tdiv U (2 ^ 60)) ^ 2 + (Int.tdiv V (2 ^ 60)) ^ 2 ≤ 4 ^ p ∧
    (2 : ℝ) ^ p * ‖(((Int.tdiv U (2 ^ 60) : ℤ) : ℂ)
        + ((Int.tdiv V (2 ^ 60) : ℤ) : ℂ) * Complex.I) / (2 : ℂ) ^ p - E‖ < 2 := by
  set z : ℂ := ((U : ℂ) + (V : ℂ) * Complex.I) / (2 : ℂ) ^ (p + 60) with hz
  set w : ℂ := ((Int.tdiv U (2^60) : ℤ) : ℂ) + ((Int.tdiv V (2^60) : ℤ) : ℂ) * Complex.I with hw
  -- the two given points put `z` strictly inside the disc of radius `1 - 28/2^{p+60}`
  have hzle : ‖z‖ ≤ 1 - 28 / (2:ℝ)^(p+60) := by
    have h1 : ‖z‖ ≤ ‖z - A‖ + ‖A‖ := by
      have h := norm_add_le (z - A) A
      simpa using h
    have hsum : ‖z - A‖ + ‖A‖ ≤ 4/(2:ℝ)^(p+60) + (1 - 32/(2:ℝ)^(p+60)) := add_le_add hZA hA
    have heq : 4/(2:ℝ)^(p+60) + (1 - 32/(2:ℝ)^(p+60)) = 1 - 28/(2:ℝ)^(p+60) := by
      field_simp
      ring
    linarith [h1, hsum, le_of_eq heq]
  -- first conclusion: the truncation still lies in the disc
  have hdisc : (Int.tdiv U (2 ^ 60)) ^ 2 + (Int.tdiv V (2 ^ 60)) ^ 2 ≤ 4 ^ p :=
    TdivDiscSq p U V (ZcNormSqBound p U V (by rw [← hz]; exact hzle))
  -- second conclusion: the truncation error rescaled by `2^p`
  have hwz : ‖w - (2:ℂ)^p * z‖ < Real.sqrt 2 := by
    have h := TdivScaleNormDiff p U V
    rwa [← hw, ← hz] at h
  have hSz : (2:ℝ)^p * ‖w / (2:ℂ)^p - z‖ = ‖w - (2:ℂ)^p * z‖ := by
    have hmul : (2:ℂ)^p * (w / (2:ℂ)^p - z) = w - (2:ℂ)^p * z := by field_simp
    rw [← hmul, norm_mul,
      show ‖((2:ℂ)^p)‖ = (2:ℝ)^p from by rw [Complex.norm_pow]; norm_num]
  have htri : ‖w / (2:ℂ)^p - E‖ ≤ ‖w/(2:ℂ)^p - z‖ + ‖z - A‖ + ‖A - E‖ := by
    have hsum : w / (2:ℂ)^p - E = (w/(2:ℂ)^p - z) + (z - A) + (A - E) := by ring
    rw [hsum]
    exact norm_add₃_le
  have hbound : (2:ℝ)^p * ‖w / (2:ℂ)^p - E‖ < 2 := by
    have h4 : (2:ℝ)^p * ‖w/(2:ℂ)^p - z‖ < Real.sqrt 2 := by rw [hSz]; exact hwz
    have h5 : (2:ℝ)^p * ‖z - A‖ ≤ (2:ℝ)^p * (4/(2:ℝ)^(p+60)) :=
      mul_le_mul_of_nonneg_left hZA (by positivity)
    have h6 : (2:ℝ)^p * ‖A - E‖ ≤ (2:ℝ)^p * (67/(2:ℝ)^(p+60)) :=
      mul_le_mul_of_nonneg_left hAE (by positivity)
    have h7 : (2:ℝ)^p * (4/(2:ℝ)^(p+60)) + (2:ℝ)^p * (67/(2:ℝ)^(p+60)) = 71/(2:ℝ)^60 := by
      rw [pow_add]; field_simp; ring
    have h8 : Real.sqrt 2 + 71/(2:ℝ)^60 < 2 := by
      have h9 : Real.sqrt 2 < 3/2 := by
        rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 3/2)]; norm_num
      have h10 : (71:ℝ)/(2:ℝ)^60 < 1/2 := by norm_num
      linarith
    have h9 := mul_le_mul_of_nonneg_left htri (by positivity : (0:ℝ) ≤ (2:ℝ)^p)
    have h10 : (2:ℝ)^p * (‖w/(2:ℂ)^p - z‖ + ‖z - A‖ + ‖A - E‖)
        = (2:ℝ)^p*‖w/(2:ℂ)^p - z‖ + (2:ℝ)^p*‖z - A‖ + (2:ℝ)^p*‖A - E‖ := by ring
    rw [h10] at h9
    linarith
  exact ⟨hdisc, hbound⟩

end Work.Fx
