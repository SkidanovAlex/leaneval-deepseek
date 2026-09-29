import Mathlib
import Submission.Work.Fx.scaleCommon
import Submission.Work.Fx.scale_sqrt_le
import Submission.Work.Fx.inDisc_scaleDiv

namespace Work.Fx
open HvdH

/-- The scaled fixed-point error of a pair equals the complex norm of the integer data minus
`2^p` times the true value. -/
theorem fxC_norm_eq (p : ℕ) (z : ℤ × ℤ) (x : ℂ) :
    (2 : ℝ) ^ p * ‖fxC p z - x‖
      = ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) - ((2 : ℝ) ^ p : ℂ) * x‖ := by
  have hcast : ((2 : ℝ) ^ p : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  have hnorm : ‖((2 : ℂ) ^ p)‖ = (2 : ℝ) ^ p := by rw [norm_pow]; norm_num
  calc (2 : ℝ) ^ p * ‖fxC p z - x‖
      = ‖((2 : ℂ) ^ p)‖ * ‖fxC p z - x‖ := by rw [hnorm]
    _ = ‖(2 : ℂ) ^ p * (fxC p z - x)‖ := (norm_mul _ _).symm
    _ = ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) - (2 : ℂ) ^ p * x‖ := by
          congr 1
          rw [fxC, mul_sub, mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
    _ = ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) - ((2 : ℝ) ^ p : ℂ) * x‖ := by rw [hcast]

/-- Truncating division identity: `b` times the rounded pair equals the exact scaled value
minus the complex remainder of the two truncating divisions. -/
theorem tdivScaleId (p c : ℕ) (x0 y0 : ℤ) (b : ℕ) :
    (((Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b : ℤ) : ℂ)
        + ((Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b : ℤ) : ℂ) * Complex.I) * (b : ℂ)
      = ((2 : ℝ) ^ p : ℂ) * (c : ℂ) * ((x0 : ℂ) + (y0 : ℂ) * Complex.I)
        - (((Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b : ℤ) : ℂ)
          + ((Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b : ℤ) : ℂ) * Complex.I) := by
  set X' : ℤ := Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b with hX'def
  set Y' : ℤ := Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b with hY'def
  set r : ℤ := Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b with hrdef
  set s : ℤ := Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b with hsdef
  have hcast : ((2 : ℝ) ^ p : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  have hx := Int.tmod_add_tdiv_mul ((2 : ℤ) ^ p * ((c : ℤ) * x0)) (b : ℤ)
  have hy := Int.tmod_add_tdiv_mul ((2 : ℤ) ^ p * ((c : ℤ) * y0)) (b : ℤ)
  have hxc : (X' : ℂ) * (b : ℂ) = (2 : ℂ) ^ p * (c : ℂ) * (x0 : ℂ) - (r : ℂ) := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) hx
    push_cast at h
    linear_combination h
  have hyc : (Y' : ℂ) * (b : ℂ) = (2 : ℂ) ^ p * (c : ℂ) * (y0 : ℂ) - (s : ℂ) := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) hy
    push_cast at h
    linear_combination h
  rw [hcast]
  have hmul : ((X' : ℂ) + (Y' : ℂ) * Complex.I) * (b : ℂ)
      = ((X' : ℂ) * (b : ℂ)) + ((Y' : ℂ) * (b : ℂ)) * Complex.I := by ring
  rw [hmul, hxc, hyc]
  ring

/-- The modulus `b` exceeds `2^p` by at most the scaled input error plus one. -/
theorem scaleErrAux {p c : ℕ} {x0 y0 : ℤ} {b : ℕ} {x : ℂ}
    (hb1 : 2 ^ p ≤ b)
    (hb3 : (b : ℝ) ≤ max ((2 : ℝ) ^ p)
            (Real.sqrt ((((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2) + 1))
    (hx : (c : ℝ) * ‖x‖ ≤ 1) :
    (b : ℝ) - (2 : ℝ) ^ p ≤
      (c : ℝ) * ‖(x0 : ℂ) + (y0 : ℂ) * Complex.I - ((2 : ℝ) ^ p : ℂ) * x‖ + 1 := by
  have hb1R : (2 : ℝ) ^ p ≤ (b : ℝ) := by exact_mod_cast hb1
  have hSle : Real.sqrt ((((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ p
        + (c : ℝ) * ‖(x0 : ℂ) + (y0 : ℂ) * Complex.I - ((2 : ℝ) ^ p : ℂ) * x‖ := by
    have h := scale_sqrt_le p c x0 y0 x
    have h1 : (2 : ℝ) ^ p * (c : ℝ) * ‖x‖ ≤ (2 : ℝ) ^ p := by
      have h' := mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ (2 : ℝ) ^ p by positivity)
      rw [mul_one] at h'
      calc (2 : ℝ) ^ p * (c : ℝ) * ‖x‖ = (2 : ℝ) ^ p * ((c : ℝ) * ‖x‖) := by ring
        _ ≤ (2 : ℝ) ^ p := h'
    linarith [h, h1]
  by_cases hcase : (b : ℝ) ≤ (2 : ℝ) ^ p
  · have : (0 : ℝ) ≤ (c : ℝ) * ‖(x0 : ℂ) + (y0 : ℂ) * Complex.I - ((2 : ℝ) ^ p : ℂ) * x‖ := by
      positivity
    linarith
  · rw [not_le] at hcase
    have hmax : (b : ℝ) ≤ Real.sqrt ((((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2) + 1 := by
      by_cases hh : (2 : ℝ) ^ p ≤ Real.sqrt ((((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2) + 1
      · rwa [max_eq_right hh] at hb3
      · rw [not_le] at hh
        rw [max_eq_left hh.le] at hb3; linarith
    linarith [hmax, hSle]

/-- Purely mathematical core of paper Lemma 2.2 (fixed-point scaling), roundings already performed:
`X' = trunc(2^p·c·x0 / b)`, `Y' = trunc(2^p·c·y0 / b)`, where `b` is the word's
`max 2^p (⌊√(c²(x0²+y0²))⌋+1)`.  The hypotheses are exactly what that `b` satisfies:
`2^p ≤ b`, `b² > (c x0)² + (c y0)²`, and `b ≤ max 2^p (√((c x0)²+(c y0)²) + 1)`.
Conclusion: the rounded pair is in the disc and satisfies the paper's error bound
`ε(ṽ) < 2c·ε(ũ) + 3` for every true value `x` with `c‖x‖ ≤ 1`. -/
theorem scaleMathB {p c : ℕ} {x0 y0 : ℤ} {b : ℕ} (hc : 1 ≤ c) {x : ℂ}
    (hx : (c : ℝ) * ‖x‖ ≤ 1)
    (hb1 : 2 ^ p ≤ b)
    (hb2 : ((b : ℝ)) ^ 2 > (((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2)
    (hb3 : (b : ℝ) ≤ max ((2 : ℝ) ^ p)
            (Real.sqrt ((((c : ℤ) * x0 : ℤ) : ℝ) ^ 2 + (((c : ℤ) * y0 : ℤ) : ℝ) ^ 2) + 1)) :
    HvdH.inDisc p (Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b, Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b) ∧
      (2 : ℝ) ^ p * ‖HvdH.fxC p (Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b,
          Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b) - (c : ℂ) * x‖ <
        2 * c * ((2 : ℝ) ^ p * ‖HvdH.fxC p (x0, y0) - x‖) + 3 := by
  have hbpos : (0 : ℤ) < (b : ℤ) := by
    have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ p := by
      have : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
      exact_mod_cast this
    have h2 : (2 : ℤ) ^ p ≤ (b : ℤ) := by exact_mod_cast hb1
    linarith
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hb1R : (2 : ℝ) ^ p ≤ (b : ℝ) := by exact_mod_cast hb1
  refine ⟨inDisc_scaleDiv (p := p) (X := (c : ℤ) * x0) (Y := (c : ℤ) * y0) (b := b) hb1 hb2, ?_⟩
  set X' : ℤ := Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b with hX'def
  set Y' : ℤ := Int.tdiv ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b with hY'def
  set r : ℤ := Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * x0)) b with hrdef
  set s : ℤ := Int.tmod ((2 : ℤ) ^ p * ((c : ℤ) * y0)) b with hsdef
  set M : ℂ := ((2 : ℝ) ^ p : ℂ) * (c : ℂ) with hMdef
  set a : ℂ := (x0 : ℂ) + (y0 : ℂ) * Complex.I with hadef
  set Z : ℂ := (X' : ℂ) + (Y' : ℂ) * Complex.I with hZdef
  set Rc : ℂ := (r : ℂ) + (s : ℂ) * Complex.I with hRcdef
  have hbne : (b : ℂ) ≠ 0 := by
    intro h
    have h2 : (b : ℝ) = 0 := by
      have := congrArg Complex.re h
      simpa using this
    exact absurd h2 (ne_of_gt hbR)
  have hZb : Z * (b : ℂ) = M * a - Rc := by
    have h := tdivScaleId p c x0 y0 b
    rw [hZdef, hMdef, hadef, hRcdef, hX'def, hY'def, hrdef, hsdef]
    exact h
  have hRc : ‖Rc‖ < 2 * (b : ℝ) := by
    have hr : |(r : ℝ)| < (b : ℝ) := by
      have h := tmod_abs_lt_R ((2 : ℤ) ^ p * ((c : ℤ) * x0)) hbpos
      rw [← hrdef] at h
      simpa using h
    have hs : |(s : ℝ)| < (b : ℝ) := by
      have h := tmod_abs_lt_R ((2 : ℤ) ^ p * ((c : ℤ) * y0)) hbpos
      rw [← hsdef] at h
      simpa using h
    calc ‖Rc‖ = ‖(r : ℂ) + (s : ℂ) * Complex.I‖ := by rw [hRcdef]
      _ ≤ ‖(r : ℂ)‖ + ‖(s : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |(r : ℝ)| + |(s : ℝ)| := by
            have e1 : ‖(r : ℂ)‖ = |(r : ℝ)| := by simp
            have e2 : ‖(s : ℂ) * Complex.I‖ = |(s : ℝ)| := by simp
            rw [e1, e2]
      _ < (b : ℝ) + (b : ℝ) := by linarith
      _ = 2 * (b : ℝ) := by ring
  have hnormM : ‖M‖ = (2 : ℝ) ^ p * (c : ℝ) := by
    rw [hMdef, norm_mul]
    have e1 : ‖((2 : ℝ) ^ p : ℂ)‖ = (2 : ℝ) ^ p := by simp
    have e2 : ‖(c : ℂ)‖ = (c : ℝ) := by simp
    rw [e1, e2]
  have hE : (2 : ℝ) ^ p * ‖fxC p (x0, y0) - x‖ = ‖a - ((2 : ℝ) ^ p : ℂ) * x‖ := by
    rw [hadef]
    exact fxC_norm_eq p (x0, y0) x
  have hL : (2 : ℝ) ^ p * ‖fxC p (X', Y') - (c : ℂ) * x‖ = ‖Z - M * x‖ := by
    rw [fxC_norm_eq p (X', Y') ((c : ℂ) * x)]
    congr 1
    rw [hZdef, hMdef]
    ring
  have hax : ‖a - (b : ℂ) * x‖ ≤ ‖a - ((2 : ℝ) ^ p : ℂ) * x‖ + ((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖ := by
    have hsplit : a - (b : ℂ) * x = (a - ((2 : ℝ) ^ p : ℂ) * x) + (((2 : ℝ) ^ p : ℂ) - (b : ℂ)) * x := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖(((2 : ℝ) ^ p : ℂ) - (b : ℂ)) * x‖ ≤ ((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖ := by
      have he : ((2 : ℝ) ^ p : ℂ) - (b : ℂ) = ((((2 : ℝ) ^ p - (b : ℝ) : ℝ)) : ℂ) := by
        rw [show ((2 : ℝ) ^ p : ℂ) = ((((2 : ℝ) ^ p : ℝ)) : ℂ) from by rw [Complex.ofReal_pow],
            show (b : ℂ) = (((b : ℝ)) : ℂ) from by push_cast; ring,
            ← Complex.ofReal_sub]
      rw [he, norm_mul]
      rw [show ‖((((2 : ℝ) ^ p - (b : ℝ) : ℝ)) : ℂ)‖ = |(2 : ℝ) ^ p - (b : ℝ)| from RCLike.norm_ofReal _]
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hb1R] : (0 : ℝ) ≤ (b : ℝ) - (2 : ℝ) ^ p)]
    linarith [h2]
  have hbmp := scaleErrAux (p := p) (c := c) (x0 := x0) (y0 := y0) (b := b) (x := x) hb1 hb3 hx
  have hb2pnn : (0 : ℝ) ≤ (b : ℝ) - (2 : ℝ) ^ p := by linarith [hb1R]
  have step : (2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ / (b : ℝ)
      ≤ 2 * ((c : ℝ) * ‖a - ((2 : ℝ) ^ p : ℂ) * x‖) + 1 := by
    have hbdiv : (2 : ℝ) ^ p / (b : ℝ) ≤ 1 := by
      rw [div_le_one hbR]; exact hb1R
    have hcancel : (2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ / (b : ℝ)
        = ((2 : ℝ) ^ p / (b : ℝ)) * ((c : ℝ) * ‖a - (b : ℂ) * x‖) := by ring
    rw [hcancel]
    have h1 : ((2 : ℝ) ^ p / (b : ℝ)) * ((c : ℝ) * ‖a - (b : ℂ) * x‖)
        ≤ 1 * ((c : ℝ) * ‖a - (b : ℂ) * x‖) :=
      mul_le_mul_of_nonneg_right hbdiv (by positivity)
    rw [one_mul] at h1
    have hA3 : (c : ℝ) * (((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖) ≤ (b : ℝ) - (2 : ℝ) ^ p := by
      have h4 := mul_le_mul_of_nonneg_right hx hb2pnn
      rw [one_mul] at h4
      calc (c : ℝ) * (((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖)
          = ((c : ℝ) * ‖x‖) * ((b : ℝ) - (2 : ℝ) ^ p) := by ring
        _ ≤ (b : ℝ) - (2 : ℝ) ^ p := h4
    have h2 : (c : ℝ) * ‖a - (b : ℂ) * x‖
        ≤ (c : ℝ) * ‖a - ((2 : ℝ) ^ p : ℂ) * x‖ + ((b : ℝ) - (2 : ℝ) ^ p) := by
      calc (c : ℝ) * ‖a - (b : ℂ) * x‖
          ≤ (c : ℝ) * (‖a - ((2 : ℝ) ^ p : ℂ) * x‖ + ((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖) :=
              mul_le_mul_of_nonneg_left hax (by positivity)
        _ = (c : ℝ) * ‖a - ((2 : ℝ) ^ p : ℂ) * x‖ + (c : ℝ) * (((b : ℝ) - (2 : ℝ) ^ p) * ‖x‖) := by ring
        _ ≤ (c : ℝ) * ‖a - ((2 : ℝ) ^ p : ℂ) * x‖ + ((b : ℝ) - (2 : ℝ) ^ p) := by linarith [hA3]
    linarith [h1, h2, hbmp]
  have hRcd : ‖Rc‖ / (b : ℝ) < 2 := by
    rw [div_lt_iff₀ hbR]
    exact hRc
  have h1 : ‖Z - M * x‖ ≤ ((2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ + ‖Rc‖) / (b : ℝ) := by
    have hdecomp : Z - M * x = (M * (a - (b : ℂ) * x) - Rc) / (b : ℂ) := by
      rw [eq_div_iff hbne, sub_mul, hZb]
      ring
    rw [hdecomp, norm_div]
    have hbn : ‖(b : ℂ)‖ = (b : ℝ) := by simp
    rw [hbn]
    have hnum : ‖M * (a - (b : ℂ) * x) - Rc‖ ≤ (2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ + ‖Rc‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, hnormM]
    exact div_le_div_of_nonneg_right hnum hbR.le
  have h2 : ((2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ + ‖Rc‖) / (b : ℝ)
      < (2 : ℝ) ^ p * (c : ℝ) * ‖a - (b : ℂ) * x‖ / (b : ℝ) + 2 := by
    rw [add_div]
    linarith [hRcd]
  rw [hL, hE]
  linarith [h1, h2, step]

end Work.Fx
