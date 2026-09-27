import Mathlib

namespace Work.Drive.N2Lead

/-- `cos (arctan (b/a)) = a / √(a² + b²)` for `a > 0` (the modulus of `a + i b`). -/
lemma cos_arctan_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.cos (Real.arctan (b / a)) = a / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hS : Real.sqrt (a^2 + b^2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [Real.cos_arctan]
  have h1 : (1:ℝ) + (b/a)^2 = (a^2 + b^2)/a^2 := by field_simp
  have h2 : Real.sqrt (1 + (b/a)^2) = Real.sqrt (a^2 + b^2)/a := by
    rw [h1, Real.sqrt_div (show (0:ℝ) ≤ a^2 + b^2 by positivity), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  rw [h2]; field_simp

/-- `sin (arctan (b/a)) = b / √(a² + b²)` for `a > 0`. -/
lemma sin_arctan_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.sin (Real.arctan (b / a)) = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hS : Real.sqrt (a^2 + b^2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [Real.sin_arctan]
  have h1 : (1:ℝ) + (b/a)^2 = (a^2 + b^2)/a^2 := by field_simp
  have h2 : Real.sqrt (1 + (b/a)^2) = Real.sqrt (a^2 + b^2)/a := by
    rw [h1, Real.sqrt_div (show (0:ℝ) ≤ a^2 + b^2 by positivity), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  rw [h2]; field_simp

open scoped Manifold ContDiff Topology in
/-- **The polar parametrisation of the two model arcs of the anchor level** (§3.2 step 1 of
`N2Lead/NOTES_LEAD_saddlePacket.md`).

Let `ηs > 0` and

* `φU w = π/2 - (1/2) * arctan (w / ηs)`, `φL w = -(π/2) - (1/2) * arctan (w / ηs)`,

the arguments of the two points `z` with `z² = -ηs + i w` in the upper respectively lower
half-plane.  Then the **polar point of the radial profile** `r = √(ηs / -cos (2φ))` — the profile of
`Work.Drive.N2Lead.mobius_lowerProfile` on its arc range — at those two angles is the square root of
`-ηs + i w`:

* `√(ηs / -cos (2 φU w)) * exp (i φU w) = I * √(ηs - i w)` (the *upper* arc, `Im > 0`);
* `√(ηs / -cos (2 φL w)) * exp (i φL w) = -(I * √(ηs - i w))` (the *lower* arc, `Im < 0`);
* and both squares are `-ηs + i w`.

Proof: `2 φU w = π - arctan (w/ηs)`, so `-cos (2 φU w) = ηs/√(ηs²+w²)` and
`sin (2 φU w) = w/√(ηs²+w²)`; hence the modulus of the right-hand side is `(ηs²+w²)^{1/4}`, equal to
`√(ηs / -cos (2 φU w))`, and its argument is `φU w`, which pins the principal square root
(`Complex.sqrt` is the principal branch); the lower arc is the negative of the upper one.  This is
the identification that lets the packet's polar curve `C₀ t = cE3 (r (Θ t) * exp (i Θ t))` coincide
with the model picture `cE3 (Z x)` on the two pinned arcs of the anchor level. -/
theorem polarArc_eq_sqrt {ηs : ℝ} (hηs : 0 < ηs) (w : ℝ) :
    let φU : ℝ := Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)
    let φL : ℝ := -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs)
    Real.sqrt (ηs / -Real.cos (2 * φU)) * Complex.exp ((φU : ℂ) * Complex.I)
        = Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I) ∧
      Real.sqrt (ηs / -Real.cos (2 * φL)) * Complex.exp ((φL : ℂ) * Complex.I)
        = -(Complex.I * Complex.sqrt ((ηs : ℂ) - (w : ℂ) * Complex.I)) ∧
      (Real.sqrt (ηs / -Real.cos (2 * φU)) * Complex.exp ((φU : ℂ) * Complex.I)) ^ 2
        = (-ηs : ℂ) + (w : ℂ) * Complex.I ∧
      (Real.sqrt (ηs / -Real.cos (2 * φL)) * Complex.exp ((φL : ℂ) * Complex.I)) ^ 2
        = (-ηs : ℂ) + (w : ℂ) * Complex.I := by
  -- Unfold the two `let`s and name the recurring quantities.
  dsimp only
  set t : ℝ := Real.arctan (w / ηs) with ht
  set φU : ℝ := Real.pi / 2 - (1 / 2) * t with hφU
  set φL : ℝ := -(Real.pi / 2) - (1 / 2) * t with hφL
  set S : ℝ := Real.sqrt (ηs ^ 2 + w ^ 2) with hSdef
  set AU : ℝ := Real.sqrt (ηs / -Real.cos (2 * φU)) with hAU
  set AL : ℝ := Real.sqrt (ηs / -Real.cos (2 * φL)) with hAL
  set z : ℂ := (ηs : ℂ) - (w : ℂ) * Complex.I with hz
  set d : ℂ := Complex.I * Complex.sqrt z with hd
  -- `S` is the modulus of `√(ηs² + w²)`.
  have hSpos : 0 < S := by rw [hSdef]; exact Real.sqrt_pos_of_pos (by positivity)
  have hSne : S ≠ 0 := ne_of_gt hSpos
  -- The values of `cos t` and `sin t` (`t = arctan (w/ηs)`).
  have hcos : Real.cos t = ηs / S := by
    rw [ht, hSdef]; exact cos_arctan_div hηs w
  have hsin : Real.sin t = w / S := by
    rw [ht, hSdef]; exact sin_arctan_div hηs w
  -- The double-angle values, for both `φU` and `φL`.
  have hcos2U : Real.cos (2 * φU) = -ηs / S := by
    have h2 : 2 * φU = Real.pi - t := by rw [hφU]; ring
    rw [h2, Real.cos_pi_sub, hcos]; ring
  have hsin2U : Real.sin (2 * φU) = w / S := by
    have h2 : 2 * φU = Real.pi - t := by rw [hφU]; ring
    rw [h2, Real.sin_pi_sub, hsin]
  have hcos2L : Real.cos (2 * φL) = -ηs / S := by
    have h2 : 2 * φL = -(Real.pi + t) := by rw [hφL]; ring
    rw [h2, Real.cos_neg, add_comm, Real.cos_add_pi, hcos]; ring
  have hsin2L : Real.sin (2 * φL) = w / S := by
    have h2 : 2 * φL = -(Real.pi + t) := by rw [hφL]; ring
    rw [h2, Real.sin_neg, add_comm, Real.sin_add_pi, hsin]; ring
  -- Hence `-cos (2φ) = ηs/S` and the two profiles equal `√S`, i.e. `(ηs²+w²)^{1/4}`.
  have hnegcos2U : -Real.cos (2 * φU) = ηs / S := by rw [hcos2U]; ring
  have hnegcos2L : -Real.cos (2 * φL) = ηs / S := by rw [hcos2L]; ring
  have hAUval : ηs / -Real.cos (2 * φU) = S := by rw [hnegcos2U]; field_simp
  have hALval : ηs / -Real.cos (2 * φL) = S := by rw [hnegcos2L]; field_simp
  have hAU2 : AU ^ 2 = S := by
    have hpos : 0 < ηs / -Real.cos (2 * φU) :=
      div_pos hηs (by rw [hnegcos2U]; exact div_pos hηs hSpos)
    rw [hAU, Real.sq_sqrt (le_of_lt hpos), hAUval]
  have hAL2 : AL ^ 2 = S := by
    have hpos : 0 < ηs / -Real.cos (2 * φL) :=
      div_pos hηs (by rw [hnegcos2L]; exact div_pos hηs hSpos)
    rw [hAL, Real.sq_sqrt (le_of_lt hpos), hALval]
  have hAUpos : 0 < AU := by rw [hAU, Real.sqrt_pos]; rw [hAUval]; exact hSpos
  -- `sin φU > 0`, because `φU = π/2 - t/2` with `|t/2| < π/2`.
  have hsinφU : 0 < Real.sin φU := by
    rw [hφU, Real.sin_pi_div_two_sub]
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    constructor
    · have h := Real.neg_pi_div_two_lt_arctan (w/ηs); rw [ht]; linarith [Real.pi_pos]
    · have h := Real.arctan_lt_pi_div_two (w/ηs); rw [ht]; linarith [Real.pi_pos]
  -- The square root on the right: `(√z)² = z` and `√z` has positive real part.
  have hzre : z.re = ηs := by rw [hz]; simp
  have hzne : z ≠ 0 := by
    intro h
    have : z.re = 0 := by rw [h]; simp
    rw [hzre] at this; linarith
  have hsqz : (Complex.sqrt z) ^ 2 = z := by
    rw [sqrt_eq_exp hzne, pow_two, ← Complex.exp_add,
      show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring, Complex.exp_log hzne]
  have hdsq : d ^ 2 = (-ηs : ℂ) + (w : ℂ) * Complex.I := by
    rw [hd, mul_pow, hsqz, Complex.I_sq, hz]; ring
  have hdim : 0 < d.im := by
    rw [hd, Complex.I_mul_im]
    have h : (Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2) := by
      rw [Complex.sqrt, Complex.cpow_inv_two_re]
    rw [h, hzre]
    apply Real.sqrt_pos_of_pos
    have := norm_nonneg z
    linarith
  -- The square of the right-hand side, and of the left-hand side.
  have hScos : S * Real.cos (2 * φU) = -ηs := by rw [hcos2U]; field_simp
  have hSsin : S * Real.sin (2 * φU) = w := by rw [hsin2U]; field_simp
  have hE2 : (Complex.exp ((φU : ℂ) * Complex.I))^2
      = Complex.exp ((↑(2 * φU) : ℂ) * Complex.I) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have hAUc : ((AU : ℂ))^2 = (S : ℂ) := by rw [← Complex.ofReal_pow, hAU2]
  have hSF : (S : ℂ) * Complex.exp ((↑(2 * φU) : ℂ) * Complex.I)
      = (-ηs : ℂ) + (w : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp only [zero_mul, mul_zero]
      rw [hScos]; ring
    · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      simp only [zero_mul, mul_zero, add_zero]
      rw [hSsin]; ring
  have hsqU : ((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I)) ^ 2
      = (-ηs : ℂ) + (w : ℂ) * Complex.I := by
    rw [mul_pow, hAUc, hE2, hSF]
  -- The left-hand side lies in the open upper half plane.
  have hImAU : 0 < ((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I)).im := by
    have him : ((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I)).im = AU * Real.sin φU := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
        Complex.exp_ofReal_mul_I_re]
      ring
    rw [him]; exact mul_pos hAUpos hsinφU
  -- Both sides are square roots of `-ηs + i w` with positive imaginary part: they coincide.
  have h1 : (AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I) = d := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp
      (show ((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I))^2 = d^2 by rw [hsqU, hdsq]))
      with h | h
    · exact h
    · exfalso
      have him1 : ((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I)).im = -d.im := by
        rw [h, Complex.neg_im]
      linarith [hImAU, hdim]
  -- `φL = φU - π`: the lower arc is the negative of the upper one.
  have hALeqAU : AL = AU := by rw [hAL, hAU, hcos2L, hcos2U]
  have hexpL : Complex.exp ((φL : ℂ) * Complex.I) = -Complex.exp ((φU : ℂ) * Complex.I) := by
    have hrel : φL = φU - Real.pi := by rw [hφU, hφL]; ring
    rw [hrel]
    have hcast2 : (↑(φU - Real.pi) : ℂ) * Complex.I
        = (↑φU : ℂ) * Complex.I + -(↑Real.pi * Complex.I) := by push_cast; ring
    rw [hcast2, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  have h2 : (AL : ℂ) * Complex.exp ((φL : ℂ) * Complex.I) = -d := by
    have hh : (AL : ℂ) * Complex.exp ((φL : ℂ) * Complex.I)
        = -((AU : ℂ) * Complex.exp ((φU : ℂ) * Complex.I)) := by
      rw [hALeqAU, hexpL]; ring
    rw [hh, h1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1
  · exact h2
  · exact hsqU
  · rw [h2, neg_sq, hdsq]

end Work.Drive.N2Lead
