import Mathlib

namespace Work.LinnikAreas2

/-- Elementary monotonicity estimate for real powers: if `0 ≤ r ≤ 1` and `X > 0` then
`X ^ (r * σ)` is at most `max 1 (X ^ σ)`. -/
theorem rpow_mul_le_max {X : ℝ} (hX : 0 < X) {r σ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    X ^ (r * σ) ≤ max 1 (X ^ σ) := by
  rcases lt_trichotomy X 1 with hlt | heq | hgt
  · rcases lt_or_ge (0 : ℝ) σ with hσ | hσ
    · exact (Real.rpow_le_one hX.le hlt.le (mul_nonneg hr0 hσ.le)).trans (le_max_left _ _)
    · have hle : σ ≤ r * σ := by nlinarith
      exact ((Real.rpow_le_rpow_left_iff_of_base_lt_one hX hlt).mpr hle).trans (le_max_right _ _)
  · subst heq; simp
  · rcases lt_or_ge (0 : ℝ) σ with hσ | hσ
    · have hle : r * σ ≤ σ := by nlinarith
      exact ((Real.rpow_le_rpow_left_iff hgt).mpr hle).trans (le_max_right _ _)
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hgt.le
        (mul_nonpos_of_nonneg_of_nonpos hr0 hσ)).trans (le_max_left _ _)

/-- The chain-rule derivative of the parametrised complex power `r ↦ X ^ (r * s)`. -/
theorem hasDerivAt_cpow_ofReal_mul {X : ℝ} (hX : 0 < X) (s : ℂ) (r : ℝ) :
    HasDerivAt (fun u : ℝ => (X : ℂ) ^ ((u : ℂ) * s))
      (s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))) r := by
  have h1 : HasDerivAt (fun y : ℂ => (X : ℂ) ^ y)
      ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ)) ((r : ℂ) * s) :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).hasDerivAt
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * s) s r := by
    have h : HasDerivAt (fun u : ℝ => u • s) s r := by
      simpa using (hasDerivAt_id r).smul_const s
    simpa [Algebra.smul_def] using h
  have h3 := HasDerivAt.scomp r h1 h2
  simpa [Function.comp_def, smul_eq_mul] using h3

/-- Norm bound for the derivative term `X ^ (r * s) * log X`. -/
theorem norm_cpow_mul_log_le {X : ℝ} (hX : 0 < X) (s : ℂ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    ‖(X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ)‖ ≤ |Real.log X| * max 1 (X ^ s.re) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, ← Complex.ofReal_log hX.le,
      Complex.norm_real, Real.norm_eq_abs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_comm]
  exact mul_le_mul_of_nonneg_left (rpow_mul_le_max hX hr0 hr1) (abs_nonneg _)

/-- The difference quotient at `0` of `u ↦ X ^ u - Y ^ u` is bounded by the stated maximum. -/
theorem dslope_diff_cpow_norm_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (s : ℂ) :
    ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 s‖
      ≤ |Real.log X| * max 1 (X ^ s.re) + |Real.log Y| * max 1 (Y ^ s.re) := by
  rcases eq_or_ne s 0 with rfl | hs
  · have hf : deriv (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0
        = Complex.log (X : ℂ) - Complex.log (Y : ℂ) := by
      have hx : HasDerivAt (fun u : ℂ => (X : ℂ) ^ u) (Complex.log (X : ℂ)) 0 := by
        have h := (Complex.hasStrictDerivAt_const_cpow
          (x := (X : ℂ)) (y := 0) (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).hasDerivAt
        simpa using h
      have hy : HasDerivAt (fun u : ℂ => (Y : ℂ) ^ u) (Complex.log (Y : ℂ)) 0 := by
        have h := (Complex.hasStrictDerivAt_const_cpow
          (x := (Y : ℂ)) (y := 0) (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).hasDerivAt
        simpa using h
      exact (hx.sub hy).deriv
    rw [dslope_same, hf]
    have h2 : ‖Complex.log (X : ℂ) - Complex.log (Y : ℂ)‖ ≤ |Real.log X| + |Real.log Y| := by
      calc ‖Complex.log (X : ℂ) - Complex.log (Y : ℂ)‖
          ≤ ‖Complex.log (X : ℂ)‖ + ‖Complex.log (Y : ℂ)‖ := norm_sub_le _ _
        _ = |Real.log X| + |Real.log Y| := by
              rw [← Complex.ofReal_log hX.le, ← Complex.ofReal_log hY.le, Complex.norm_real,
                  Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    simpa using h2
  · have hds : dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 s
        = s⁻¹ • ((X : ℂ) ^ s - (Y : ℂ) ^ s) := by
      rw [dslope_of_ne _ hs, slope_def_module, sub_zero]
      simp
    set D : ℝ := |Real.log X| * max 1 (X ^ s.re) + |Real.log Y| * max 1 (Y ^ s.re) with hD
    have hbound : ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ ≤ ‖s‖ * D := by
      have hf' : ∀ r ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt (fun u : ℝ => (X : ℂ) ^ ((u : ℂ) * s) - (Y : ℂ) ^ ((u : ℂ) * s))
            (s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))
              - s * ((Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ)))
            (Set.Icc (0 : ℝ) 1) r := by
        intro r hr
        exact ((hasDerivAt_cpow_ofReal_mul hX s r).sub
                (hasDerivAt_cpow_ofReal_mul hY s r)).hasDerivWithinAt
      have hb : ∀ r ∈ Set.Ico (0 : ℝ) 1,
          ‖s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))
              - s * ((Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ))‖ ≤ ‖s‖ * D := by
        intro r hr
        have hr0 : 0 ≤ r := hr.1
        have hr1 : r ≤ 1 := le_of_lt hr.2
        have hXb := norm_cpow_mul_log_le hX s hr0 hr1
        have hYb := norm_cpow_mul_log_le hY s hr0 hr1
        calc ‖s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))
                - s * ((Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ))‖
            ≤ ‖s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))‖
                + ‖s * ((Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ))‖ := norm_sub_le _ _
          _ = ‖s‖ * ‖(X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ)‖
                + ‖s‖ * ‖(Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ)‖ := by
                simp only [norm_mul]
          _ ≤ ‖s‖ * (|Real.log X| * max 1 (X ^ s.re))
                + ‖s‖ * (|Real.log Y| * max 1 (Y ^ s.re)) :=
                add_le_add (mul_le_mul_of_nonneg_left hXb (norm_nonneg _))
                           (mul_le_mul_of_nonneg_left hYb (norm_nonneg _))
          _ = ‖s‖ * D := by rw [hD]; ring
      have hmain := norm_image_sub_le_of_norm_deriv_le_segment_01'
        (f := fun u : ℝ => (X : ℂ) ^ ((u : ℂ) * s) - (Y : ℂ) ^ ((u : ℂ) * s))
        (f' := fun r : ℝ => s * ((X : ℂ) ^ ((r : ℂ) * s) * Complex.log (X : ℂ))
                            - s * ((Y : ℂ) ^ ((r : ℂ) * s) * Complex.log (Y : ℂ)))
        hf' hb
      have hg10 : (fun u : ℝ => (X : ℂ) ^ ((u : ℂ) * s) - (Y : ℂ) ^ ((u : ℂ) * s)) 1
          - (fun u : ℝ => (X : ℂ) ^ ((u : ℂ) * s) - (Y : ℂ) ^ ((u : ℂ) * s)) 0
            = (X : ℂ) ^ s - (Y : ℂ) ^ s := by simp
      rwa [hg10] at hmain
    have hgoal : ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 s‖ ≤ D := by
      calc ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (Y : ℂ) ^ u) 0 s‖
          = ‖s⁻¹‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ := by rw [hds, norm_smul]
        _ = ‖s‖⁻¹ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ := by rw [norm_inv]
        _ ≤ ‖s‖⁻¹ * (‖s‖ * D) :=
              mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg _))
        _ = D := by rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs), one_mul]
    rw [hD] at hgoal
    exact hgoal

end Work.LinnikAreas2
