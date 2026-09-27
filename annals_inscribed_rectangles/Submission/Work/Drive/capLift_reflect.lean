import Mathlib
import Submission.Work.Drive.cappingProjCoords

namespace Work.Drive

/-- Two vectors of `ℂ² ≅ ℝ⁴` with equal complex coordinates are equal. -/
lemma eq_of_c₁_c₂_eq {v w : Eucl 3} (h1 : c₁ v = c₁ w) (h2 : c₂ v = c₂ w) : v = w := by
  conv_lhs => rw [← ofComplex_c₁_c₂ v]
  conv_rhs => rw [← ofComplex_c₁_c₂ w]
  rw [h1, h2]

/-- The reflected square-root coordinate `w = u · d̄/‖d‖` is a unit complex number. -/
lemma norm_reflectW {u d : ℂ} (hu : ‖u‖ = 1) (hd : d ≠ 0) :
    ‖u * star d / (‖d‖ : ℂ)‖ = 1 := by
  rw [norm_div, norm_mul, norm_star, hu, one_mul, Complex.norm_of_nonneg (norm_nonneg d),
    div_self (norm_ne_zero_iff.mpr hd)]

/-- The norm of the reflected disk coordinate
`d_cap = √2 · (d/‖d‖) · √(1 - ‖d‖²/2)` is `√(2 - ‖d‖²)`, so `‖d_cap‖² = 2 - ‖d‖²`. -/
lemma norm_capReflectVec {d : ℂ} (hd : d ≠ 0) (hd2 : ‖d‖ ≤ Real.sqrt 2) :
    ‖((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ)) * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖
      = Real.sqrt (2 - ‖d‖ ^ 2) := by
  have hdne : (‖d‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hd
  have hsnn : (0 : ℝ) ≤ 1 - ‖d‖ ^ 2 / 2 := by
    have h2 : ‖d‖ ^ 2 ≤ 2 := by
      nlinarith [hd2, norm_nonneg d, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have hnorm : ‖((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ))
        * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖
      = Real.sqrt 2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
    rw [norm_div, Complex.norm_of_nonneg (norm_nonneg d)]
    rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_self hdne]; ring
  rw [hnorm, show Real.sqrt 2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2) = Real.sqrt (2 - ‖d‖ ^ 2) by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring]

/-- **The reflection of a configuration sphere lift across the Clifford torus is a cap sphere lift.**
For a unit complex `u` and a complex `d` with `0 < ‖d‖ ≤ √2`, the configuration sphere lift
`confProjVecOf u d` of a chord whose disk coordinate is `d` is *exactly* the cap lift
`capProjVecOf w d_cap` for `w = u * conj d / ‖d‖` and `d_cap = (√2 * d / ‖d‖) * √(1 - ‖d‖²/2)`.
This is the algebraic content of the "reflection continuation" used to build the smooth capped plane:
since `‖d_cap‖² = 2 - ‖d‖²`, a formal value `‖d‖ > 1` of the chord's disk coordinate is described by
the *cap* piece with `‖d_cap‖ < 1`, i.e. the projective class has crossed the Clifford torus
`{|c₁| = |c₂|}` of `ℝP³`. -/
theorem capLift_reflect {u d : ℂ} (hu : ‖u‖ = 1) (hd : d ≠ 0)
    (hd2 : ‖d‖ ≤ Real.sqrt 2) :
    capProjVecOf (u * star d / (‖d‖ : ℂ))
        (((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ))
          * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)) = confProjVecOf u d := by
  have hdne : (‖d‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hd
  rw [capProjVecOf, confProjVecOf]
  set r2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) with hr2def
  set m : ℂ := ((‖d‖ : ℝ) : ℂ) with hmdef
  set s : ℂ := ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) with hsdef
  have hm_ne : m ≠ 0 := by rw [hmdef]; exact Complex.ofReal_ne_zero.mpr hdne
  have hr2_ne : r2 ≠ 0 := by
    rw [hr2def]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hm_star : (starRingEnd ℂ) m = m := by rw [hmdef, Complex.conj_ofReal]
  have hconj : d * star d = m * m := by
    rw [show d * star d = ((‖d‖ ^ 2 : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    rw [hmdef]; push_cast; ring
  have hsnn : (0 : ℝ) ≤ 1 - ‖d‖ ^ 2 / 2 := by
    have h2 : ‖d‖ ^ 2 ≤ 2 := by
      nlinarith [hd2, norm_nonneg d, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have hnorm : ‖r2 * (d / m) * s‖ = Real.sqrt 2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
    rw [norm_mul, norm_mul, hr2def, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
    rw [norm_div, hmdef, Complex.norm_of_nonneg (norm_nonneg d)]
    rw [hsdef, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_self hdne]; ring
  have hcapnorm : ‖r2 * (d / m) * s‖ ^ 2 = 2 - ‖d‖ ^ 2 := by
    rw [hnorm, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt hsnn]
    ring
  have hcap : 1 - ‖r2 * (d / m) * s‖ ^ 2 / 2 = ‖d‖ ^ 2 / 2 := by rw [hcapnorm]; ring
  have hscap : Real.sqrt (1 - ‖r2 * (d / m) * s‖ ^ 2 / 2) = ‖d‖ / Real.sqrt 2 := by
    rw [hcap, Real.sqrt_div (sq_nonneg ‖d‖) 2, Real.sqrt_sq (norm_nonneg d)]
  have hA : (r2 * (d / m) * s) * (u * star d / m) / r2 = u * s := by
    rw [show (r2 * (d / m) * s) * (u * star d / m) / r2 = (d * star d / (m*m)) * (u*s) by
      field_simp]
    rw [hconj, div_self (mul_ne_zero hm_ne hm_ne), one_mul]
  have hB : star (u * star d / m) * ((Real.sqrt (1 - ‖r2 * (d / m) * s‖ ^ 2 / 2) : ℝ) : ℂ)
      = star u * d / r2 := by
    rw [hscap]
    rw [show ((‖d‖ / Real.sqrt 2 : ℝ) : ℂ) = m / r2 by rw [hmdef, hr2def]; push_cast; ring]
    rw [show star (u * star d / m) = star u * d / m by
      rw [Complex.star_def, map_div₀, map_mul, Complex.conj_conj, hm_star]]
    field_simp
  refine eq_of_c₁_c₂_eq ?_ ?_
  · rw [c₁_ofComplex, c₁_ofComplex]; exact hA
  · rw [c₂_ofComplex, c₂_ofComplex]; exact hB

end Work.Drive
