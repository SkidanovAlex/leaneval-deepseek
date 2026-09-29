import Mathlib
import Submission.CDTPlan.Interfaces

/-! # The derivative of the lune map at `0`

`lune c z = (z(1+c²) - (1+c²) + √((1+c²)²(1+z)² - 16c²z))/(2(c²-1))`.
The radicand at `z = 0` is `(1+c²)² > 0` (for `c > 1`), so the principal square root is analytic
there, and differentiating the numerator gives
`(1+c²) + ((1+c²)² - 8c²)/(1+c²)`, whence `lune c '(0) = (c²-1)/(c²+1)`. -/

namespace Work.ANum

open Submission.CDTPlan Complex

/-- For a positive real `x`, `((x:ℂ)^2)^(1/2-1) = (x:ℂ)⁻¹`. -/
lemma cpow_neg_half_sq_of_pos (x : ℝ) (hx : 0 < x) :
    ((x : ℂ) ^ 2) ^ (1 / 2 - 1 : ℂ) = (x : ℂ)⁻¹ := by
  have hx2 : (0 : ℝ) ≤ x ^ 2 := by positivity
  rw [show ((x : ℂ) ^ 2) = (((x ^ 2 : ℝ)) : ℂ) by push_cast; ring]
  rw [show (1 / 2 - 1 : ℂ) = (((-(1 : ℝ) / 2) : ℝ) : ℂ) by norm_num]
  rw [← ofReal_cpow hx2 ((-(1 : ℝ) / 2) : ℝ)]
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_div_two_eq_sqrt 1 (by positivity)]
  rw [Real.sqrt_sq hx.le, Real.rpow_one]
  simp

theorem lune_deriv_zero (c : ℝ) (hc : 1 < c) :
    HasDerivAt (lune c) ((c ^ 2 - 1) / (c ^ 2 + 1)) 0 := by
  have hcp : (0 : ℝ) < 1 + c ^ 2 := by positivity
  -- (1) the radicand map
  have hlin : HasDerivAt (fun z : ℂ => (1 : ℂ) + z) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add 1
  have hsq0 : HasDerivAt (fun z : ℂ => (1 + z) * (1 + z)) (1 * (1 + 0) + (1 + 0) * 1) 0 :=
    hlin.mul hlin
  have hfe : (fun z : ℂ => (1 + z) * (1 + z)) = fun z : ℂ => (1 + z) ^ 2 := by
    funext z; ring
  rw [hfe] at hsq0
  have hv0 : (1 * (1 + 0) + (1 + 0) * 1 : ℂ) = 2 := by ring
  have hsq := hsq0.congr_deriv hv0
  have hrad0 : HasDerivAt
      (fun z : ℂ => (1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z)
      ((1 + (c : ℂ) ^ 2) ^ 2 * 2 - 16 * (c : ℂ) ^ 2 * 1) 0 :=
    (hsq.const_mul ((1 + (c : ℂ) ^ 2) ^ 2)).sub
      ((hasDerivAt_id (0 : ℂ)).const_mul (16 * (c : ℂ) ^ 2))
  have hvR : (1 + (c : ℂ) ^ 2) ^ 2 * 2 - 16 * (c : ℂ) ^ 2 * 1 =
      2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2 := by ring
  have hrad := hrad0.congr_deriv hvR
  -- (2) the radicand at `0`
  have hradval : (1 + (c : ℂ) ^ 2) ^ 2 * (1 + 0) ^ 2 - 16 * (c : ℂ) ^ 2 * 0 =
      (1 + (c : ℂ) ^ 2) ^ 2 := by ring
  have hmem : (1 + (c : ℂ) ^ 2) ^ 2 * (1 + 0) ^ 2 - 16 * (c : ℂ) ^ 2 * 0 ∈ Complex.slitPlane := by
    rw [hradval, Complex.mem_slitPlane_iff]
    left
    rw [show ((1 + (c : ℂ) ^ 2) ^ 2) = (((1 + c ^ 2 : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.ofReal_re]
    positivity
  -- (3) the principal square root
  have hσ0 : HasDerivAt
      (fun z : ℂ => ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (((1 + (c : ℂ) ^ 2) ^ 2) ^ (1 / 2 - 1 : ℂ)) *
        (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2)) 0 := by
    have h := hrad.cpow_const (c := (1 / 2 : ℂ)) hmem
    rw [hradval] at h
    exact h
  have hkey : (((1 + (c : ℂ) ^ 2) ^ 2) ^ (1 / 2 - 1 : ℂ)) = (1 + (c : ℂ) ^ 2)⁻¹ := by
    rw [show ((1 + (c : ℂ) ^ 2) ^ 2) = (((1 + c ^ 2 : ℝ)) : ℂ) ^ 2 by push_cast; ring]
    rw [cpow_neg_half_sq_of_pos (1 + c ^ 2) hcp]
    push_cast
    ring
  have hσ : HasDerivAt
      (fun z : ℂ => ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 + (c : ℂ) ^ 2)⁻¹ * (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2)) 0 := by
    have hv : (1 / 2 : ℂ) * (((1 + (c : ℂ) ^ 2) ^ 2) ^ (1 / 2 - 1 : ℂ)) *
        (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2) =
        (1 / 2 : ℂ) * (1 + (c : ℂ) ^ 2)⁻¹ * (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2) := by
      rw [hkey]
    exact hσ0.congr_deriv hv
  -- (4) the numerator
  have hz : HasDerivAt (fun z : ℂ => z * (1 + (c : ℂ) ^ 2) - 1 - (c : ℂ) ^ 2)
      (1 + (c : ℂ) ^ 2) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).mul_const (1 + (c : ℂ) ^ 2)
    have h2 := h.sub_const 1
    have h3 := h2.sub_const ((c : ℂ) ^ 2)
    have hv : (1 * (1 + (c : ℂ) ^ 2) : ℂ) = 1 + (c : ℂ) ^ 2 := by ring
    exact h3.congr_deriv hv
  have hnum : HasDerivAt
      (fun z : ℂ => z * (1 + (c : ℂ) ^ 2) - 1 - (c : ℂ) ^ 2 +
        ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ))
      ((1 + (c : ℂ) ^ 2) + (1 / 2 : ℂ) * (1 + (c : ℂ) ^ 2)⁻¹ *
        (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2)) 0 := hz.add hσ
  -- (5) divide by the constant and identify with `lune c`
  have hCne : (2 * ((c : ℂ) ^ 2 - 1)) ≠ 0 := by
    have h1 : (c : ℂ) ^ 2 - 1 ≠ 0 := by
      intro h
      have h2 : c ^ 2 - 1 = 0 := by exact_mod_cast h
      nlinarith [hc]
    exact mul_ne_zero two_ne_zero h1
  have hlune0 : HasDerivAt
      (fun z : ℂ => (z * (1 + (c : ℂ) ^ 2) - 1 - (c : ℂ) ^ 2 +
        ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ)) /
        (2 * ((c : ℂ) ^ 2 - 1)))
      (((1 + (c : ℂ) ^ 2) + (1 / 2 : ℂ) * (1 + (c : ℂ) ^ 2)⁻¹ *
        (2 * (1 + (c : ℂ) ^ 2) ^ 2 - 16 * (c : ℂ) ^ 2)) / (2 * ((c : ℂ) ^ 2 - 1))) 0 :=
    hnum.div_const (2 * ((c : ℂ) ^ 2 - 1))
  have he : (fun z : ℂ => (z * (1 + (c : ℂ) ^ 2) - 1 - (c : ℂ) ^ 2 +
        ((1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) ^ 2 - 16 * (c : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ)) /
        (2 * ((c : ℂ) ^ 2 - 1))) = lune c := by
    funext z; rfl
  rw [he] at hlune0
  refine hlune0.congr_deriv ?_
  -- (6) final algebra
  have h1 : (c : ℂ) ^ 2 - 1 ≠ 0 := by
    intro h
    have h2 : c ^ 2 - 1 = 0 := by exact_mod_cast h
    nlinarith [hc]
  have h2 : (c : ℂ) ^ 2 + 1 ≠ 0 := by
    intro h
    have h3 : c ^ 2 + 1 = 0 := by exact_mod_cast h
    nlinarith [hc]
  have h3 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h4 : (1 : ℂ) + (c : ℂ) ^ 2 ≠ 0 := by
    intro h
    have h5 : (1 + c ^ 2 : ℝ) = 0 := by exact_mod_cast h
    nlinarith [hc]
  field_simp
  ring

end Work.ANum
