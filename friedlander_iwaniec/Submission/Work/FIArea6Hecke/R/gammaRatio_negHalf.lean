import Mathlib

namespace Work.FIArea6Hecke.R

open Complex

/-- Conjugation identity for the complex Gamma function, phrased with `star` so it can be
used as a rewriting rule. -/
private theorem Gamma_star_rewrite (w : ℂ) :
    Complex.Gamma (star w) = star (Complex.Gamma w) := Complex.Gamma_conj w

/-- Norm is invariant under `star`, phrased with `star` so it can be used as a rewriting rule. -/
private theorem norm_star_rewrite (w : ℂ) : ‖star w‖ = ‖w‖ := Complex.norm_conj w

theorem gammaRatio_negHalf (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - (t : ℂ) * Complex.I) /
      Complex.Gamma ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ = 1 / 4 + t ^ 2 := by
  have hGs : ∀ w : ℂ, Complex.Gamma (star w) = star (Complex.Gamma w) :=
    Gamma_star_rewrite
  have hNs : ∀ w : ℂ, ‖star w‖ = ‖w‖ := norm_star_rewrite
  -- Work with the point `z = 1/2 + i t` on the critical line.
  set z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hz_ne : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.zero_re, hzre] at this
    norm_num at this
  have hz1_ne : z - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, hzre] at this
    norm_num at this
  have hstar_ne : star z ≠ 0 := by
    rwa [star_ne_zero]
  have hGz_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hzre]; norm_num)
  -- `3/2 - i t = star z + 1` and `-1/2 + i t = z - 1`.
  have hz1 : (3 / 2 : ℂ) - (t : ℂ) * Complex.I = star z + 1 := by
    rw [hz]; simp [Complex.conj_ofReal, Complex.conj_I]; ring
  have hz0 : (-1 / 2 : ℂ) + (t : ℂ) * Complex.I = z - 1 := by
    rw [hz]; ring
  -- Functional equation in the numerator: `Γ(star z + 1) = star z · Γ(star z) = star z · star (Γ z)`.
  have hnum : Complex.Gamma ((3 / 2 : ℂ) - (t : ℂ) * Complex.I)
      = star z * star (Complex.Gamma z) := by
    rw [hz1, Complex.Gamma_add_one _ hstar_ne, hGs]
  -- Functional equation in the denominator: `Γ z = (z - 1) · Γ (z - 1)`.
  have hden_eq : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
    conv_lhs => rw [show z = (z - 1) + 1 by ring]
    rw [Complex.Gamma_add_one _ hz1_ne]
  have hden : Complex.Gamma ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = Complex.Gamma z / (z - 1) := by
    rw [hz0, hden_eq, mul_div_cancel_left₀ _ hz1_ne]
  -- The whole ratio.
  have hratio : Complex.Gamma ((3 / 2 : ℂ) - (t : ℂ) * Complex.I)
        / Complex.Gamma ((-1 / 2 : ℂ) + (t : ℂ) * Complex.I)
      = (z - 1) * star z * (star (Complex.Gamma z) / Complex.Gamma z) := by
    rw [hnum, hden, div_div_eq_mul_div]
    ring
  rw [hratio]
  -- The Gamma factors cancel in modulus, leaving `‖z - 1‖ * ‖z‖`.
  rw [norm_mul, norm_mul, norm_div, hNs, hNs,
      div_self (norm_ne_zero_iff.mpr hGz_ne), mul_one]
  have h1 : ‖z‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hz, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have h2 : ‖z - 1‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hz, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [mul_comm, ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg (z - 1)),
    h1, h2]
  rw [Real.mul_self_sqrt (by positivity)]

end Work.FIArea6Hecke.R
