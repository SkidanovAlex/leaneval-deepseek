import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Cauchy/Lorentzian Fourier transform pair

This file develops the classical identity

`∫ x, exp (-a x i) / (β² + x²) dx = (π/β) exp (-β |a|)`

for `β > 0`, by computing the Fourier transform of the two-sided exponential and
applying Mathlib's Fourier inversion theorem.

The identity is the analytic heart of the Mellin–Plancherel computation for the truncated
Dirichlet series `dirSum` (`Work.BMF.dirSum`).
-/

open Complex MeasureTheory Real
open scoped FourierTransform

set_option maxHeartbeats 2000000

namespace Work.BMF

/-- Real arithmetic behind the sum of the two one-sided exponential integrals. -/
theorem arith_key (β w : ℝ) (hβ : 0 < β) :
    (1:ℂ)/((↑(2*Real.pi*β) : ℂ) + (↑(-2*Real.pi*w) : ℂ) * Complex.I)
      + (-1)/((↑(-2*Real.pi*β) : ℂ) + (↑(-2*Real.pi*w) : ℂ) * Complex.I)
      = ((β / (Real.pi * (β^2 + w^2)) : ℝ) : ℂ) := by
  set Z : ℂ := (β:ℂ) + (w:ℂ)*Complex.I with hZ
  have hZre : Z.re = β := by rw [hZ]; simp
  have hZne : Z ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hZre] at this; simp at this; linarith
  have hZc : starRingEnd ℂ Z = (β:ℂ) - (w:ℂ)*Complex.I := by
    rw [hZ, map_add, map_mul]; simp [Complex.conj_I]; ring
  have hkey : (1:ℂ)/Z + 1/(starRingEnd ℂ Z) = ((2*β/(β^2+w^2) : ℝ) : ℂ) := by
    have hZcne : starRingEnd ℂ Z ≠ 0 := by
      rw [hZc]; intro h; have := congrArg Complex.re h; simp at this; linarith
    have hh1 : Z + starRingEnd ℂ Z = ((2*β : ℝ) : ℂ) := by rw [hZc, hZ]; push_cast; ring
    have hns : Complex.normSq Z = β^2 + w^2 := by rw [hZ, Complex.normSq_apply]; simp; ring
    have hnorm : Z * starRingEnd ℂ Z = ((β^2 + w^2 : ℝ) : ℂ) := by rw [Complex.mul_conj, hns]
    rw [div_add_div _ _ hZne hZcne]
    rw [show 1 * starRingEnd ℂ Z + Z * 1 = Z + starRingEnd ℂ Z by ring]
    rw [hh1, hnorm]
    norm_num
  have hA : (↑(-2*Real.pi*β) : ℂ) + (↑(-2*Real.pi*w) : ℂ) * Complex.I = -(2*Real.pi:ℂ) * Z := by
    rw [hZ]; push_cast; ring
  have hB : (↑(2*Real.pi*β) : ℂ) + (↑(-2*Real.pi*w) : ℂ) * Complex.I
      = (2*Real.pi:ℂ) * (starRingEnd ℂ Z) := by
    rw [hZc]; push_cast; ring
  rw [hA, hB, neg_mul]
  rw [show (1:ℂ)/((2*Real.pi:ℂ) * (starRingEnd ℂ Z))
        = (1/(2*Real.pi:ℂ)) * (1/(starRingEnd ℂ Z)) by rw [one_div, one_div, mul_inv]; ring]
  rw [show (-1:ℂ)/(-((2*Real.pi:ℂ) * Z)) = (1/(2*Real.pi:ℂ)) * (1/Z) by
        rw [neg_div_neg_eq, one_div, one_div, mul_inv]; ring]
  rw [← mul_add, add_comm ((1:ℂ)/(starRingEnd ℂ Z)) ((1:ℂ)/Z), hkey]
  rw [show (1:ℂ)/(2*Real.pi:ℂ) = ((1/(2*Real.pi) : ℝ) : ℂ) by
        norm_num [Complex.ofReal_div, Complex.ofReal_mul]]
  rw [← Complex.ofReal_mul]
  congr 1
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : β^2 + w^2 ≠ 0 := by positivity
  field_simp

/-- `x ↦ exp (-c |x|)` is integrable for `c > 0`. -/
theorem integrable_exp_neg_mul_abs (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * |x|))) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun
      (fun x hx => by rw [abs_of_pos (Set.mem_Ioi.mp hx)]; ring_nf) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun
      (fun x hx => by rw [abs_of_nonpos (Set.mem_Iic.mp hx), show -(c * -x) = c * x by ring])
      measurableSet_Iic
  have h3 := h1.union h2
  rwa [Set.Ioi_union_Iic, integrableOn_univ] at h3

/-- The Fourier transform of the two-sided exponential. -/
theorem fourier_two_sided_exp (β w : ℝ) (hβ : 0 < β) :
    (∫ v : ℝ, Complex.exp ((↑(-2*Real.pi*v*w) : ℂ) * Complex.I)
        * (((Real.exp (-(2*Real.pi*β*|v|)) : ℝ)) : ℂ))
      = ((β / (Real.pi * (β^2 + w^2)) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp (((↑(-2*Real.pi*v*w) : ℂ) * Complex.I)
    + ((↑(-(2*Real.pi*β*|v|))) : ℂ)) with hF
  have hpt : (fun v : ℝ => Complex.exp ((↑(-2*Real.pi*v*w) : ℂ) * Complex.I)
      * (((Real.exp (-(2*Real.pi*β*|v|)) : ℝ)) : ℂ)) = F := by
    funext v
    simp only [hF, Complex.ofReal_exp, ← Complex.exp_add]
  rw [hpt]
  set A : ℂ := ↑(-2*Real.pi*β) + ↑(-2*Real.pi*w) * Complex.I with hA
  set B : ℂ := ↑(2*Real.pi*β) + ↑(-2*Real.pi*w) * Complex.I with hB
  have hAre : A.re < 0 := by rw [hA]; simp; positivity
  have hBre : 0 < B.re := by rw [hB]; simp; positivity
  have hio_eq : Set.EqOn F (fun v : ℝ => Complex.exp (A * (v:ℂ))) (Set.Ioi 0) := by
    intro v hv
    simp only [hF]
    congr 1
    rw [hA, abs_of_pos (Set.mem_Ioi.mp hv)]
    push_cast
    ring
  have hic_eq : Set.EqOn F (fun v : ℝ => Complex.exp (B * (v:ℂ))) (Set.Iic 0) := by
    intro v hv
    simp only [hF]
    congr 1
    rw [hB, abs_of_nonpos (Set.mem_Iic.mp hv)]
    push_cast
    ring
  have hint_io : IntegrableOn F (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hAre 0).congr_fun hio_eq.symm measurableSet_Ioi
  have hint_ic : IntegrableOn F (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hBre 0).congr_fun hic_eq.symm measurableSet_Iic
  have hio : (∫ v in Set.Ioi (0:ℝ), F v) = -1/A := by
    rw [setIntegral_congr_fun measurableSet_Ioi hio_eq, integral_exp_mul_complex_Ioi hAre 0]
    simp
  have hic : (∫ v in Set.Iic (0:ℝ), F v) = 1/B := by
    rw [setIntegral_congr_fun measurableSet_Iic hic_eq, integral_exp_mul_complex_Iic hBre 0]
    simp
  have hsplit : (∫ v : ℝ, F v) = (∫ v in Set.Iic (0:ℝ), F v) + (∫ v in Set.Ioi (0:ℝ), F v) := by
    rw [← setIntegral_univ (f := F), ← Set.Iic_union_Ioi (a := (0:ℝ)),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint_ic hint_io]
  rw [hsplit]
  rw [hic, hio]
  rw [hA, hB]
  exact arith_key β w hβ

/-- The classical Cauchy (Lorentzian) Fourier transform:
`∫ x, exp (-a x i) / (β² + x²) dx = (π/β) exp (-β |a|)` for `β > 0`. -/
theorem cauchy_fourier_integral (β a : ℝ) (hβ : 0 < β) :
    (∫ x : ℝ, Complex.exp (-(a * x) * Complex.I) * (((β ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ))
      = ((Real.pi / β) * Real.exp (-(β * |a|)) : ℂ) := by
  set ψ : ℝ → ℂ := fun x => ((Real.exp (-(2 * Real.pi * β * |x|)) : ℝ) : ℂ) with hψ
  set φ : ℝ → ℂ := fun x => ((Real.pi / β : ℝ) : ℂ) * ψ x with hφ
  set g : ℝ → ℂ := fun w => (((β ^ 2 + w ^ 2)⁻¹ : ℝ) : ℂ) with hg
  have hIntψ : Integrable ψ := by
    rw [hψ]
    refine Integrable.mono' (g := fun x : ℝ => Real.exp (-(2 * Real.pi * β * |x|)))
      (integrable_exp_neg_mul_abs (2 * Real.pi * β) (by positivity)) ?_ ?_
    · fun_prop
    · filter_upwards with x
      exact le_of_eq ((RCLike.norm_ofReal (Real.exp (-(2 * Real.pi * β * |x|)))).trans
        (abs_of_nonneg (Real.exp_nonneg _)))
  have hIntφ : Integrable φ := by
    rw [hφ]
    exact hIntψ.const_mul _
  have hIntg : Integrable g := by
    rw [hg]
    refine Integrable.mono' (g := fun w : ℝ => (1/β^2) * (1 + ((1/β) * w)^2)⁻¹)
      ((integrable_inv_one_add_mul_sq (b := 1/β) (by positivity)).const_mul _) ?_ ?_
    · fun_prop
    · filter_upwards with w
      have h1 : ‖(((β^2 + w^2)⁻¹ : ℝ) : ℂ)‖ = (β^2 + w^2)⁻¹ :=
        (RCLike.norm_ofReal ((β^2+w^2)⁻¹)).trans (abs_of_nonneg (by positivity))
      rw [h1]
      rw [show (β^2 + w^2)⁻¹ = (1/β^2) * (1 + ((1/β)*w)^2)⁻¹ by
            have h1 : β ≠ 0 := hβ.ne'
            field_simp]
  have hFourier : 𝓕 φ = g := by
    funext w
    rw [fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul, hφ, hψ, hg]
    rw [show (∫ v : ℝ, Complex.exp ((↑(-2*Real.pi*v*w) : ℂ) * Complex.I)
              * (((Real.pi/β : ℝ) : ℂ) * ↑(Real.exp (-(2*Real.pi*β*|v|)))))
          = ((Real.pi/β : ℝ) : ℂ) * ∫ v : ℝ, Complex.exp ((↑(-2*Real.pi*v*w) : ℂ) * Complex.I)
              * ↑(Real.exp (-(2*Real.pi*β*|v|))) by
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
        ring]
    rw [fourier_two_sided_exp β w hβ]
    rw [← Complex.ofReal_mul]
    congr 1
    have h1 : β ≠ 0 := hβ.ne'
    have h2 : Real.pi ≠ 0 := Real.pi_ne_zero
    have h3 : β^2 + w^2 ≠ 0 := by positivity
    field_simp
  have hInv : 𝓕⁻ g = φ := by
    rw [← hFourier]
    exact Continuous.fourierInv_fourier_eq (by rw [hφ, hψ]; fun_prop) hIntφ
      (by rw [hFourier]; exact hIntg)
  have hphi_val : φ (-a/(2*Real.pi)) = ((Real.pi/β) * Real.exp (-(β*|a|)) : ℂ) := by
    change ((((Real.pi/β : ℝ) : ℂ) * ↑(Real.exp (-(2*Real.pi*β*|-a/(2*Real.pi)|)))))
        = ((Real.pi/β) * Real.exp (-(β*|a|)) : ℂ)
    rw [show (2*Real.pi*β*|-a/(2*Real.pi)|) = β*|a| by
          rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
          field_simp]
    rw [show (((Real.pi/β : ℝ) : ℂ)) = (Real.pi : ℂ)/(β : ℂ) by rw [Complex.ofReal_div]]
  have hInv_val : 𝓕⁻ g (-a/(2*Real.pi)) = ((Real.pi/β) * Real.exp (-(β*|a|)) : ℂ) := by
    rw [congrFun hInv (-a/(2*Real.pi)), hphi_val]
  rw [show (∫ x : ℝ, Complex.exp (-(a * x) * Complex.I) * (((β ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ))
        = 𝓕⁻ g (-a/(2*Real.pi)) by
      rw [fourierInv_eq']
      refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
      simp only [smul_eq_mul, hg]
      rw [show Complex.exp (-(↑a * ↑v) * Complex.I)
            = Complex.exp ((↑(2*Real.pi*inner ℝ v (-a/(2*Real.pi))) : ℂ) * Complex.I) by
            congr 1
            congr 1
            rw [show inner ℝ v (-a/(2*Real.pi)) = (-a/(2*Real.pi))*v by simp]
            rw [show (2*Real.pi*((-a/(2*Real.pi))*v)) = -a*v by field_simp]
            push_cast
            ring]]
  exact hInv_val

/-- The single-summand evaluation: integrating `Re (C exp (-i L τ))` against the
Cauchy kernel `(β² + τ²)⁻¹`. -/
theorem integral_exp_mul_cauchy (β L : ℝ) (hβ : 0 < β) (C : ℂ) :
    (∫ τ : ℝ, (C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)).re
        * (((β^2 + τ^2)⁻¹ : ℝ)))
      = C.re * ((Real.pi/β) * Real.exp (-(β * |L|))) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hIntK : Integrable (fun τ : ℝ => (((β^2 + τ^2)⁻¹ : ℝ))) := by
    have h := (integrable_inv_one_add_mul_sq (b := 1/β) (by positivity)).const_mul (1/β^2)
    refine h.congr (Filter.Eventually.of_forall (fun τ => ?_))
    field_simp
  have hint : Integrable (fun τ : ℝ => C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
      * (((β^2 + τ^2)⁻¹ : ℝ) : ℂ)) := by
    refine Integrable.mono' (hIntK.const_mul ‖C‖) ?_ ?_
    · fun_prop
    · filter_upwards with τ
      have hK : ‖(((β^2 + τ^2)⁻¹ : ℝ) : ℂ)‖ = (β^2 + τ^2)⁻¹ :=
        (RCLike.norm_ofReal ((β^2+τ^2)⁻¹)).trans (abs_of_nonneg (by positivity))
      rw [norm_mul, norm_mul, Complex.norm_exp, hK]
      simp
  have h1 : (∫ τ : ℝ, (C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)).re
        * (((β^2 + τ^2)⁻¹ : ℝ)))
      = (∫ τ : ℝ, C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
          * (((β^2 + τ^2)⁻¹ : ℝ) : ℂ)).re := by
    rw [show (∫ τ : ℝ, (C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)).re
          * (((β^2 + τ^2)⁻¹ : ℝ)))
        = ∫ τ : ℝ, (C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
          * ((((β^2 + τ^2)⁻¹ : ℝ)) : ℂ)).re by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]]
    exact integral_re hint
  rw [h1]
  have h2 : (∫ τ : ℝ, C * Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
          * (((β^2 + τ^2)⁻¹ : ℝ) : ℂ))
      = C * (∫ τ : ℝ, Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
          * (((β^2 + τ^2)⁻¹ : ℝ) : ℂ)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun τ => ?_))
    ring
  rw [h2]
  have h3 : (∫ τ : ℝ, Complex.exp ((((-(L)) * τ : ℝ) : ℂ) * Complex.I)
        * (((β^2 + τ^2)⁻¹ : ℝ) : ℂ))
      = ((Real.pi / β) * Real.exp (-(β * |L|)) : ℂ) := by
    rw [← cauchy_fourier_integral β L hβ]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    rw [show ((-(↑L)) * ↑x) * Complex.I = (-(↑L * ↑x)) * Complex.I by ring]
  rw [h3]
  have hrw : (C * ((Real.pi / β) * Real.exp (-(β * |L|)) : ℂ)).re
      = C.re * ((Real.pi / β) * Real.exp (-(β * |L|))) := by
    rw [show ((Real.pi / β) * Real.exp (-(β * |L|)) : ℂ)
          = (((Real.pi / β) * Real.exp (-(β * |L|)) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hrw]

end Work.BMF
