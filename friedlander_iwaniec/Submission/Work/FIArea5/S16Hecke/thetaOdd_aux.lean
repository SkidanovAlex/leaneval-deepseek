/-
# `Submission.Work.FIArea5.S16Hecke.thetaOdd_aux`

Elementary API for the theta transformation of the Grössencharacter theta series
`Work.FIArea5.S16Hecke.thetaOdd`: the bijection `ℤ[i] ≃ ℤ × ℤ`, the facts that `1 + i` is not a
unit modulo `4d` (so a character extended by zero off the units vanishes off the odd elements),
the coordinate form of `gnorm`, the periodicity of `chiOdd chi` modulo `4d`, and the
summability/decay facts for polynomially weighted Gaussians that feed
`Work.FIArea5.S16.poisson_periodic_2d`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16.holoGaussDefs
import Submission.Work.FIArea5.S16.deriv_shift_gaussian_isBigO
import Submission.Work.FIArea5.S16.cexp_quadratic_poly_isBigO
import Submission.Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The summand of `thetaOdd` -/

/-- The summand of `thetaOdd`: `χ(z)z^m e^{-πu|z|²}`, zero off the odd elements. -/
def thetaOddSummand (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ :=
  chiOdd chi z * ((z : ℂ) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)))

theorem thetaOdd_eq_tsum_summand (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaOdd chi m u = ∑' z : GaussianInt, thetaOddSummand chi m u z := by
  rw [thetaOdd]
  refine tsum_congr (fun z => ?_)
  unfold thetaOddSummand
  by_cases h : isOddG z
  · rw [chiOdd, if_pos h, if_pos h]; ring
  · rw [chiOdd, if_neg h, if_neg h]; ring

/-! ## The bijection `ℤ[i] ≃ ℤ × ℤ` -/

/-- The bijection sending `z` to `(z.re, z.im)`. -/
def gaussToProd : GaussianInt ≃ ℤ × ℤ where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem gaussToProd_apply (z : GaussianInt) : gaussToProd z = (z.re, z.im) := rfl
@[simp] theorem gaussToProd_symm_apply (p : ℤ × ℤ) : gaussToProd.symm p = ⟨p.1, p.2⟩ := rfl

/-- **`thetaOdd` as a sum over `ℤ²`.** -/
theorem thetaOdd_eq_tsum_Z2 (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaOdd chi m u = ∑' p : ℤ × ℤ, thetaOddSummand chi m u (gaussToProd.symm p) := by
  rw [thetaOdd_eq_tsum_summand]
  exact Equiv.tsum_eq gaussToProd
    (fun p : ℤ × ℤ => thetaOddSummand chi m u (gaussToProd.symm p))

/-- The `ℤ²`-form of the summand. -/
theorem thetaOddSummand_symm (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (p : ℤ × ℤ) :
    thetaOddSummand chi m u (gaussToProd.symm p)
      = chiOdd chi ⟨p.1, p.2⟩ * (((⟨p.1, p.2⟩ : GaussianInt) : ℂ) ^ m
          * Complex.exp (-Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ))) := rfl

/-! ## `1 + i` and the odd elements -/

theorem oneAddI_pow_four : oneAddI ^ 4 = -(4 : GaussianInt) := by decide

/-- `1 + i` divides `4d`. -/
theorem oneAddI_dvd_four_mul (d : ℕ) : oneAddI ∣ (((4 * d : ℕ)) : GaussianInt) := by
  have h4 : (((4 * d : ℕ)) : GaussianInt) = -(d : GaussianInt) * oneAddI ^ 4 := by
    rw [oneAddI_pow_four]; push_cast; ring
  exact ⟨-(d : GaussianInt) * oneAddI ^ 3, by rw [h4]; ring⟩

theorem oneAddI_not_isUnit : ¬ IsUnit oneAddI := by
  intro h
  have h1 : oneAddI.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr h
  have h2 : oneAddI.norm.natAbs = 2 := by decide
  omega

/-- A Gaussian integer divisible by `1 + i` is **not** a unit modulo `4d`. -/
theorem not_isUnitMod4d_of_oneAddI_dvd {d : ℕ} {z : GaussianInt} (h : oneAddI ∣ z) :
    ¬ IsUnitMod4d d z := by
  rintro ⟨w, hw⟩
  have h1 : oneAddI ∣ (z * w - 1) := dvd_trans (oneAddI_dvd_four_mul d) hw
  have h2 : oneAddI ∣ z * w := Dvd.dvd.mul_right h w
  have h3 : oneAddI ∣ (1 : GaussianInt) := by
    have := dvd_sub h2 h1
    rwa [sub_sub_cancel] at this
  exact oneAddI_not_isUnit (isUnit_iff_dvd_one.mpr h3)

/-- A character extended by zero off the unit group vanishes off the odd elements. -/
theorem chi_eq_zero_of_oneAddI_dvd {d : ℕ} (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) {z : GaussianInt} (h : oneAddI ∣ z) : chi z = 0 :=
  hchi.2 z (not_isUnitMod4d_of_oneAddI_dvd h)

theorem chiOdd_eq_zero_of_not_isOddG (chi : GaussianInt → ℂ) {z : GaussianInt}
    (h : ¬ isOddG z) : chiOdd chi z = 0 := by
  rw [chiOdd, if_neg h]

/-- The norm bound on `chiOdd`. -/
theorem norm_chiOdd_le_one (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi) (z : GaussianInt) : ‖chiOdd chi z‖ ≤ 1 := by
  by_cases h : isOddG z
  · rw [chiOdd, if_pos h]; exact hchi.2.2.1 z
  · rw [chiOdd, if_neg h]; simp

/-- `chiOdd chi` is periodic modulo `4d`. -/
theorem chiOdd_periodic (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi) :
    ∀ z w : GaussianInt, ((((4 * d : ℕ) : ℤ) : GaussianInt)) ∣ (z - w) →
      chiOdd chi z = chiOdd chi w := by
  intro z w hzw
  have hdvd : oneAddI ∣ ((((4 * d : ℕ) : ℤ) : GaussianInt)) := oneAddI_dvd_four_mul d
  have hiff : isOddG z ↔ isOddG w := by
    simp only [isOddG]
    constructor
    · intro hz hw
      refine hz ?_
      have h1 : oneAddI ∣ (z - w) := dvd_trans hdvd hzw
      have := dvd_add h1 hw
      rwa [sub_add_cancel] at this
    · intro hw hz
      refine hw ?_
      have h1 : oneAddI ∣ (z - w) := dvd_trans hdvd hzw
      have h2 : oneAddI ∣ (w - z) := by simpa [neg_sub] using (dvd_neg.mpr h1)
      have := dvd_add h2 hz
      rwa [sub_add_cancel] at this
  by_cases hz : isOddG z
  · have hw : isOddG w := hiff.mp hz
    rw [chiOdd, if_pos hz, chiOdd, if_pos hw]
    exact hchi.2.2.2.1 z w hzw
  · have hw : ¬ isOddG w := fun h => hz (hiff.mpr h)
    rw [chiOdd, if_neg hz, chiOdd, if_neg hw]

/-! ## Coordinates of `gnorm` -/

/-- `gnorm` in coordinates: `|z|² = re² + im²`. -/
theorem gnorm_cast_real (z : GaussianInt) :
    ((gnorm z : ℕ) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [gnorm, ← Int.cast_natCast,
    Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z), Zsqrtd.norm_def]
  push_cast
  ring

/-! ## Norms of the Poisson phases -/

theorem norm_exp_two_pi_I_mul_div (a : ℤ) (q : ℕ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / (q : ℂ)))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * ((a : ℂ) / (q : ℂ))
      = (((2 * Real.pi * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The Gauss sum is bounded by the group order `16 d²`. -/
theorem norm_gaussSum_le (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi) (ξ : GaussianInt) :
    ‖gaussSum d chi ξ‖ ≤ ((4 * d : ℕ) : ℝ) ^ 2 := by
  rw [gaussSum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ α ∈ (Finset.range (4 * d)).product (Finset.range (4 * d)),
      ‖(if isOddG (⟨α.1, α.2⟩ : GaussianInt) then
        chi (⟨α.1, α.2⟩ : GaussianInt) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((α.1 * ξ.re + α.2 * ξ.im : ℤ)) : ℂ) / ((4 * d : ℕ) : ℂ)))
       else 0)‖ ≤ 1 := by
    intro α _
    by_cases h : isOddG (⟨α.1, α.2⟩ : GaussianInt)
    · rw [if_pos h, norm_mul, norm_exp_two_pi_I_mul_div (α.1 * ξ.re + α.2 * ξ.im) (4 * d)]
      exact mul_le_one₀ (hchi.2.2.1 _) zero_le_one le_rfl
    · rw [if_neg h]; simp
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  simp [Finset.card_product, Finset.card_range]
  ring

/-! ## Polynomial weights times Gaussians -/

private theorem abs_le_one_add_sq_add_sq (x y : ℝ) : |x| ≤ 1 + x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x, abs_nonneg x, sq_nonneg y]

theorem norm_exp_neg_pi_mul_sq (u : ℝ) (x : ℤ) :
    ‖Complex.exp (-Real.pi * u * ((x : ℂ) ^ 2))‖ = Real.exp (-(Real.pi * u) * (x : ℝ) ^ 2) := by
  have h : -Real.pi * u * ((x : ℂ) ^ 2) = ((-(Real.pi * u) * (x : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp, Complex.ofReal_re]

theorem norm_kernel_factor (u : ℝ) (a : ℕ) (x : ℤ) :
    ‖((x : ℂ) ^ a) * Complex.exp (-Real.pi * u * ((x : ℂ) ^ 2))‖ =
      |(x : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (x : ℝ) ^ 2) := by
  rw [norm_mul, norm_exp_neg_pi_mul_sq, Complex.norm_pow, Complex.norm_intCast]

/-- Summability of `χ(z)·z₁^a z₂^b e^{-πu|z|²}` over `ℤ²`. -/
theorem summable_chiOdd_poly_gauss (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi) {u : ℝ} (hu : 0 < u) (a b : ℕ) :
    Summable (fun p : ℤ × ℤ => chiOdd chi ⟨p.1, p.2⟩ *
      ((((p.1 : ℂ) ^ a) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
        * (((p.2 : ℂ) ^ b) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))) := by
  have hc : 0 < Real.pi * u := mul_pos Real.pi_pos hu
  have hdom := Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add hc 0 (a + b)
  refine Summable.of_norm_bounded hdom (fun p => ?_)
  have h1 : ‖chiOdd chi ⟨p.1, p.2⟩‖ ≤ 1 := norm_chiOdd_le_one d chi hchi _
  have hn : ‖chiOdd chi ⟨p.1, p.2⟩ *
      ((((p.1 : ℂ) ^ a) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
        * (((p.2 : ℂ) ^ b) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))‖
      = ‖chiOdd chi ⟨p.1, p.2⟩‖ * ((|(p.1 : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2))
          * (|(p.2 : ℝ)| ^ b * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2))) := by
    rw [norm_mul, norm_mul, norm_kernel_factor, norm_kernel_factor]
  rw [hn]
  set K : ℝ := 1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hb1 : |(p.1 : ℝ)| ≤ K := by
    rw [hK]; exact abs_le_one_add_sq_add_sq _ _
  have hb2 : |(p.2 : ℝ)| ≤ K := by
    rw [hK]
    calc |(p.2 : ℝ)| ≤ 1 + (p.2 : ℝ) ^ 2 + (p.1 : ℝ) ^ 2 := abs_le_one_add_sq_add_sq _ _
      _ = 1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by ring
  have hprod : |(p.1 : ℝ)| ^ a * |(p.2 : ℝ)| ^ b ≤ K ^ (a + b) := by
    calc |(p.1 : ℝ)| ^ a * |(p.2 : ℝ)| ^ b ≤ K ^ a * K ^ b :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb1 a)
            (pow_le_pow_left₀ (abs_nonneg _) hb2 b) (by positivity) (by positivity)
      _ = K ^ (a + b) := (pow_add K a b).symm
  have hexp : Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2)
      = Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hsplit : ‖chiOdd chi ⟨p.1, p.2⟩‖ * ((|(p.1 : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2))
        * (|(p.2 : ℝ)| ^ b * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2)))
      = ‖chiOdd chi ⟨p.1, p.2⟩‖ * (|(p.1 : ℝ)| ^ a * |(p.2 : ℝ)| ^ b)
        * (Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2)) := by
    ring
  rw [hsplit, hexp]
  calc ‖chiOdd chi ⟨p.1, p.2⟩‖ * (|(p.1 : ℝ)| ^ a * |(p.2 : ℝ)| ^ b)
        * Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
      ≤ 1 * K ^ (a + b) * Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) :=
        mul_le_mul (mul_le_mul h1 hprod (by positivity) (by norm_num)) (le_refl _)
          (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
          + 0 * (|(p.1 : ℝ)| + |(p.2 : ℝ)|))
        * (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (a + b) := by
        rw [hK, zero_mul, add_zero]; ring

/-- Joint summability of a product of two summable sequences over `ℤ²`. -/
theorem summable_prod_mul {A B : ℤ → ℂ} (hA : Summable A) (hB : Summable B) :
    Summable (fun p : ℤ × ℤ => A p.1 * B p.2) := by
  refine Summable.of_norm ?_
  refine (Summable.mul_of_nonneg hA.norm hB.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)).congr (fun p => ?_)
  rw [norm_mul]

/-! ## The polynomially weighted Gaussian and its Fourier transform -/

/-- The kernel `x ↦ x^k e^{-π u x²}` is continuous. -/
theorem continuous_kernel (u : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ => ((x : ℂ) ^ k) * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)) := by
  fun_prop

/-- The kernel `x ↦ x^k e^{-π u x²}` decays faster than any power of `|x|`. -/
theorem kernel_isBigO (u : ℝ) (hu : 0 < u) (k : ℕ) {b : ℝ} :
    (fun x : ℝ => ((x : ℂ) ^ k) * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
  refine (Work.FIArea5.S16.cexp_quadratic_poly_isBigO (A := (u : ℂ)) (by simpa using hu)
    (0 : ℂ) k (B := b)).congr_left (fun x => ?_)
  simp

/-- The `k`-th derivative of the frequency-side Gaussian. -/
theorem iteratedDeriv_gaussW_eq (u : ℝ) (k : ℕ) :
    (fun ξ : ℝ => iteratedDeriv k (Work.FIArea5.S16.gaussW u) (ξ : ℂ))
      = fun ξ : ℝ => iteratedDeriv k (fun w : ℂ => 1 / (u : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp (-Real.pi / (u : ℂ) * (w + Complex.I * (0 : ℂ)) ^ 2)) (ξ : ℂ) := by
  funext ξ
  congr 1
  funext w
  simp only [Work.FIArea5.S16.gaussW]
  norm_num

/-- The Fourier transform of the kernel `x ↦ x^k e^{-π u x²}` decays faster than any power. -/
theorem fourier_kernel_isBigO (u : ℝ) (hu : 0 < u) (k : ℕ) {b : ℝ} :
    (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ k) *
        Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
  have h := Work.FIArea5.S16.deriv_shift_gaussian_isBigO (A := (u : ℂ)) (by simpa using hu)
    (0 : ℂ) k (B := b)
  have h' : (fun ξ : ℝ => iteratedDeriv k (Work.FIArea5.S16.gaussW u) (ξ : ℂ))
      =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) :=
    h.congr_left (fun ξ => (congrFun (iteratedDeriv_gaussW_eq u k) ξ).symm)
  refine (h'.const_mul_left ((Complex.I / (2 * Real.pi)) ^ k)).congr_left (fun ξ => ?_)
  exact (Work.FIArea5.S16.fourier_gaussian_poly_u hu k ξ).symm

/-- The frequency-side kernel is summable along the lattice `ℤ/q`. -/
theorem fourier_kernel_summable (u : ℝ) (hu : 0 < u) (k : ℕ) {q : ℝ} (hq : 0 < q) :
    Summable (fun n : ℤ => (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ k) *
        Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((n : ℝ) / q)) :=
  Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (by norm_num : (1 : ℝ) < 2)
    (fourier_kernel_isBigO u hu k (b := 2)) hq

/-- The frequency-side summand of the theta transformation is summable. -/
theorem summable_gaussSum_fourier_kernel (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi) {u q : ℝ} (hu : 0 < u) (hq : 0 < q) (a b : ℕ) :
    Summable (fun ξ : ℤ × ℤ => gaussSum d chi ⟨ξ.1, ξ.2⟩ *
      ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) *
            Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / q)
        * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
            Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / q))) := by
  set A : ℤ → ℂ := fun n => (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) *
      Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((n : ℝ) / q) with hAdef
  set B : ℤ → ℂ := fun n => (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
      Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((n : ℝ) / q) with hBdef
  have hD : Summable (fun ξ : ℤ × ℤ => ‖A ξ.1‖ * ‖B ξ.2‖) :=
    Summable.mul_of_nonneg (fourier_kernel_summable u hu a hq).norm
      (fourier_kernel_summable u hu b hq).norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine Summable.of_norm_bounded (hD.mul_left (((4 * d : ℕ) : ℝ) ^ 2)) (fun ξ => ?_)
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_gaussSum_le d chi hchi _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))


/-! ## The star of the summand and the dual (frequency) summand -/

theorem star_chiOdd (d : ℕ) (chi : GaussianInt → ℂ) (hchi : IsCharMod4dStrict d chi)
    (z : GaussianInt) : star (chiOdd chi z) = star (chi z) := by
  by_cases h : isOddG z
  · rw [chiOdd, if_pos h]
  · rw [chiOdd, if_neg h]
    have hz : oneAddI ∣ z := by
      by_contra hz'
      exact h hz'
    rw [chi_eq_zero_of_oneAddI_dvd chi hchi hz]

theorem star_gaussToProd_symm (p : ℤ × ℤ) :
    star (((gaussToProd.symm p : GaussianInt)) : ℂ) = (p.1 : ℂ) - Complex.I * (p.2 : ℂ) := by
  rw [gaussToProd_symm_apply, Complex.star_def, ← GaussianInt.toComplex_star, Zsqrtd.star_mk]
  simp only [GaussianInt.toComplex_def]
  push_cast
  ring

theorem star_exp_neg_pi (u : ℝ) (n : ℕ) :
    star (Complex.exp (-Real.pi * u * (n : ℝ))) = Complex.exp (-Real.pi * u * (n : ℝ)) := by
  have h : Complex.exp (-Real.pi * u * (n : ℝ))
      = (((Real.exp (-(Real.pi * u * (n : ℝ)))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h, Complex.star_def, Complex.conj_ofReal]

/-- The summand of `star (thetaOdd chi m u)` in the `ℤ²`-coordinates. -/
def thetaOddStarSummand (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (p : ℤ × ℤ) : ℂ :=
  star (chi ⟨p.1, p.2⟩) *
    (((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) ^ m
      * Complex.exp (-Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ)))

theorem star_thetaOddSummand (d : ℕ) (chi : GaussianInt → ℂ) (hchi : IsCharMod4dStrict d chi)
    (m : ℕ) (u : ℝ) (z : GaussianInt) :
    star (thetaOddSummand chi m u z)
      = star (chi z) * ((star ((z : ℂ)) ^ m) * Complex.exp (-Real.pi * u * (gnorm z : ℝ))) := by
  rw [thetaOddSummand, star_mul, star_mul, star_chiOdd d chi hchi, star_pow,
    star_exp_neg_pi u (gnorm z)]
  ring

/-- **`star (thetaOdd)` in the dual coordinates.** -/
theorem star_thetaOdd_eq (d : ℕ) (chi : GaussianInt → ℂ) (hchi : IsCharMod4dStrict d chi)
    (m : ℕ) (u : ℝ) :
    star (thetaOdd chi m u) = ∑' p : ℤ × ℤ, thetaOddStarSummand chi m u p := by
  rw [thetaOdd_eq_tsum_Z2, tsum_star]
  refine tsum_congr (fun p => ?_)
  rw [star_thetaOddSummand d chi hchi, star_gaussToProd_symm]
  rfl

/-! ## Cast arithmetic for the modulus `4d` -/

theorem four_d_sq_cast (d : ℕ) :
    ((((4 * d : ℕ) : ℂ))) ^ 2 = ((16 * (d : ℝ) ^ 2 : ℝ) : ℂ) := by
  push_cast
  ring

theorem inv_u_mul_four_d_sq (d : ℕ) (u : ℝ) :
    1 / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2) = ((1 / (16 * (d : ℝ) ^ 2 * u) : ℝ) : ℂ) := by
  have hX : (u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2 = ((16 * (d : ℝ) ^ 2 * u : ℝ) : ℂ) := by
    rw [four_d_sq_cast]; push_cast; ring
  rw [hX]
  push_cast
  rfl

end

end Work.FIArea5.S16Hecke
