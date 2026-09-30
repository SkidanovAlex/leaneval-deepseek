import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology Real
open Complex hiding exp

/-!
# Fourier (cosine) value of the Cauchy density on the positive half-line

`∫_0^∞ cos(a·x)/(1+x²) dx = (π/2)·e^{−|a|}` for every real `a`, as a Lebesgue integral.

Proof (classical; inlined from `Submission/CosValue.lean` and
`Submission/ChildFubini.lean`):

  1. For `s > 0` the full-line Gaussian cosine integral is
     `∫_ℝ cos(a·x)·e^{−s·x²} dx = √(π/s)·e^{−a²/(4s)}` (`gaussian_cos_univ`),
     hence the half-line version is half of it (`gaussian_cos_Ioi`).
  2. Fubini over `(0,∞) × (0,∞)` using `1/(1+x²) = ∫_0^∞ e^{−(1+x²)t} dt`
     gives (`fubini_cauchy`):
     `∫_{x>0} cos(a·x)/(1+x²) dx = (1/2)·∫_{t>0} √(π/t)·e^{−t}·e^{−a²/(4t)} dt`.
  3. The one-dimensional integral is `π·e^{−|a|}` (`exp_eval`), via `t = u²`,
     the substitution `w = u − c/u` and the classical `∫_0^∞ e^{−w²} dw = √π`.
  4. Combine 2 and 3.
-/

namespace Commons.Analysis.Fourier

lemma gaussian_cos_univ (a s : ℝ) (hs : 0 < s) :
    ∫ x : ℝ, Real.cos (a * x) * Real.exp (-(s * x ^ 2)) =
      Real.sqrt (Real.pi / s) * Real.exp (-(a ^ 2 / (4 * s))) := by
  let G : ℝ → ℂ := fun x => cexp (I * (a : ℂ) * (x : ℂ)) * cexp (-(s : ℂ) * (x : ℂ) ^ 2)
  have hb : 0 < ((s : ℂ)).re := by simpa using hs
  have harg (x : ℝ) : I * (a : ℂ) * (x : ℂ) = I * ((a * x : ℝ) : ℂ) := by
    rw [mul_assoc]
    rw [← Complex.ofReal_mul]
  have hnorm (x : ℝ) : ‖G x‖ = ‖cexp (-(s : ℂ) * (x : ℂ) ^ 2)‖ := by
    unfold G
    rw [harg x]
    rw [norm_mul]
    rw [norm_exp_I_mul_ofReal]
    rw [one_mul]
  have hbd : Integrable (fun x : ℝ => ‖cexp (-(s : ℂ) * (x : ℂ) ^ 2)‖) :=
    (integrable_cexp_neg_mul_sq hb).norm
  have hGmeas : AEStronglyMeasurable G := by
    fun_prop
  have hGint : Integrable G := by
    refine Integrable.mono' (g := fun x : ℝ => ‖cexp (-(s : ℂ) * (x : ℂ) ^ 2)‖) hbd hGmeas ?_
    filter_upwards with x
    rw [hnorm x]
  have hre_fun (x : ℝ) : (G x).re = Real.cos (a * x) * Real.exp (-(s * x ^ 2)) := by
    unfold G
    have hcos : cexp (I * ((a * x : ℝ) : ℂ)) = (Real.cos (a * x) : ℂ) + (Real.sin (a * x) : ℂ) * I := by
      rw [mul_comm I ((a * x : ℝ) : ℂ)]
      rw [Complex.exp_mul_I]
      rw [Complex.ofReal_cos, Complex.ofReal_sin]
    have hexp1 : cexp (-(s : ℂ) * (x : ℂ) ^ 2) = (Real.exp (-(s * x ^ 2)) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      rw [neg_mul]
      rw [Complex.ofReal_neg]
      rw [neg_inj]
      rw [← Complex.ofReal_pow x 2]
      rw [← Complex.ofReal_mul]
    rw [harg x, hexp1]
    rw [Complex.re_mul_ofReal]
    rw [hcos]
    rw [Complex.add_re, Complex.mul_re]
    rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hfull := fourierIntegral_gaussian hb (a : ℂ)
  have hcpow : ((Real.pi : ℂ) / (s : ℂ)) ^ ((1 / 2 : ℂ)) = (Real.sqrt (Real.pi / s) : ℂ) := by
    rw [← Complex.ofReal_div Real.pi s]
    have hh : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hh]
    rw [← Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / s) (1 / 2 : ℝ)]
    congr 1
    rw [Real.sqrt_eq_rpow]
  have hcarg : cexp (-(a : ℂ) ^ 2 / (4 * (s : ℂ))) = (Real.exp (-(a ^ 2 / (4 * s))) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    have hneg : (-(a : ℂ) ^ 2) / (4 * (s : ℂ)) = -((a : ℂ) ^ 2 / (4 * (s : ℂ))) := by ring
    rw [hneg]
    rw [Complex.ofReal_neg]
    rw [neg_inj]
    rw [← Complex.ofReal_pow a 2]
    have h4 : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
    rw [h4]
    rw [← Complex.ofReal_mul (4 : ℝ) s]
    rw [← Complex.ofReal_div (a ^ 2) (4 * s)]
  calc
    ∫ x : ℝ, Real.cos (a * x) * Real.exp (-(s * x ^ 2)) =
        ∫ x : ℝ, (G x).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hre_fun x]
    _ = (∫ x : ℝ, G x).re := by
      simpa using (integral_re hGint : ∫ x : ℝ, RCLike.re (G x) = RCLike.re (∫ x : ℝ, G x))
    _ = Real.sqrt (Real.pi / s) * Real.exp (-(a ^ 2 / (4 * s))) := by
      have hval : (∫ x : ℝ, G x) = ((Real.sqrt (Real.pi / s) * Real.exp (-(a ^ 2 / (4 * s))) : ℝ) : ℂ) := by
        change ∫ x : ℝ, cexp (I * (a : ℂ) * (x : ℂ)) * cexp (-(s : ℂ) * (x : ℂ) ^ 2) =
          ((Real.sqrt (Real.pi / s) * Real.exp (-(a ^ 2 / (4 * s))) : ℝ) : ℂ)
        rw [hfull]
        rw [hcpow, hcarg]
        rw [← Complex.ofReal_mul]
      rw [hval]
      exact Complex.ofReal_re _

lemma gaussian_cos_Ioi (a s : ℝ) (hs : 0 < s) :
    (∫ x in Set.Ioi (0 : ℝ), Real.cos (a * x) * Real.exp (-(s * x ^ 2))) =
      (Real.sqrt (Real.pi / s) * Real.exp (-(a ^ 2 / (4 * s)))) / 2 := by
  let f : ℝ → ℝ := fun x => Real.cos (a * x) * Real.exp (-(s * x ^ 2))
  have hf_int : Integrable f := by
    refine Integrable.mono' (g := fun x : ℝ => Real.exp (-(s * x ^ 2))) ?_ ?_ ?_
    · simpa using integrable_exp_neg_mul_sq hs
    · fun_prop
    · filter_upwards with x
      unfold f
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        |Real.cos (a * x)| * Real.exp (-(s * x ^ 2))
            ≤ 1 * Real.exp (-(s * x ^ 2)) :=
              mul_le_mul_of_nonneg_right (abs_cos_le_one (a * x)) (Real.exp_pos _).le
        _ = Real.exp (-(s * x ^ 2)) := by rw [one_mul]
  have full_integral := gaussian_cos_univ a s hs
  have heven (x : ℝ) : f (-x) = f x := by
    unfold f
    simp [Real.cos_neg]
  have h_eq := calc
    ∫ x : ℝ in Iic 0, f x = ∫ x : ℝ in Ioi 0, f (-x) := by
      simpa using (integral_comp_neg_Ioi 0 f).symm
    _ = ∫ x : ℝ in Ioi 0, f x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact heven x
  rw [← integral_add_compl (s := Ioi 0) (by simp) hf_int, compl_Ioi, h_eq, ← mul_two] at full_integral
  exact (eq_div_iff (two_ne_zero)).2 (by simpa using full_integral)

lemma dom_integrable :
    Integrable (fun p : ℝ × ℝ => Real.exp (-p.2) * Real.exp (-(p.2 * p.1 ^ 2)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let B : ℝ × ℝ → ℝ := fun p => Real.exp (-p.2) * Real.exp (-(p.2 * p.1 ^ 2))
  have hmeas : AEStronglyMeasurable B (μ.prod μ) := by fun_prop
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards with x
    refine Integrable.mono' (g := fun t : ℝ => Real.exp (-(1 + x ^ 2) * t)) ?_ ?_ ?_
    · have ha : -(1 + x ^ 2) < 0 := by linarith [sq_nonneg x]
      have hbound := integrableOn_exp_mul_Ioi (a := -(1 + x ^ 2)) ha (0 : ℝ)
      change Integrable (fun t : ℝ => Real.exp (-(1 + x ^ 2) * t)) μ
      exact hbound
    · fun_prop
    · filter_upwards with t
      have hb : ‖B (x, t)‖ = Real.exp (-(1 + x ^ 2) * t) := by
        unfold B
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hb]
  · have hval (x : ℝ) : (∫ t : ℝ, ‖B (x, t)‖ ∂μ) = (1 + x ^ 2)⁻¹ := by
      rw [show (∫ t : ℝ, ‖B (x, t)‖ ∂μ) = ∫ t : ℝ in Set.Ioi (0 : ℝ), ‖B (x, t)‖ by rfl]
      have hinteq (t : ℝ) : ‖B (x, t)‖ = Real.exp (-(1 + x ^ 2) * t) := by
        unfold B
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show (fun t : ℝ => ‖B (x, t)‖) = fun t : ℝ => Real.exp (-(1 + x ^ 2) * t) by
        funext t; exact hinteq t]
      have hcore : (1 + x ^ 2)⁻¹ = ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(1 + x ^ 2) * t) := by
        have ha : -(1 + x ^ 2) < 0 := by linarith [sq_nonneg x]
        have h := integral_exp_mul_Ioi (a := -(1 + x ^ 2)) ha (0 : ℝ)
        rw [h]
        rw [mul_zero, Real.exp_zero]
        field_simp
      exact hcore.symm
    refine Integrable.mono' (g := fun x : ℝ => (1 + x ^ 2)⁻¹) ?_ ?_ ?_
    · exact integrable_inv_one_add_sq.integrableOn
    · have hn : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖B p‖) (μ.prod μ) := by fun_prop
      exact hn.integral_prod_right'
    · filter_upwards with x
      rw [hval x]
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]

lemma fubini_cauchy (a : ℝ) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a * x) / (1 + x ^ 2)) =
      (1 / 2) * (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (Real.pi / t) *
        Real.exp (-t) * Real.exp (-(a ^ 2 / (4 * t)))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun x t => Real.cos (a * x) * Real.exp (-t) * Real.exp (-(t * x ^ 2))
  have hFint : Integrable (fun p : ℝ × ℝ => F p.1 p.2) (μ.prod μ) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => Real.exp (-p.2) * Real.exp (-(p.2 * p.1 ^ 2))) ?_ ?_ ?_
    · exact dom_integrable
    · fun_prop
    · filter_upwards with p
      unfold F
      rw [Real.norm_eq_abs]
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_cos_le_one (a * p.1)) (Real.exp_pos _).le)
        (Real.exp_pos _).le).trans_eq (by rw [one_mul])
  have hrep (x : ℝ) : Real.cos (a * x) / (1 + x ^ 2) = ∫ t : ℝ, F x t ∂μ := by
    have hcore : (1 + x ^ 2)⁻¹ = ∫ t : ℝ, Real.exp (-(1 + x ^ 2) * t) ∂μ := by
      have ha : -(1 + x ^ 2) < 0 := by linarith [sq_nonneg x]
      have h := integral_exp_mul_Ioi (a := -(1 + x ^ 2)) ha (0 : ℝ)
      rw [show (∫ t : ℝ, Real.exp (-(1 + x ^ 2) * t) ∂μ) =
        ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(1 + x ^ 2) * t) by rfl]
      rw [h]
      rw [mul_zero, Real.exp_zero]
      field_simp
    have hinteq (t : ℝ) : F x t = Real.cos (a * x) * Real.exp (-(1 + x ^ 2) * t) := by
      unfold F
      rw [mul_assoc]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.cos (a * x) / (1 + x ^ 2)
          = Real.cos (a * x) * (1 + x ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ = Real.cos (a * x) * ∫ t : ℝ, Real.exp (-(1 + x ^ 2) * t) ∂μ := by rw [hcore]
      _ = ∫ t : ℝ, Real.cos (a * x) * Real.exp (-(1 + x ^ 2) * t) ∂μ := by
            rw [← integral_const_mul]
      _ = ∫ t : ℝ, F x t ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            exact (hinteq t).symm
  have hinner (t : ℝ) (ht : 0 < t) :
      (∫ x : ℝ, F x t ∂μ) = (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-t) *
        Real.exp (-(a ^ 2 / (4 * t)))) := by
    calc
      (∫ x : ℝ, F x t ∂μ)
          = ∫ x : ℝ in Set.Ioi (0 : ℝ), F x t := by rfl
      _ = ∫ x : ℝ in Set.Ioi (0 : ℝ), (Real.cos (a * x) * Real.exp (-(t * x ^ 2))) * Real.exp (-t) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            unfold F
            ring
      _ = (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a * x) * Real.exp (-(t * x ^ 2))) * Real.exp (-t) := by
            rw [integral_mul_const]
      _ = Real.exp (-t) * (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a * x) * Real.exp (-(t * x ^ 2))) := by ring
      _ = Real.exp (-t) * ((Real.sqrt (Real.pi / t) * Real.exp (-(a ^ 2 / (4 * t)))) / 2) := by
            rw [gaussian_cos_Ioi a t ht]
      _ = (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-t) * Real.exp (-(a ^ 2 / (4 * t)))) := by ring
  calc
    (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a * x) / (1 + x ^ 2))
        = ∫ x : ℝ, Real.cos (a * x) / (1 + x ^ 2) ∂μ := by rfl
    _ = ∫ x : ℝ, (∫ t : ℝ, F x t ∂μ) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hrep x]
    _ = ∫ t : ℝ, (∫ x : ℝ, F x t ∂μ) ∂μ := by
          exact integral_integral_swap hFint
    _ = ∫ t : ℝ, (1 / 2) * (Real.sqrt (Real.pi / t) * Real.exp (-t) * Real.exp (-(a ^ 2 / (4 * t)))) ∂μ := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hinner t ht
    _ = (1 / 2) * ∫ t : ℝ, (Real.sqrt (Real.pi / t) * Real.exp (-t) * Real.exp (-(a ^ 2 / (4 * t)))) ∂μ := by
          rw [← integral_const_mul]
    _ = (1 / 2) * (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t) * Real.exp (-(a ^ 2 / (4 * t)))) := by rfl



/-! ### The classical identity `∫_0^∞ e^{−(u−c/u)²} du = √π/2`, `c > 0`. -/

lemma cinv_deriv (c u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => c / t) (-(c / u ^ 2)) u := by
  simpa [div_eq_mul_inv] using (hasDerivAt_inv hu).const_mul c

lemma phi_deriv (c u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => t - c / t) (1 + c / u ^ 2) u := by
  have hsub : HasDerivAt (fun t : ℝ => t - c / t) (1 - (-(c / u ^ 2))) u :=
    (hasDerivAt_id u).sub (cinv_deriv c u hu)
  simpa [sub_eq_add_neg, add_comm] using hsub

lemma phi_inj (c : ℝ) (hc : 0 ≤ c) : InjOn (fun t : ℝ => t - c / t) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  field_simp [hx0, hy0] at hxy
  have hf : (x - y) * (x * y + c) = 0 := by
    ring_nf at hxy ⊢
    linarith
  have hxyc : 0 < x * y + c := by
    have : 0 ≤ c := hc
    nlinarith [mul_pos hx (mem_Ioi.mp hy)]
  have hxy0 : x - y = 0 := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hxyc)
  linarith

/-- The map `u ↦ u − c/u` sends `(0,∞)` onto all of `ℝ` (for `c > 0`). -/
lemma phi_image (c : ℝ) (hc : 0 < c) : (fun t : ℝ => t - c / t) '' Ioi (0 : ℝ) = univ := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    trivial
  · intro hw
    let d : ℝ := Real.sqrt (w ^ 2 + 4 * c)
    let u : ℝ := (w + d) / 2
    have hsq : 0 ≤ w ^ 2 + 4 * c := by nlinarith [sq_nonneg w, hc]
    have hd_sq : d ^ 2 = w ^ 2 + 4 * c := by
      dsimp [d]
      rw [Real.sq_sqrt hsq]
    have hd_gt : |w| < d := by
      dsimp [d]
      rw [← Real.sqrt_sq_eq_abs w]
      exact Real.sqrt_lt_sqrt (sq_nonneg w) (by nlinarith [hc])
    have hwd : w + d > 0 := by
      have : -w ≤ |w| := neg_le_abs w
      linarith
    have hu : 0 < u := by
      dsimp [u]
      exact half_pos hwd
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hquad : u ^ 2 - w * u - c = 0 := by
      dsimp [u]
      ring_nf
      nlinarith [hd_sq]
    have hcu : c / u = u - w := by
      apply (div_eq_iff hu0).2
      nlinarith [hquad]
    have hphi : u - c / u = w := by
      rw [hcu]
      ring
    exact ⟨u, hu, hphi⟩

lemma phi_deriv_pos (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : 0 < u) : 0 < 1 + c / u ^ 2 := by
  have : 0 < c / u ^ 2 := div_pos hc (sq_pos_of_pos hu)
  nlinarith

/-- Change of variable `w = u − c/u`: `∫_{u>0} (1 + c/u²)·e^{−(u−c/u)²} du = ∫_ℝ e^{−w²} dw`. -/
lemma phi_value (c : ℝ) (hc : 0 < c) :
    (∫ u : ℝ in Ioi (0 : ℝ), (1 + c / u ^ 2) * Real.exp (-(u - c / u) ^ 2)) =
      ∫ w : ℝ, Real.exp (-(w ^ 2)) := by
  have him := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => t - c / t) (f' := fun u : ℝ => 1 + c / u ^ 2)
    (hs := measurableSet_Ioi)
    (hf' := fun u hu => (phi_deriv c u (ne_of_gt hu)).hasDerivWithinAt)
    (hf := phi_inj c hc.le)
    (g := fun w : ℝ => Real.exp (-(w ^ 2)))
  rw [phi_image c hc] at him
  calc
    (∫ u : ℝ in Ioi (0 : ℝ), (1 + c / u ^ 2) * Real.exp (-(u - c / u) ^ 2))
        = ∫ u : ℝ in Ioi (0 : ℝ), |1 + c / u ^ 2| • Real.exp (-(u - c / u) ^ 2) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
          have hpos : 0 ≤ 1 + c / u ^ 2 := (phi_deriv_pos c hc u hu).le
          simp [abs_of_nonneg hpos]
    _ = ∫ w : ℝ, Real.exp (-(w ^ 2)) := by
          simpa [smul_eq_mul] using him.symm

lemma cinv_inj (c : ℝ) (hc : 0 < c) : InjOn (fun u : ℝ => c / u) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp [hx0, hy0, hc0] at hxy
  linarith

lemma cinv_image (c : ℝ) (hc : 0 < c) : (fun u : ℝ => c / u) '' Ioi 0 = Ioi 0 := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_pos hc (mem_Ioi.mp hu)
  · intro hw
    refine ⟨c / w, ?_, ?_⟩
    · exact div_pos hc (mem_Ioi.mp hw)
    · field_simp [ne_of_gt (mem_Ioi.mp hw)]

/-- Change of variable `v = c/u`: `∫_{v>0} e^{−(v−c/v)²} dv = ∫_{u>0} (c/u²)·e^{−(u−c/u)²} du`. -/
lemma cinv_value (c : ℝ) (hc : 0 < c) :
    (∫ v : ℝ in Ioi (0 : ℝ), Real.exp (-(v - c / v) ^ 2)) =
      ∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * Real.exp (-(u - c / u) ^ 2) := by
  have him := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun t : ℝ => c / t) (f' := fun u : ℝ => -(c / u ^ 2))
    (hs := measurableSet_Ioi)
    (hf' := fun u hu => (cinv_deriv c u (ne_of_gt hu)).hasDerivWithinAt)
    (hf := cinv_inj c hc)
    (g := fun v : ℝ => Real.exp (-(v - c / v) ^ 2))
  rw [cinv_image c hc] at him
  calc
    (∫ v : ℝ in Ioi (0 : ℝ), Real.exp (-(v - c / v) ^ 2))
        = ∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * Real.exp (-(u - c / u) ^ 2) := by
          rw [him]
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
          have hpos : 0 ≤ c / u ^ 2 := div_nonneg hc.le (sq_pos_of_pos hu).le
          have habs : |-(c / u ^ 2)| = c / u ^ 2 := by
            rw [abs_neg]
            exact abs_of_nonneg hpos
          have hcuu : c / (c / u) = u := by
            field_simp [hc.ne', (ne_of_gt (mem_Ioi.mp hu))]
          have harg : -(c / u - c / (c / u)) ^ 2 = -(u - c / u) ^ 2 := by
            rw [hcuu]
            field_simp [hc.ne', (ne_of_gt (mem_Ioi.mp hu))]
            ring
          rw [habs]
          simp only [smul_eq_mul]
          rw [harg]

/-- Integrability of `(1 + c/u²)·e^{−(u−c/u)²}` on `(0,∞)`, pulled back from `e^{−w²}`. -/
lemma tot_int (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (1 + c / u ^ 2) * Real.exp (-(u - c / u) ^ 2)) (Ioi (0 : ℝ)) := by
  have hpull : IntegrableOn (fun u : ℝ => |1 + c / u ^ 2| • Real.exp (-(u - c / u) ^ 2)) (Ioi 0) := by
    have hL : IntegrableOn (fun w : ℝ => Real.exp (-(w ^ 2))) univ := by
      rw [integrableOn_univ]
      simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num))
    have him := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun t : ℝ => t - c / t) (f' := fun u : ℝ => 1 + c / u ^ 2)
      (hs := measurableSet_Ioi)
      (hf' := fun u hu => (phi_deriv c u (ne_of_gt hu)).hasDerivWithinAt)
      (hf := phi_inj c hc.le)
      (g := fun w : ℝ => Real.exp (-(w ^ 2)))).1
    rw [phi_image c hc] at him
    exact him hL
  refine hpull.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hpos : 0 ≤ 1 + c / u ^ 2 := (phi_deriv_pos c hc u hu).le
  simp [abs_of_nonneg hpos]

lemma g_meas (c : ℝ) :
    AEStronglyMeasurable (fun u : ℝ => Real.exp (-(u - c / u) ^ 2)) (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

lemma cg_meas (c : ℝ) :
    AEStronglyMeasurable (fun u : ℝ => (c / u ^ 2) * Real.exp (-(u - c / u) ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

lemma g_int (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-(u - c / u) ^ 2)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (tot_int c hc) ?_ ?_
  · exact g_meas c
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
    have he : 0 ≤ Real.exp (-(u - c / u) ^ 2) := (exp_pos _).le
    have h1 : 1 ≤ 1 + c / u ^ 2 := by
      have : 0 ≤ c / u ^ 2 := div_nonneg hc.le (sq_pos_of_pos hu).le
      nlinarith
    simpa using mul_le_mul_of_nonneg_right h1 he

lemma cg_int (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (c / u ^ 2) * Real.exp (-(u - c / u) ^ 2)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (tot_int c hc) ?_ ?_
  · exact cg_meas c
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le,
      abs_of_nonneg (div_nonneg hc.le (sq_pos_of_pos hu).le)]
    have he : 0 ≤ Real.exp (-(u - c / u) ^ 2) := (exp_pos _).le
    exact mul_le_mul_of_nonneg_right (by nlinarith : c / u ^ 2 ≤ 1 + c / u ^ 2) he

/-- `∫_{u>0} e^{−(u−c/u)²} du = √π/2` for `c > 0`. -/
lemma phi_integral_value (c : ℝ) (hc : 0 < c) :
    (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-(u - c / u) ^ 2)) = Real.sqrt Real.pi / 2 := by
  let g : ℝ → ℝ := fun u => Real.exp (-(u - c / u) ^ 2)
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa [g] using g_int c hc
  have hcg_int : IntegrableOn (fun u : ℝ => (c / u ^ 2) * g u) (Ioi (0 : ℝ)) := by
    simpa [g] using cg_int c hc
  have hsum : (∫ u : ℝ in Ioi (0 : ℝ), (1 + c / u ^ 2) * g u) =
      (∫ u : ℝ in Ioi (0 : ℝ), g u) + (∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * g u) := by
    calc
      (∫ u : ℝ in Ioi (0 : ℝ), (1 + c / u ^ 2) * g u)
          = ∫ u : ℝ in Ioi (0 : ℝ), (g u + (c / u ^ 2) * g u) := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
            ring
      _ = (∫ u : ℝ in Ioi (0 : ℝ), g u) + (∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * g u) := by
            rw [integral_add hg_int hcg_int]
  have hgauss : (∫ w : ℝ, Real.exp (-(w ^ 2))) = Real.sqrt Real.pi := by
    have hg := integral_gaussian (1 : ℝ)
    simpa [div_one] using hg
  have hphi := phi_value c hc
  have hcinv := cinv_value c hc
  have hcinv' : (∫ u : ℝ in Ioi (0 : ℝ), g u) = (∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * g u) := by
    simpa [g] using hcinv
  have htwo : (∫ u : ℝ in Ioi (0 : ℝ), g u) * 2 = Real.sqrt Real.pi := by
    calc
      (∫ u : ℝ in Ioi (0 : ℝ), g u) * 2
          = (∫ u : ℝ in Ioi (0 : ℝ), g u) + (∫ u : ℝ in Ioi (0 : ℝ), g u) := by ring
      _ = (∫ u : ℝ in Ioi (0 : ℝ), g u) + (∫ u : ℝ in Ioi (0 : ℝ), (c / u ^ 2) * g u) := by
            linarith
      _ = (∫ u : ℝ in Ioi (0 : ℝ), (1 + c / u ^ 2) * g u) := by
            rw [← hsum]
      _ = Real.sqrt Real.pi := by
            simpa [g] using hphi.trans hgauss
  simpa [g] using (eq_div_iff (two_ne_zero' ℝ)).2 htwo

/-! ### Evaluation of `∫_{t>0} √(π/t)·e^{−t}·e^{−a²/(4t)} dt = π·e^{−|a|}`. -/

/-- `∫_{u>0} e^{−(u² + a²/(4u²))} du = (√π/2)·e^{−|a|}` for `a ≠ 0`. -/
lemma integral_exp_neg_sq_sub (a : ℝ) (ha : a ≠ 0) :
    (∫ u : ℝ in Ioi 0, Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2)))) =
      (Real.sqrt Real.pi / 2) * Real.exp (-|a|) := by
  let c : ℝ := |a| / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (abs_pos.mpr ha) two_pos
  have hval := phi_integral_value c hc
  have hpoint : ∀ u ∈ Ioi (0 : ℝ), Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))) =
      Real.exp (-|a|) * Real.exp (-(u - c / u) ^ 2) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    rw [← Real.exp_add]
    congr 1
    dsimp [c]
    have hsq : |a| ^ 2 = a ^ 2 := sq_abs a
    field_simp [hu0]
    ring_nf
    rw [hsq]
  calc
    (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))))
        = ∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-|a|) * Real.exp (-(u - c / u) ^ 2) := by
            refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpoint u hu)
    _ = Real.exp (-|a|) * (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-(u - c / u) ^ 2)) := by
            rw [integral_const_mul]
    _ = Real.exp (-|a|) * (Real.sqrt Real.pi / 2) := by rw [hval]
    _ = (Real.sqrt Real.pi / 2) * Real.exp (-|a|) := by ring

/-- The case `a ≠ 0` of the exponential evaluation, by `t = u²`. -/
lemma exp_eval_ne_zero (a : ℝ) (ha : a ≠ 0) :
    (∫ t : ℝ in Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t) *
        Real.exp (-(a ^ 2 / (4 * t)))) =
      Real.pi * Real.exp (-|a|) := by
  let F : ℝ → ℝ := fun t => Real.sqrt (Real.pi / t) * Real.exp (-t) *
        Real.exp (-(a ^ 2 / (4 * t)))
  have hsub := (integral_comp_rpow_Ioi_of_pos (g := F) (p := 2) (by norm_num : (0:ℝ) < 2)).symm
  have hpow : ∀ u ∈ Ioi (0 : ℝ), u ^ ((2 : ℝ) - 1) = u := by
    intro u hu
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact Real.rpow_one u
  have hpt2 : ∀ u ∈ Ioi (0 : ℝ),
      (2 * u) * (Real.sqrt (Real.pi / u ^ 2) * Real.exp (-(u ^ 2)) *
          Real.exp (-(a ^ 2 / (4 * u ^ 2)))) =
        (2 * Real.sqrt Real.pi) * Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hsqrt : Real.sqrt (Real.pi / u ^ 2) = Real.sqrt Real.pi / u := by
      rw [Real.sqrt_div pi_nonneg (u ^ 2)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu.le]
    have hexp : Real.exp (-(u ^ 2)) * Real.exp (-(a ^ 2 / (4 * u ^ 2))) =
        Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hcoef : 2 * u * (Real.sqrt Real.pi / u) = 2 * Real.sqrt Real.pi := by
      field_simp [hu0]
    rw [hsqrt]
    calc
      2 * u * (Real.sqrt Real.pi / u * Real.exp (-(u ^ 2)) * Real.exp (-(a ^ 2 / (4 * u ^ 2))))
          = (2 * u * (Real.sqrt Real.pi / u)) * (Real.exp (-(u ^ 2)) * Real.exp (-(a ^ 2 / (4 * u ^ 2)))) := by
              ring
      _ = (2 * Real.sqrt Real.pi) * (Real.exp (-(u ^ 2)) * Real.exp (-(a ^ 2 / (4 * u ^ 2)))) := by
              rw [hcoef]
      _ = 2 * Real.sqrt Real.pi * Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))) := by
              rw [hexp]
  calc
    (∫ t : ℝ in Ioi (0 : ℝ), F t)
        = ∫ u : ℝ in Ioi (0 : ℝ), (2 * u) * (Real.sqrt (Real.pi / u ^ 2) * Real.exp (-(u ^ 2)) *
            Real.exp (-(a ^ 2 / (4 * u ^ 2)))) := by
          rw [hsub]
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
          have h2 : u ^ (2 : ℝ) = u ^ 2 := Real.rpow_natCast u 2
          rw [hpow u hu, h2]
          simp only [smul_eq_mul]
          dsimp [F]
    _ = ∫ u : ℝ in Ioi (0 : ℝ), (2 * Real.sqrt Real.pi) * Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2))) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpt2 u hu)
    _ = (2 * Real.sqrt Real.pi) * (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-(u ^ 2 + a ^ 2 / (4 * u ^ 2)))) := by
          rw [integral_const_mul]
    _ = (2 * Real.sqrt Real.pi) * ((Real.sqrt Real.pi / 2) * Real.exp (-|a|)) := by
          rw [integral_exp_neg_sq_sub a ha]
    _ = Real.pi * Real.exp (-|a|) := by
          ring_nf
          rw [Real.sq_sqrt pi_nonneg]
          ring

/-- The case `a = 0` of the exponential evaluation. -/
lemma exp_eval_zero :
    (∫ t : ℝ in Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t)) = Real.pi := by
  let F : ℝ → ℝ := fun t => Real.sqrt (Real.pi / t) * Real.exp (-t)
  have hsub := (integral_comp_rpow_Ioi_of_pos (g := F) (p := 2) (by norm_num : (0:ℝ) < 2)).symm
  have hpow : ∀ u ∈ Ioi (0 : ℝ), u ^ ((2 : ℝ) - 1) = u := by
    intro u hu
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    exact Real.rpow_one u
  have hpt2 : ∀ u ∈ Ioi (0 : ℝ),
      (2 * u) * (Real.sqrt (Real.pi / u ^ 2) * Real.exp (-(u ^ 2))) =
        (2 * Real.sqrt Real.pi) * Real.exp (-(u ^ 2)) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hsqrt : Real.sqrt (Real.pi / u ^ 2) = Real.sqrt Real.pi / u := by
      rw [Real.sqrt_div pi_nonneg (u ^ 2)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu.le]
    have hcoef : 2 * u * (Real.sqrt Real.pi / u) = 2 * Real.sqrt Real.pi := by
      field_simp [hu0]
    rw [hsqrt]
    calc
      2 * u * (Real.sqrt Real.pi / u * Real.exp (-(u ^ 2)))
          = (2 * u * (Real.sqrt Real.pi / u)) * Real.exp (-(u ^ 2)) := by ring
      _ = 2 * Real.sqrt Real.pi * Real.exp (-(u ^ 2)) := by rw [hcoef]
  calc
    (∫ t : ℝ in Ioi (0 : ℝ), F t)
        = ∫ u : ℝ in Ioi (0 : ℝ), (2 * u) * (Real.sqrt (Real.pi / u ^ 2) * Real.exp (-(u ^ 2))) := by
          rw [hsub]
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
          have h2 : u ^ (2 : ℝ) = u ^ 2 := Real.rpow_natCast u 2
          rw [hpow u hu, h2]
          simp only [smul_eq_mul]
          dsimp [F]
    _ = ∫ u : ℝ in Ioi (0 : ℝ), (2 * Real.sqrt Real.pi) * Real.exp (-(u ^ 2)) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpt2 u hu)
    _ = (2 * Real.sqrt Real.pi) * (∫ u : ℝ in Ioi (0 : ℝ), Real.exp (-(u ^ 2))) := by
          rw [integral_const_mul]
    _ = (2 * Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) := by
          congr 1
          simpa [div_one] using integral_gaussian_Ioi (1 : ℝ)
    _ = Real.pi := by
          ring_nf
          rw [Real.sq_sqrt pi_nonneg]

/-- `∫_{t>0} √(π/t)·e^{−t}·e^{−a²/(4t)} dt = π·e^{−|a|}` for all real `a`. -/
lemma exp_eval (a : ℝ) :
    (∫ t : ℝ in Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t) *
        Real.exp (-(a ^ 2 / (4 * t)))) =
      Real.pi * Real.exp (-|a|) := by
  by_cases ha : a = 0
  · subst a
    have hrew : (∫ t : ℝ in Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t) *
          Real.exp (-(0 ^ 2 / (4 * t)))) =
        (∫ t : ℝ in Ioi (0 : ℝ), Real.sqrt (Real.pi / t) * Real.exp (-t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      simp
    rw [hrew, exp_eval_zero]
    simp
  · simpa using exp_eval_ne_zero a ha

/-- `∫_0^∞ cos (a·x) / (1+x²) dx = (π/2)·e^{−|a|}`, as a Lebesgue integral. -/
theorem cos_inv_one_add_sq_Ioi (a : ℝ) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.cos (a * x) / (1 + x ^ 2)) =
      (Real.pi / 2) * Real.exp (-|a|) := by
  have hf := fubini_cauchy a
  have he := exp_eval a
  rw [hf, he]
  ring


end Commons.Analysis.Fourier
