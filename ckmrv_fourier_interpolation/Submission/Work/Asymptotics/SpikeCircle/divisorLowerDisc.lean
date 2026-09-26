/-
# The divisor lower bound in the spike circle

This file proves

`Work.Asymptotics.SpikeCircle.divisorLowerDisc`:

there is `c > 0` such that for every `τ` in the funnel and every `ζ` at distance at most
`29/20` from `τ`,

  `c * exp (2π Im τ) * ‖(ζ-τ)(ζ-τ-1)(ζ-τ+1)‖ ≤ ‖j τ - j ζ‖`.

The three zeros `τ-1`, `τ`, `τ+1` are exactly the points of the `j`-orbit of `τ` in the
closed disc of radius `29/20` (`fiber_orbit_gap`).  On the boundary circle the estimate is
obtained from the cusp expansion of `j` together with `exp_circle_lower` when `Im τ` is
large, and from compactness of the strip (`sphereLowerStrip`) when `Im τ` is bounded; the
third divided difference of `z ↦ j z - j τ` is then non-zero on the closed disc and the
minimum modulus principle (`disc_lower`) upgrades the boundary bound to the full disc.

The lift `jLift` of `j` to `ℂ` and its three divided differences along the zeros are the
technical devices that make the minimum modulus argument available.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Residues.normalizedDeriv_jInvariantFun
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.jInvariantFun_cusp_second

namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane
open scoped Manifold Topology

set_option maxHeartbeats 1000000

noncomputable section

lemma exp_circle_lower (w : ℂ) (hw : ‖w‖ = 29 / 20) :
    (1 / 2 : ℝ) ≤ ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖ := by
  set a : ℝ := w.re with ha
  set b : ℝ := w.im with hb
  have hsq : a ^ 2 + b ^ 2 = (29 / 20) ^ 2 := by
    have h2 : ‖w‖ ^ 2 = (29 / 20) ^ 2 := by rw [hw]
    rw [Complex.sq_norm, Complex.normSq_apply, ← ha, ← hb] at h2
    nlinarith [h2]
  set r : ℝ := Real.exp (-(2 * Real.pi * b)) with hr
  have hw_dec : w = (a : ℂ) + (b : ℂ) * Complex.I := by
    rw [Complex.ext_iff]; constructor <;> simp [ha, hb]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * w
      = ((-(2 * Real.pi * b) : ℝ) : ℂ) + ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I := by
    rw [hw_dec]
    have h1 : 2 * (Real.pi:ℂ) * Complex.I * (b:ℂ) * Complex.I = ((-(2*Real.pi*b) : ℝ) : ℂ) := by
      rw [show 2 * (Real.pi:ℂ) * Complex.I * (b:ℂ) * Complex.I
          = ((2*(Real.pi:ℂ)*(b:ℂ)) : ℂ) * (Complex.I * Complex.I) by ring]
      rw [Complex.I_mul_I]
      push_cast
      ring
    have h2 : 2 * (Real.pi:ℂ) * Complex.I * (a:ℂ) = (((2*Real.pi*a : ℝ)) : ℂ) * Complex.I := by
      push_cast; ring
    rw [show 2 * (Real.pi:ℂ) * Complex.I * ((a:ℂ) + (b:ℂ) * Complex.I)
        = 2 * (Real.pi:ℂ) * Complex.I * (a:ℂ) + 2 * (Real.pi:ℂ) * Complex.I * (b:ℂ) * Complex.I
        by ring, h2, h1]
    ring
  have hfac : Complex.exp (2 * Real.pi * Complex.I * w)
      = (r : ℂ) * Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) := by
    rw [harg, hr, Complex.exp_add, Complex.ofReal_exp]
  have hnormEa : ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * a)
  have hnrm : ‖(r:ℂ)‖ = r := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hnormE : ‖Complex.exp (2 * Real.pi * Complex.I * w)‖ = r := by
    rw [hfac, norm_mul, hnormEa, mul_one, hnrm]
  have hbnd : |r - 1| ≤ ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖ := by
    have h := abs_norm_sub_norm_le (Complex.exp (2 * Real.pi * Complex.I * w)) 1
    rw [norm_one, hnormE] at h
    exact h
  by_cases h : (1 / 2 : ℝ) ≤ ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖
  · exact h
  · have hlt : ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖ < 1 / 2 := not_le.mp h
    have habs : |r - 1| < 1 / 2 := lt_of_le_of_lt hbnd hlt
    have hr1 : (1 / 2 : ℝ) < r := by have := (abs_lt.mp habs).1; linarith
    have hr2 : r < 3 / 2 := by have := (abs_lt.mp habs).2; linarith
    have hb_lt : |b| < 0.1104 := by
      have h1 : Real.exp (Real.log (1/2)) < Real.exp (-(2 * Real.pi * b)) := by
        rw [Real.exp_log (by norm_num : (0:ℝ) < 1/2), ← hr]; exact hr1
      have h2 : Real.exp (-(2 * Real.pi * b)) < Real.exp (Real.log (3/2)) := by
        rw [Real.exp_log (by norm_num : (0:ℝ) < 3/2), ← hr]; exact hr2
      have e1 := Real.exp_lt_exp.mp h1
      have e2 := Real.exp_lt_exp.mp h2
      have hlog1 : Real.log (1/2) = - Real.log 2 := by
        rw [show (1/2:ℝ) = 2⁻¹ by norm_num, Real.log_inv]
      have hlog2 : Real.log (3/2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
      rw [hlog1] at e1
      have key : |2 * Real.pi * b| < Real.log 2 := by
        rw [abs_lt]; constructor <;> linarith
      have habs2 : |2 * Real.pi * b| = 2 * Real.pi * |b| := by
        rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [habs2] at key
      have key2 : |b| < Real.log 2 / (2 * Real.pi) := by
        rw [lt_div_iff₀ (by positivity)]; linarith [key]
      have h3 : Real.log 2 / (2 * Real.pi) < 0.1104 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [Real.log_two_lt_d9, Real.pi_gt_d6]
      linarith
    have hb2 : b ^ 2 ≤ 0.0122 := by nlinarith [sq_abs b, abs_nonneg b, hb_lt]
    have ha2 : (1.4457:ℝ) < |a| := by
      have h1 : (1.4457:ℝ)^2 < a^2 := by nlinarith [hsq, hb2]
      calc (1.4457:ℝ) = Real.sqrt ((1.4457:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
        _ < Real.sqrt (a^2) := Real.sqrt_lt_sqrt (by norm_num) h1
        _ = |a| := Real.sqrt_sq_eq_abs a
    have ha_le : |a| ≤ 29/20 := by
      have h1 : a^2 ≤ (29/20:ℝ)^2 := by nlinarith [hsq, sq_nonneg b]
      calc |a| = Real.sqrt (a^2) := (Real.sqrt_sq_eq_abs a).symm
        _ ≤ Real.sqrt ((29/20:ℝ)^2) := Real.sqrt_le_sqrt h1
        _ = 29/20 := Real.sqrt_sq (by norm_num)
    have hcos : Real.cos (2 * Real.pi * a) ≤ -0.9 := by
      have hx : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * |a|) := by
        rcases abs_choice a with h | h
        · rw [h]
        · rw [h, mul_neg, Real.cos_neg]
      rw [hx]
      set θ := 2 * Real.pi * |a| with hθ
      have hθ_lo : 9.07 < θ := by rw [hθ]; nlinarith [Real.pi_gt_d20, ha2]
      have hθ_hi : θ ≤ 9.12 := by rw [hθ]; nlinarith [Real.pi_lt_d20, ha_le]
      have hφ_hi : 3 * Real.pi - θ ≤ 0.355 := by nlinarith [Real.pi_lt_d20, hθ_lo]
      have h1 : 1 - (3 * Real.pi - θ) ^ 2 / 2 ≤ Real.cos (3 * Real.pi - θ) :=
        Real.one_sub_sq_div_two_le_cos
      have h2 : (3 * Real.pi - θ) ^ 2 ≤ 0.355 ^ 2 := by
        have h0 : (0:ℝ) ≤ 3 * Real.pi - θ := by nlinarith [Real.pi_gt_d20, hθ_hi]
        nlinarith [hφ_hi, h0]
      have h3 : -Real.cos (3 * Real.pi - θ) ≤ -0.9 := by nlinarith [h1, h2]
      have h4 : Real.cos θ = -Real.cos (3 * Real.pi - θ) := by
        have h5 : 3 * Real.pi - θ = (Real.pi - θ) + 2 * Real.pi := by ring
        rw [h5, Real.cos_add_two_pi, Real.cos_pi_sub]; ring
      rw [h4]; exact h3
    have hdec : Complex.exp (2 * Real.pi * Complex.I * w) - 1
        = (Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1)
          + Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) * ((r : ℂ) - 1) := by
      rw [hfac]; ring
    have hEa : (1.9 : ℝ) ≤ ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1‖ := by
      have hre : (Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1).re
          = Real.cos (2 * Real.pi * a) - 1 := by
        rw [Complex.exp_ofReal_mul_I]
        simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, sub_zero, mul_one]
        ring
      calc (1.9:ℝ) ≤ 1 - Real.cos (2*Real.pi*a) := by linarith [hcos]
        _ = |Real.cos (2*Real.pi*a) - 1| := by
            rw [abs_of_nonpos (by linarith [Real.cos_le_one (2*Real.pi*a)])]; ring
        _ = |(Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1).re| := by rw [hre]
        _ ≤ ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1‖ := Complex.abs_re_le_norm _
    have hlow : (1.9:ℝ) - |r - 1| ≤ ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖ := by
      rw [hdec]
      have h1 : ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1‖ -
          ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) * ((r:ℂ) - 1)‖
          ≤ ‖(Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1)
              + Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) * ((r:ℂ) - 1)‖ := by
        have h := abs_norm_sub_norm_le (Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) - 1)
          (-(Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) * ((r:ℂ) - 1)))
        rw [norm_neg, sub_neg_eq_add] at h
        exact le_trans (le_abs_self _) h
      have h2 : ‖Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I) * ((r:ℂ) - 1)‖ = |r - 1| := by
        rw [norm_mul, hnormEa, one_mul]
        have hrw : ((r:ℂ) - 1) = ((r - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [hrw, Complex.norm_def, Complex.normSq_ofReal,
          show (r - 1) * (r - 1) = (r - 1)^2 by ring, Real.sqrt_sq_eq_abs]
      linarith [hEa, h1, h2]
    linarith [hlow, habs]



/-! ## E6 does not vanish for `Im ≥ 2` -/

lemma E6Fun_ne_zero_im (z : UpperHalfPlane) (hz : 2 ≤ z.im) : Work.Kernels.E6Fun z ≠ 0 := by
  intro hE6
  have hdisc : Work.Kernels.DeltaFun z
      = (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2) / 1728 :=
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  have hE4cube : Work.Kernels.E4Fun z ^ 3 = 1728 * Work.Kernels.DeltaFun z := by
    rw [hdisc, hE6]; ring
  have hE4 : (1/2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ := by
    have hle := Work.FunnelNumerics.E4_sub_one_le z (le_trans (by norm_num) hz)
    have hsub : (1 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ + ‖Work.Kernels.E4Fun z - 1‖ := by
      have h := norm_sub_le (Work.Kernels.E4Fun z) (Work.Kernels.E4Fun z - 1)
      rw [show Work.Kernels.E4Fun z - (Work.Kernels.E4Fun z - 1) = 1 by ring, norm_one] at h
      exact h
    linarith
  have hE4n : (1/8 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hE4 3
    norm_num at h
    linarith
  have hD : ‖Work.Kernels.DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * z.im)) :=
    Work.Asymptotics.DeltaFun_upper_sharp z (le_trans (by norm_num) hz)
  have hexp : (27648 : ℝ) < Real.exp (4 * Real.pi) := by
    have h2 : (12:ℝ) < 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h3 : Real.exp 12 < Real.exp (4 * Real.pi) := Real.exp_lt_exp.mpr h2
    have h4 : (27648:ℝ) < Real.exp 12 := by
      have h5 : Real.exp 12 = (Real.exp 1)^12 := by
        rw [show (12:ℝ) = (12:ℕ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h5]
      have h6 : (2.7182818283:ℝ)^12 < (Real.exp 1)^12 :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      have h7 : (27648:ℝ) < (2.7182818283:ℝ)^12 := by norm_num
      linarith
    linarith
  have he : Real.exp (-(2 * Real.pi * z.im)) < 1/27648 := by
    have h2 : Real.exp (-(2*Real.pi*z.im)) ≤ Real.exp (-(4*Real.pi)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz]
    have h3 : Real.exp (-(4*Real.pi)) < 1/27648 := by
      rw [Real.exp_neg, show (1:ℝ)/27648 = (27648:ℝ)⁻¹ by norm_num]
      exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr hexp
    linarith
  have hDn : (1728:ℝ) * ‖Work.Kernels.DeltaFun z‖ < 1/8 := by
    have h2 : (1728:ℝ) * (2 * Real.exp (-(2 * Real.pi * z.im))) < 1/8 := by
      nlinarith [he]
    linarith
  have hnorm : ‖Work.Kernels.E4Fun z‖ ^ 3 = 1728 * ‖Work.Kernels.DeltaFun z‖ := by
    calc ‖Work.Kernels.E4Fun z‖ ^ 3 = ‖Work.Kernels.E4Fun z ^ 3‖ := (norm_pow _ _).symm
      _ = ‖1728 * Work.Kernels.DeltaFun z‖ := by rw [hE4cube]
      _ = 1728 * ‖Work.Kernels.DeltaFun z‖ := by rw [norm_mul, Complex.norm_ofNat]
  linarith [hE4n, hnorm, hDn]

/-! ## The lift of `j` to `ℂ` -/

def jLift : ℂ → ℂ := fun z => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)

lemma jLift_of_pos {z : ℂ} (hz : 0 < z.im) :
    jLift z = Work.Kernels.jInvariantFun ⟨z, hz⟩ := by
  simp only [jLift, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma jLift_diff : DifferentiableOn ℂ jLift {z : ℂ | 0 < z.im} := by
  have hMD : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant)
      (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)
  exact UpperHalfPlane.mdifferentiable_iff.mp hMD

lemma jLift_periodic (z : ℂ) (hz : 0 < z.im) : jLift (z + 1) = jLift z := by
  have hz1 : 0 < (z + 1).im := by
    have h1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_num
    rw [h1, Complex.add_im, Complex.ofReal_im, add_zero]
    exact hz
  rw [jLift_of_pos hz1, jLift_of_pos hz]
  have heq : (⟨z + 1, hz1⟩ : UpperHalfPlane) = (1:ℝ) +ᵥ (⟨z, hz⟩ : UpperHalfPlane) := by
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [heq, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

lemma deriv_jLift (τ : UpperHalfPlane) :
    deriv jLift (τ : ℂ) = (2 * (Real.pi : ℂ) * Complex.I)
      * Derivative.normalizedDerivOfComplex Work.Kernels.jInvariantFun τ := by
  rw [show jLift = (Work.Kernels.jInvariantFun ∘ UpperHalfPlane.ofComplex) from rfl,
    Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

lemma deriv_jLift_ne_zero (τ : UpperHalfPlane) (hτ : 2 ≤ τ.im) :
    deriv jLift (τ : ℂ) ≠ 0 := by
  rw [deriv_jLift, congr_fun Work.Residues.normalizedDeriv_jInvariantFun τ]
  refine mul_ne_zero
    (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) ?_
  refine div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 ?_) ?_))
    (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  · intro h0
    have h := Work.FunnelNumerics.E4_sub_one_le τ hτ
    rw [h0] at h
    norm_num at h
  · exact E6Fun_ne_zero_im τ hτ

/-! ## The orbit gap -/

lemma int_small (b : ℤ) (hb : ‖(((b : ℤ)) : ℂ)‖ ≤ 29/20) : b = -1 ∨ b = 0 ∨ b = 1 := by
  have hbR : |((b : ℝ))| < 2 := by
    have h := hb
    rw [Complex.norm_intCast] at h
    linarith
  have h1 : -(2:ℤ) < b := by
    by_contra hcon
    push_neg at hcon
    have h2 : ((b : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : b ≤ -2)
    rw [abs_of_neg (by linarith)] at hbR
    linarith
  have h3 : b < 2 := by
    by_contra hcon
    push_neg at hcon
    have h2 : (2:ℝ) ≤ ((b : ℤ) : ℝ) := by exact_mod_cast (by omega : (2:ℤ) ≤ b)
    rw [abs_of_nonneg (by linarith)] at hbR
    linarith
  omega

private lemma div_form {a b d : ℤ} (h : a * d = 1) (w : ℂ) :
    (((a : ℤ) : ℂ) * w + ((b : ℤ) : ℂ)) / (((d : ℤ) : ℂ))
      = w + (((b * a : ℤ) : ℂ)) := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · rw [ha, hd]; push_cast; ring
  · rw [ha, hd]; push_cast; ring

lemma orbitGap (τ : UpperHalfPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hτ : 2 ≤ τ.im) (h : ‖(((γ • τ : UpperHalfPlane)) : ℂ) - (τ : ℂ)‖ ≤ 29/20) :
    ∃ b : ℤ, (b = -1 ∨ b = 0 ∨ b = 1) ∧
      (((γ • τ : UpperHalfPlane)) : ℂ) = (τ : ℂ) + (b : ℂ) := by
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  by_cases hc : (γ 1 0 : ℤ) = 0
  · have hdet : (γ 0 0) * (γ 1 1) = 1 := by
      have h2 : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
        have := γ.2
        rw [Matrix.det_fin_two] at this
        exact this
      rw [hc, mul_zero, sub_zero] at h2
      exact h2
    have hval : (((γ • τ : UpperHalfPlane)) : ℂ)
        = (τ : ℂ) + (((γ 0 1) * (γ 0 0) : ℤ) : ℂ) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      rw [show ((algebraMap ℤ ℝ) (γ 1 0) : ℂ) = 0 by rw [hc]; simp,
        hcast (γ 0 0), hcast (γ 0 1), hcast (γ 1 1)]
      simp only [zero_mul, zero_add]
      exact div_form hdet (τ : ℂ)
    have hbnd : ‖((((γ 0 1) * (γ 0 0) : ℤ)) : ℂ)‖ ≤ 29/20 := by
      have h2 := h
      rw [hval] at h2
      rw [show (τ:ℂ) + ((((γ 0 1) * (γ 0 0) : ℤ)) : ℂ) - (τ:ℂ)
        = ((((γ 0 1) * (γ 0 0) : ℤ)) : ℂ) by ring] at h2
      exact h2
    rcases int_small ((γ 0 1) * (γ 0 0)) hbnd with hb | hb | hb
    · exact ⟨_, Or.inl hb, hval⟩
    · exact ⟨_, Or.inr (Or.inl hb), hval⟩
    · exact ⟨_, Or.inr (Or.inr hb), hval⟩
  · exfalso
    have hc1 : (1:ℝ) ≤ |(((γ 1 0 : ℤ)) : ℝ)| := by
      have h1 : (1:ℤ) ≤ |(γ 1 0 : ℤ)| := Int.one_le_abs hc
      exact_mod_cast h1
    set c : ℝ := (((γ 1 0 : ℤ)) : ℝ) with hcdef
    set dz : ℂ := UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ))
      ((τ : ℂ)) with hzdef
    have hcast2 : ∀ n : ℤ, ((n : ℂ)) = (((n : ℝ)) : ℂ) := fun n => by push_cast; ring
    have hzim : dz.im = c * τ.im := by
      rw [hzdef, ModularGroup.denom_apply, hcdef]
      simp only [hcast2, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        UpperHalfPlane.coe_im, zero_mul, add_zero] <;> ring
    have hNN : (4:ℝ) ≤ Complex.normSq dz := by
      have h1 : dz.im * dz.im ≤ Complex.normSq dz := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg dz.re]
      have h2 : (4:ℝ) ≤ dz.im * dz.im := by
        rw [hzim]
        have hc2 : (1:ℝ) ≤ c * c := by
          have h3 : (1:ℝ) ≤ |c| * |c| := by nlinarith [hc1, abs_nonneg c]
          have h4 : |c| * |c| = c * c := by
            rw [← abs_mul, abs_of_nonneg (mul_self_nonneg c)]
          linarith [h3, h4]
        have hb2 : (0:ℝ) ≤ c * c := by linarith
        have hτ2 : (4:ℝ) ≤ τ.im * τ.im := by nlinarith [hτ]
        calc (4:ℝ) = 1 * 4 := by ring
          _ ≤ (c * c) * (τ.im * τ.im) := mul_le_mul hc2 hτ2 (by norm_num) hb2
          _ = (c * τ.im) * (c * τ.im) := by ring
      linarith
    have him : (((γ • τ : UpperHalfPlane))).im ≤ τ.im / 4 := by
      have h1 := ModularGroup.im_smul_eq_div_normSq γ τ
      rw [h1, hzdef.symm]
      exact div_le_div_of_nonneg_left (le_of_lt τ.im_pos) (by norm_num) hNN
    have hdist : |(((γ • τ : UpperHalfPlane))).im - τ.im| ≤ 29/20 := by
      have h1 := Complex.abs_im_le_norm ((((γ • τ : UpperHalfPlane)) : ℂ) - (τ : ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h1
      linarith
    have h5 : -(29/20:ℝ) ≤ (((γ • τ : UpperHalfPlane))).im - τ.im := (abs_le.mp hdist).1
    have h6 : (3/2:ℝ) ≤ τ.im - (((γ • τ : UpperHalfPlane))).im := by linarith
    linarith

lemma fiber_orbit_gap (τ ζ : UpperHalfPlane) (hτ : 2 ≤ τ.im)
    (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20)
    (hjj : Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun τ) :
    (ζ : ℂ) = (τ : ℂ) - 1 ∨ (ζ : ℂ) = (τ : ℂ) ∨ (ζ : ℂ) = (τ : ℂ) + 1 := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjj
  have hdist' : ‖(((γ • τ : UpperHalfPlane)) : ℂ) - (τ : ℂ)‖ ≤ 29/20 := by
    rw [hγ]; exact h
  obtain ⟨b, hb, hbval⟩ := orbitGap τ γ hτ hdist'
  rw [hγ] at hbval
  rcases hb with hb | hb | hb
  · left; rw [hbval, hb]; push_cast; ring
  · right; left; rw [hbval, hb]; push_cast; ring
  · right; right; rw [hbval, hb]; push_cast; ring

lemma jDiff_q_bound :
    ∃ T M : ℝ, 0 < T ∧ 0 < M ∧ ∀ w : UpperHalfPlane, T ≤ w.im →
      ‖Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹‖ ≤ M := by
  obtain ⟨T, M, hT, hM, hexp⟩ := Work.Asymptotics.jInvariantFun_cusp_second
  refine ⟨T, M + 744, hT, by linarith, fun w hw => ?_⟩
  have h1 := hexp w hw
  have hqE : Work.Kernels.qParamFun w = Work.Residues.Ept w ^ 2 := by
    rw [Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]; congr 1; ring
  have hEinv : (Work.Residues.Ept w)⁻¹ ^ 2 = (Work.Kernels.qParamFun w)⁻¹ := by
    rw [hqE, ← inv_pow]
  rw [hEinv] at h1
  have hE2 : ‖Work.Residues.Ept w‖ ^ 2 = ‖Work.Kernels.qParamFun w‖ := by rw [hqE, norm_pow]
  rw [hE2] at h1
  have h2 : Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹
      = (Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744) + 744 := by ring
  rw [h2]
  have h3 : ‖Work.Kernels.qParamFun w‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, w.im_pos]
  calc ‖(Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744) + 744‖
      ≤ ‖Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744‖ + ‖(744:ℂ)‖ :=
        norm_add_le _ _
    _ ≤ M * ‖Work.Kernels.qParamFun w‖ + 744 := by rw [Complex.norm_ofNat]; linarith
    _ ≤ M + 744 := by nlinarith [hM, h3]

/-! ## The lower bound on the strip -/

lemma sphereLowerStrip (Y : ℝ) (hY : 2 ≤ Y) :
    ∃ m : ℝ, 0 < m ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ → τ.im ≤ Y →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29/20 →
        m ≤ ‖Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ‖ := by
  set R : ℝ := Real.sqrt (1 + Y^2) + 2 with hR
  set S : Set (ℂ × ℂ) := {p : ℂ × ℂ | |p.1.re| ≤ 1 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ Y ∧
    ‖p.2 - p.1‖ = 29/20} with hS
  have hcont1 : Continuous fun p : ℂ × ℂ => |p.1.re| := by fun_prop
  have hcont2 : Continuous fun p : ℂ × ℂ => p.1.im := by fun_prop
  have hcont3 : Continuous fun p : ℂ × ℂ => ‖p.2 - p.1‖ := by fun_prop
  have h : S = {p : ℂ × ℂ | |p.1.re| ≤ 1} ∩ {p : ℂ × ℂ | 2 ≤ p.1.im}
      ∩ {p : ℂ × ℂ | p.1.im ≤ Y} ∩ {p : ℂ × ℂ | ‖p.2 - p.1‖ = 29/20} := by
    ext p; simp only [hS, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  have hm : ∀ p : ℂ × ℂ, p ∈ S ↔ (|p.1.re| ≤ 1 ∧ 2 ≤ p.1.im ∧ p.1.im ≤ Y ∧
      ‖p.2 - p.1‖ = 29/20) := by
    intro p; simp only [hS, Set.mem_setOf_eq]
  have hSclosed : IsClosed S := by
    rw [h]
    exact (((isClosed_Iic.preimage hcont1).inter (isClosed_Ici.preimage hcont2)).inter
      (isClosed_Iic.preimage hcont2)).inter (isClosed_singleton.preimage hcont3)
  have hnorm1 : ∀ p : ℂ × ℂ, |p.1.re| ≤ 1 → 2 ≤ p.1.im → p.1.im ≤ Y →
      ‖p.1‖ ≤ Real.sqrt (1 + Y^2) := by
    intro p h1 h2 h3
    rw [Complex.norm_def, Complex.normSq_apply]
    apply Real.sqrt_le_sqrt
    have h8 : -(1:ℝ) ≤ p.1.re := (abs_le.mp h1).1
    have h9 : p.1.re ≤ 1 := (abs_le.mp h1).2
    nlinarith [h9, h8, h3, h2]
  have hSsub : S ⊆ Metric.closedBall (0:ℂ) R ×ˢ Metric.closedBall (0:ℂ) R := by
    intro p hp
    rw [hm] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h5 := hnorm1 p h1 h2 h3
      rw [hR]; linarith
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h5 := hnorm1 p h1 h2 h3
      have h6 : ‖p.2‖ ≤ ‖p.2 - p.1‖ + ‖p.1‖ := by
        have h7 := norm_add_le (p.2 - p.1) p.1
        rwa [sub_add_cancel] at h7
      rw [hR]; linarith
  have hScomp : IsCompact S :=
    IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0:ℂ) R).prod (isCompact_closedBall (0:ℂ) R)) hSclosed hSsub
  have hJcont : ContinuousOn jLift {z : ℂ | 0 < z.im} :=
    (jLift_diff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet).continuousOn
  have him2 : ∀ p : ℂ × ℂ, 2 ≤ p.1.im → ‖p.2 - p.1‖ = 29/20 → 0 < p.2.im := by
    intro p h2 h4
    have h5 : |p.2.im - p.1.im| ≤ 29/20 := by
      have h6 := Complex.abs_im_le_norm (p.2 - p.1)
      rw [Complex.sub_im, h4] at h6
      exact h6
    have h7 : -(29/20:ℝ) ≤ p.2.im - p.1.im := (abs_le.mp h5).1
    linarith
  have hFcont : ContinuousOn (fun p : ℂ × ℂ => ‖jLift p.2 - jLift p.1‖) S := by
    apply ContinuousOn.norm
    refine ContinuousOn.sub ?_ ?_
    · refine hJcont.comp continuous_snd.continuousOn (fun p hp => ?_)
      rw [hm] at hp
      exact him2 p hp.2.1 hp.2.2.2
    · refine hJcont.comp continuous_fst.continuousOn (fun p hp => ?_)
      rw [hm] at hp
      exact lt_of_lt_of_le (by norm_num) hp.2.1
  have hSne : S.Nonempty := by
    refine ⟨((2:ℂ) * Complex.I, (2:ℂ) * Complex.I + 29/20), ?_⟩
    rw [hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hY
    · rw [add_sub_cancel_left]; norm_num
  obtain ⟨p₀, hp₀S, hp₀min⟩ := hScomp.exists_isMinOn hSne hFcont
  have hpos : 0 < ‖jLift p₀.2 - jLift p₀.1‖ := by
    rw [hm] at hp₀S
    obtain ⟨h1, h2, h3, h4⟩ := hp₀S
    have hp1 : 0 < p₀.1.im := lt_of_lt_of_le (by norm_num) h2
    have hp2 : 0 < p₀.2.im := him2 p₀ h2 h4
    set τ' : UpperHalfPlane := ⟨p₀.1, hp1⟩ with hτ'
    set ζ' : UpperHalfPlane := ⟨p₀.2, hp2⟩ with hζ'
    by_contra hcon
    have hzero : jLift p₀.2 = jLift p₀.1 := by
      have h5 : ‖jLift p₀.2 - jLift p₀.1‖ = 0 := le_antisymm (le_of_not_gt hcon) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp h5)
    have hjj : Work.Kernels.jInvariantFun ζ' = Work.Kernels.jInvariantFun τ' := by
      have e1 : jLift p₀.2 = Work.Kernels.jInvariantFun ζ' := by
        rw [hζ']; exact jLift_of_pos hp2
      have e2 : jLift p₀.1 = Work.Kernels.jInvariantFun τ' := by
        rw [hτ']; exact jLift_of_pos hp1
      rw [e1, e2] at hzero
      exact hzero
    have hcoe : ‖(ζ' : ℂ) - (τ' : ℂ)‖ = 29/20 := by
      rw [hζ', hτ']; exact h4
    have hτim : 2 ≤ τ'.im := by rw [hτ']; exact h2
    rcases fiber_orbit_gap τ' ζ' hτim (le_of_eq hcoe) hjj with hh | hh | hh
    · have h6 : ‖(ζ' : ℂ) - (τ' : ℂ)‖ = 1 := by rw [hh]; norm_num
      rw [hcoe] at h6; norm_num at h6
    · have h6 : ‖(ζ' : ℂ) - (τ' : ℂ)‖ = 0 := by rw [hh]; norm_num
      rw [hcoe] at h6; norm_num at h6
    · have h6 : ‖(ζ' : ℂ) - (τ' : ℂ)‖ = 1 := by rw [hh]; norm_num
      rw [hcoe] at h6; norm_num at h6
  refine ⟨‖jLift p₀.2 - jLift p₀.1‖, hpos, fun τ ζ hτ hτY hζ => ?_⟩
  have hmem : ((τ : ℂ), (ζ : ℂ)) ∈ S := by
    rw [hm]
    exact ⟨le_of_lt (Work.Asymptotics.Funnel.re_abs_lt_one hτ),
      Work.Asymptotics.Funnel.im_two hτ, hτY, hζ⟩
  have hmin : (fun p : ℂ × ℂ => ‖jLift p.2 - jLift p.1‖) p₀
      ≤ (fun p : ℂ × ℂ => ‖jLift p.2 - jLift p.1‖) ((τ : ℂ), (ζ : ℂ)) := hp₀min hmem
  have e1 : jLift (ζ : ℂ) = Work.Kernels.jInvariantFun ζ := by
    simp only [jLift, UpperHalfPlane.ofComplex_apply]
  have e2 : jLift (τ : ℂ) = Work.Kernels.jInvariantFun τ := by
    simp only [jLift, UpperHalfPlane.ofComplex_apply]
  simp only at hmin
  rw [e1, e2] at hmin
  exact hmin



open Classical in
theorem sphereBound : ∃ c : ℝ, 0 < c ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
    ‖(ζ : ℂ) - (τ : ℂ)‖ = 29/20 →
      c * Real.exp (2 * Real.pi * τ.im) ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
  obtain ⟨T, M, hT, hM, hq⟩ := jDiff_q_bound
  set Y₀ : ℝ := max 4 (max (T + 2) (Real.log (8 * M) / (2 * Real.pi) + 1)) with hY₀def
  have hY0 : 2 ≤ Y₀ := le_trans (by norm_num) (le_max_left _ _)
  obtain ⟨m, hm, hmstrip⟩ := sphereLowerStrip Y₀ hY0
  have hY0T : T + 2 ≤ Y₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hY0M : Real.log (8 * M) / (2 * Real.pi) + 1 ≤ Y₀ :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨min (1/4) (m * Real.exp (-(2 * Real.pi * Y₀))), lt_min (by norm_num) (by positivity), ?_⟩
  intro τ ζ hτ hζ
  by_cases hy : τ.im ≤ Y₀
  · -- strip case
    have h1 := hmstrip τ ζ hτ hy hζ
    have h2 : m * Real.exp (-(2 * Real.pi * Y₀)) * Real.exp (2 * Real.pi * τ.im) ≤ m := by
      have h3 : 2 * Real.pi * τ.im - 2 * Real.pi * Y₀ ≤ 0 := by nlinarith [Real.pi_pos, hy]
      have h4 : Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * Y₀) ≤ 1 := Real.exp_le_one_iff.mpr h3
      have h5 : Real.exp (2 * Real.pi * τ.im - 2 * Real.pi * Y₀)
          = Real.exp (-(2 * Real.pi * Y₀)) * Real.exp (2 * Real.pi * τ.im) := by
        rw [← Real.exp_add]; ring_nf
      nlinarith [h4, h5, hm]
    calc min (1/4) (m * Real.exp (-(2 * Real.pi * Y₀))) * Real.exp (2 * Real.pi * τ.im)
        ≤ (m * Real.exp (-(2 * Real.pi * Y₀))) * Real.exp (2 * Real.pi * τ.im) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ ≤ m := h2
      _ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
          rw [norm_sub_rev]; exact h1
  · -- large case
    have hy' : Y₀ < τ.im := not_le.mp hy
    have hτT : T ≤ τ.im := by linarith [hY0T, hy']
    have hζT : T ≤ ζ.im := by
      have h1 : |ζ.im - τ.im| ≤ 29/20 := by
        have h2 := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
        rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hζ] at h2
        exact h2
      have h3 : -(29/20:ℝ) ≤ ζ.im - τ.im := (abs_le.mp h1).1
      linarith [hY0T, hy']
    have hlog : Real.log (8 * M) < 2 * Real.pi * τ.im := by
      have h1 : Real.log (8 * M) / (2 * Real.pi) < τ.im := by linarith [hY0M, hy']
      have h2 : 2 * Real.pi * (Real.log (8 * M) / (2 * Real.pi)) < 2 * Real.pi * τ.im :=
        mul_lt_mul_of_pos_left h1 (by positivity : (0:ℝ) < 2 * Real.pi)
      rwa [mul_div_cancel₀ _ (by positivity : (2:ℝ) * Real.pi ≠ 0)] at h2
    have hexp8 : 8 * M < Real.exp (2 * Real.pi * τ.im) := by
      have h1 : Real.exp (Real.log (8 * M)) < Real.exp (2 * Real.pi * τ.im) :=
        Real.exp_lt_exp.mpr hlog
      rwa [Real.exp_log (by positivity)] at h1
    have hqζ := hq ζ hζT
    have hqτ := hq τ hτT
    have hdec : Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ
        = ((Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹)
          + ((Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
            - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹)) := by ring
    have hqdiff : (1/2) * Real.exp (2 * Real.pi * τ.im)
        ≤ ‖(Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹‖ := by
      have h1 : (Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹
          = Complex.exp (-(2 * Real.pi * Complex.I * (τ:ℂ)))
            * (Complex.exp (-(2 * Real.pi * Complex.I * ((ζ:ℂ) - (τ:ℂ)))) - 1) := by
        have e1 : (Work.Kernels.qParamFun ζ)⁻¹
            = Complex.exp (-(2 * Real.pi * Complex.I * (ζ:ℂ))) := by
          rw [Work.Kernels.qParamFun, ← Complex.exp_neg]
        have e2 : (Work.Kernels.qParamFun τ)⁻¹
            = Complex.exp (-(2 * Real.pi * Complex.I * (τ:ℂ))) := by
          rw [Work.Kernels.qParamFun, ← Complex.exp_neg]
        have hsum : -(2 * Real.pi * Complex.I * (τ:ℂ))
            + -(2 * Real.pi * Complex.I * ((ζ:ℂ) - (τ:ℂ)))
            = -(2 * Real.pi * Complex.I * (ζ:ℂ)) := by ring
        rw [e1, e2, ← hsum, Complex.exp_add]
        ring
      rw [h1, norm_mul]
      have h2 : ‖Complex.exp (-(2 * Real.pi * Complex.I * (τ:ℂ)))‖
          = Real.exp (2 * Real.pi * τ.im) := by
        have e : Complex.exp (-(2 * Real.pi * Complex.I * (τ:ℂ)))
            = (Work.Kernels.qParamFun τ)⁻¹ := by
          rw [Work.Kernels.qParamFun, ← Complex.exp_neg]
        rw [e, norm_inv, Work.Asymptotics.norm_qParamFun, ← Real.exp_neg]
        congr 1
        ring
      have h3 : (1/2 : ℝ)
          ≤ ‖Complex.exp (-(2 * Real.pi * Complex.I * ((ζ:ℂ) - (τ:ℂ)))) - 1‖ := by
        have h4 : -(2 * Real.pi * Complex.I * ((ζ:ℂ) - (τ:ℂ)))
            = 2 * Real.pi * Complex.I * ((τ:ℂ) - (ζ:ℂ)) := by ring
        rw [h4]
        exact exp_circle_lower ((τ:ℂ) - (ζ:ℂ)) (by rw [norm_sub_rev]; exact hζ)
      rw [h2]
      calc (1/2) * Real.exp (2 * Real.pi * τ.im)
          = Real.exp (2 * Real.pi * τ.im) * (1/2) := by ring
        _ ≤ Real.exp (2 * Real.pi * τ.im)
              * ‖Complex.exp (-(2 * Real.pi * Complex.I * ((ζ:ℂ) - (τ:ℂ)))) - 1‖ :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    have hSdiff : ‖(Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
        - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹)‖ ≤ 2 * M := by
      have h1 : ‖(Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
          - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹)‖
          ≤ ‖Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹‖
            + ‖Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹‖ := norm_sub_le _ _
      linarith
    have hmain : (1/2) * Real.exp (2 * Real.pi * τ.im) - 2 * M
        ≤ ‖Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ‖ := by
      rw [hdec]
      have h1 : ‖((Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹)
            + ((Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
              - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹))‖
          ≥ ‖(Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹‖
            - ‖(Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
              - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹)‖ := by
        have h2 := abs_norm_sub_norm_le ((Work.Kernels.qParamFun ζ)⁻¹ - (Work.Kernels.qParamFun τ)⁻¹)
          (-((Work.Kernels.jInvariantFun ζ - (Work.Kernels.qParamFun ζ)⁻¹)
              - (Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹)))
        rw [norm_neg, sub_neg_eq_add] at h2
        exact le_trans (le_abs_self _) h2
      linarith [hqdiff, hSdiff, h1]
    have hfin : (1/4) * Real.exp (2 * Real.pi * τ.im)
        ≤ ‖Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ‖ := by
      have h4 : 2 * M ≤ (1/4) * Real.exp (2 * Real.pi * τ.im) := by linarith
      linarith [hmain, h4]
    calc min (1/4) (m * Real.exp (-(2 * Real.pi * Y₀))) * Real.exp (2 * Real.pi * τ.im)
        ≤ (1/4) * Real.exp (2 * Real.pi * τ.im) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
          rw [norm_sub_rev]; exact hfin


/-! ## The divided differences of the lift along the three zeros of `f` -/

private lemma csucc_ne (c : ℂ) : c + 1 ≠ c := by
  intro hh
  have h := congrArg (fun x : ℂ => x - c) hh
  rw [add_sub_cancel_left, sub_self] at h
  exact one_ne_zero h

private lemma cpred_ne (c : ℂ) : c - 1 ≠ c := by
  intro hh
  have h := congrArg (fun x : ℂ => x - c) hh
  have h2 : (c - 1) - c = -(1:ℂ) := by ring
  rw [h2, sub_self] at h
  exact neg_ne_zero.mpr one_ne_zero h

private lemma csucc_ne_pred (c : ℂ) : c + 1 ≠ c - 1 := by
  intro hh
  have h := congrArg (fun x : ℂ => x - c) hh
  have h2 : (c + 1) - c = (1:ℂ) := by ring
  have h3 : (c - 1) - c = -(1:ℂ) := by ring
  rw [h2, h3] at h
  norm_num at h

private lemma cpred_ne_succ (c : ℂ) : c - 1 ≠ c + 1 := by
  intro hh
  have h := congrArg (fun x : ℂ => x - c) hh
  have h2 : (c - 1) - c = -(1:ℂ) := by ring
  have h3 : (c + 1) - c = (1:ℂ) := by ring
  rw [h2, h3] at h
  norm_num at h



private lemma dslope_eq_div {g : ℂ → ℂ} {c z : ℂ} (h0 : g c = 0) (h : z ≠ c) :
    dslope g c z = g z / (z - c) := by
  rw [dslope_of_ne _ h, slope_def_module, h0, sub_zero, smul_eq_mul]
  ring

private lemma dslope_eq_zero {g : ℂ → ℂ} {c z : ℂ} (h0 : g c = 0) (hz : g z = 0) (h : z ≠ c) :
    dslope g c z = 0 := by
  rw [dslope_of_ne _ h, slope_def_module, h0, hz, sub_zero, smul_zero]

private lemma deriv_dslope_eq {g : ℂ → ℂ} {c z : ℂ} (hz : g z = 0) (h0 : g c = 0)
    (hne : z ≠ c) (hd : DifferentiableAt ℂ g z) :
    deriv (dslope g c) z = deriv g z / (z - c) := by
  have hpos : (0:ℝ) < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have heq : (dslope g c) =ᶠ[𝓝 z] fun w => g w * (w - c)⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds z hpos] with w hw
    have hlt : ‖w - z‖ < ‖z - c‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hw
    have hwc : w ≠ c := by
      intro hh
      have h1 : ‖w - c‖ = 0 := by rw [hh, sub_self, norm_zero]
      have h2 : ‖z - c‖ ≤ ‖w - z‖ := by
        calc ‖z - c‖ = ‖(z - w) + (w - c)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
          _ = ‖w - z‖ + 0 := by rw [h1, norm_sub_rev]
          _ = ‖w - z‖ := by ring
      linarith
    rw [dslope_of_ne _ hwc, slope_def_module, h0, sub_zero, smul_eq_mul]
    ring
  rw [heq.deriv_eq]
  have h1 : HasDerivAt g (deriv g z) z := hd.hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => (w - c)⁻¹) (-1 / (z - c) ^ 2) z := by
    have h3 : HasDerivAt (fun w : ℂ => w - c) 1 z := (hasDerivAt_id z).sub_const c
    have h4 : (z - c) ≠ 0 := sub_ne_zero.mpr hne
    exact h3.inv h4
  have h6 : HasDerivAt (fun w : ℂ => g w * (w - c)⁻¹)
      (deriv g z * (z - c)⁻¹ + g z * (-1 / (z - c) ^ 2)) z := h1.mul h2
  rw [h6.deriv, hz, zero_mul, add_zero, div_eq_mul_inv]

private lemma dslope3_form {g : ℂ → ℂ} {c : ℂ} (h0 : g c = 0) (h1 : g (c+1) = 0)
    (h2 : g (c-1) = 0) {z : ℂ} (hz0 : z ≠ c) (hz1 : z ≠ c + 1) (hz2 : z ≠ c - 1) :
    dslope (dslope (dslope g c) (c+1)) (c-1) z
      = g z / ((z - c) * (z - c - 1) * (z - c + 1)) := by
  have hF1 : dslope g c (c+1) = 0 := dslope_eq_zero h0 h1 (csucc_ne c)
  have hF2 : dslope g c (c-1) = 0 := dslope_eq_zero h0 h2 (cpred_ne c)
  have hG2 : dslope (dslope g c) (c+1) (c-1) = 0 := dslope_eq_zero hF1 hF2 (cpred_ne_succ c)
  have hD : dslope (dslope g c) (c+1) z = (dslope g c z) / (z - (c+1)) :=
    dslope_eq_div hF1 hz1
  have hB : dslope g c z = g z / (z - c) := dslope_eq_div h0 hz0
  rw [dslope_eq_div hG2 hz2, hD, hB,
    show z - (c+1) = z - c - 1 by ring, show z - (c-1) = z - c + 1 by ring]
  have e1 : z - c ≠ 0 := sub_ne_zero.mpr hz0
  have e2 : z - c - 1 ≠ 0 := by intro hh; apply hz1; linear_combination hh
  have e3 : z - c + 1 ≠ 0 := by intro hh; apply hz2; linear_combination hh
  field_simp
  <;> ring

private lemma dslope3_center {g : ℂ → ℂ} {c : ℂ} (h0 : g c = 0) (h1 : g (c+1) = 0)
    (h2 : g (c-1) = 0) :
    dslope (dslope (dslope g c) (c+1)) (c-1) c = - deriv g c := by
  have hF1 : dslope g c (c+1) = 0 := dslope_eq_zero h0 h1 (csucc_ne c)
  have hF2 : dslope g c (c-1) = 0 := dslope_eq_zero h0 h2 (cpred_ne c)
  have hG2 : dslope (dslope g c) (c+1) (c-1) = 0 := dslope_eq_zero hF1 hF2 (cpred_ne_succ c)
  have hG1 : dslope (dslope g c) (c+1) c = - deriv g c := by
    rw [dslope_of_ne _ (csucc_ne c).symm, slope_def_module, dslope_same g c, hF1,
      sub_zero, smul_eq_mul]
    ring
  rw [dslope_of_ne _ (cpred_ne c).symm, slope_def_module, hG1, hG2, sub_zero, smul_eq_mul]
  ring

private lemma dslope3_at_c1 {g : ℂ → ℂ} {c : ℂ} (h0 : g c = 0) (h1 : g (c+1) = 0)
    (h2 : g (c-1) = 0) (hd : DifferentiableAt ℂ g (c+1)) :
    dslope (dslope (dslope g c) (c+1)) (c-1) (c+1) = deriv g (c+1) / 2 := by
  have hF1 : dslope g c (c+1) = 0 := dslope_eq_zero h0 h1 (csucc_ne c)
  have hF2 : dslope g c (c-1) = 0 := dslope_eq_zero h0 h2 (cpred_ne c)
  have hG2 : dslope (dslope g c) (c+1) (c-1) = 0 := dslope_eq_zero hF1 hF2 (cpred_ne_succ c)
  have hG1 : dslope (dslope g c) (c+1) (c+1) = deriv g (c+1) := by
    rw [dslope_same]
    have hh := deriv_dslope_eq h1 h0 (csucc_ne c) hd
    rwa [show (c+1) - c = 1 by ring, div_one] at hh
  rw [dslope_of_ne _ (csucc_ne_pred c), slope_def_module, hG1, hG2, sub_zero,
    smul_eq_mul]
  ring

private lemma dslope3_at_cm1 {g : ℂ → ℂ} {c : ℂ} (h0 : g c = 0) (h1 : g (c+1) = 0)
    (h2 : g (c-1) = 0) (hd1 : DifferentiableAt ℂ (dslope g c) (c-1))
    (hd2 : DifferentiableAt ℂ g (c-1)) :
    dslope (dslope (dslope g c) (c+1)) (c-1) (c-1) = deriv g (c-1) / 2 := by
  have hF1 : dslope g c (c+1) = 0 := dslope_eq_zero h0 h1 (csucc_ne c)
  have hF2 : dslope g c (c-1) = 0 := dslope_eq_zero h0 h2 (cpred_ne c)
  have hder1 : deriv (dslope (dslope g c) (c+1)) (c-1)
      = deriv (dslope g c) (c-1) / ((c-1) - (c+1)) :=
    deriv_dslope_eq hF2 hF1 (cpred_ne_succ c) hd1
  have hder2 : deriv (dslope g c) (c-1) = deriv g (c-1) / ((c-1) - c) :=
    deriv_dslope_eq h2 h0 (cpred_ne c) hd2
  rw [dslope_same, hder1, hder2]
  ring

/-! ## The disc lower bound for an abstract holomorphic function -/

private lemma disc_lower {x : ℂ} {f : ℂ → ℂ} {c : ℝ} (hcpos : 0 < c)
    (hfx : f x = 0) (hf1 : f (x + 1) = 0) (hfm1 : f (x - 1) = 0)
    (hfdiff : DifferentiableOn ℂ f (Metric.ball x 2))
    (hne : ∀ z ∈ Metric.closedBall x (29/20),
      dslope (dslope (dslope f x) (x + 1)) (x - 1) z ≠ 0)
    (hbd : ∀ z ∈ Metric.sphere x (29/20), c ≤ ‖f z‖) :
    ∀ z ∈ Metric.closedBall x (29/20),
      (c / 9) * ‖(z - x) * (z - x - 1) * (z - x + 1)‖ ≤ ‖f z‖ := by
  set h : ℂ → ℂ := dslope (dslope (dslope f x) (x + 1)) (x - 1) with hhdef
  have hne' : ∀ z ∈ Metric.closedBall x (29/20), h z ≠ 0 := by
    intro z hz
    rw [hhdef]
    exact hne z hz
  have hball : Metric.ball x 2 ∈ 𝓝 x := Metric.ball_mem_nhds x (by norm_num)
  have hmem1 : Metric.ball x 2 ∈ 𝓝 (x + 1) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; norm_num)
  have hmem2 : Metric.ball x 2 ∈ 𝓝 (x - 1) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; norm_num)
  have hd1 : DifferentiableOn ℂ (dslope f x) (Metric.ball x 2) :=
    (Complex.differentiableOn_dslope hball).mpr hfdiff
  have hd2 : DifferentiableOn ℂ (dslope (dslope f x) (x+1)) (Metric.ball x 2) :=
    (Complex.differentiableOn_dslope hmem1).mpr hd1
  have hd3 : DifferentiableOn ℂ h (Metric.ball x 2) := by
    rw [hhdef]
    exact (Complex.differentiableOn_dslope hmem2).mpr hd2
  have hF3 : ∀ z ∈ Metric.ball x 2, z ≠ x → z ≠ x + 1 → z ≠ x - 1 →
      h z = f z / ((z - x) * (z - x - 1) * (z - x + 1)) := by
    intro z hz h0 h1 h2
    rw [hhdef]
    exact dslope3_form hfx hf1 hfm1 h0 h1 h2
  have hP : ∀ z ∈ Metric.ball x 2, h z * ((z - x) * (z - x - 1) * (z - x + 1)) = f z := by
    intro z hz
    by_cases hzx : z = x
    · rw [hzx, show (x - x) * (x - x - 1) * (x - x + 1) = 0 by ring, mul_zero, hfx]
    · by_cases hzx1 : z = x + 1
      · rw [hzx1, show (x + 1 - x) * (x + 1 - x - 1) * (x + 1 - x + 1) = 0 by ring, mul_zero, hf1]
      · by_cases hzxm1 : z = x - 1
        · rw [hzxm1, show (x - 1 - x) * (x - 1 - x - 1) * (x - 1 - x + 1) = 0 by ring, mul_zero, hfm1]
        · rw [hF3 z hz hzx hzx1 hzxm1]
          have hPne : (z - x) * (z - x - 1) * (z - x + 1) ≠ 0 := by
            rw [show z - x - 1 = z - (x+1) by ring, show z - x + 1 = z - (x-1) by ring]
            exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hzx) (sub_ne_zero.mpr hzx1))
              (sub_ne_zero.mpr hzxm1)
          rw [div_mul_cancel₀ _ hPne]
  have hbound : ∀ z ∈ Metric.sphere x (29/20), ‖(1:ℂ) / h z‖ ≤ 9 / c := by
    intro z hz
    have hznorm : ‖z - x‖ = 29/20 := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hz
    have hzball : z ∈ Metric.ball x 2 := by
      rw [Metric.mem_ball, dist_eq_norm, hznorm]; norm_num
    have hzne : z ≠ x := by intro hh; rw [hh, sub_self, norm_zero] at hznorm; norm_num at hznorm
    have hze1 : z ≠ x + 1 := by
      intro hh
      have h2 : ‖(x+1) - x‖ = 29/20 := by rw [← hh]; exact hznorm
      rw [show x + 1 - x = 1 by ring, norm_one] at h2; norm_num at h2
    have hzem1 : z ≠ x - 1 := by
      intro hh
      have h2 : ‖(x-1) - x‖ = 29/20 := by rw [← hh]; exact hznorm
      rw [show x - 1 - x = -1 by ring, norm_neg, norm_one] at h2; norm_num at h2
    have hF := hF3 z hzball hzne hze1 hzem1
    have hPbound : ‖(z - x) * (z - x - 1) * (z - x + 1)‖ ≤ 9 := by
      have h2 : ‖z - x - 1‖ ≤ 49/20 := by
        have h4 : ‖(z - x) - 1‖ ≤ ‖z - x‖ + 1 := by
          have h5 := norm_sub_le (z - x) (1:ℂ)
          rwa [norm_one] at h5
        rw [hznorm] at h4; linarith
      have h3 : ‖z - x + 1‖ ≤ 49/20 := by
        have h4 : ‖z - x + 1‖ ≤ ‖z - x‖ + 1 := by
          have h5 := norm_add_le (z - x) (1:ℂ)
          rwa [norm_one] at h5
        rw [hznorm] at h4; linarith
      rw [norm_mul, norm_mul, hznorm]
      have h5 : (29/20:ℝ) * (49/20) * (49/20) ≤ 9 := by norm_num
      nlinarith [h2, h3, norm_nonneg (z - x - 1), norm_nonneg (z - x + 1)]
    have hhge : c / 9 ≤ ‖h z‖ := by
      have hPpos : 0 < ‖(z - x) * (z - x - 1) * (z - x + 1)‖ := by
        rw [norm_mul, norm_mul]
        refine mul_pos (mul_pos ?_ ?_) ?_
        · exact norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
        · rw [show z - x - 1 = z - (x+1) by ring]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hze1)
        · rw [show z - x + 1 = z - (x-1) by ring]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hzem1)
      rw [hF, norm_div, le_div_iff₀ hPpos]
      calc (c / 9) * ‖(z - x) * (z - x - 1) * (z - x + 1)‖
          ≤ (c / 9) * 9 := mul_le_mul_of_nonneg_left hPbound (by positivity)
        _ = c := by ring
        _ ≤ ‖f z‖ := hbd z hz
    rw [norm_div, norm_one]
    have hpos1 : 0 < ‖h z‖ := lt_of_lt_of_le (by positivity) hhge
    rw [div_le_div_iff₀ hpos1 hcpos]
    linarith [hhge]
  have hgd : DifferentiableOn ℂ (fun z => (1:ℂ) / h z) (Metric.ball x (29/20)) :=
    (differentiableOn_const (1:ℂ)).div (hd3.mono (Metric.ball_subset_ball (by norm_num)))
      (fun z hz => hne' z (Metric.ball_subset_closedBall hz))
  have hgc : ContinuousOn (fun z => (1:ℂ) / h z) (closure (Metric.ball x (29/20))) := by
    rw [closure_ball x (by norm_num : (29/20:ℝ) ≠ 0)]
    refine continuousOn_const.div ((hd3.mono ?_).continuousOn) (fun z hz => hne' z hz)
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    linarith
  have hmax : ∀ z ∈ Metric.closedBall x (29/20), ‖(1:ℂ) / h z‖ ≤ 9 / c := by
    intro z hz
    have hcl : z ∈ closure (Metric.ball x (29/20)) := by
      rw [closure_ball x (by norm_num : (29/20:ℝ) ≠ 0)]
      exact hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) ⟨hgd, hgc⟩
      (fun w hw => hbound w (Metric.frontier_ball_subset_sphere hw)) hcl
  intro z hz
  have hPz := hP z (Metric.closedBall_subset_ball (by norm_num) hz)
  have hmaxz := hmax z hz
  have hc9 : c / 9 ≤ ‖h z‖ := by
    have h1 : ‖(1:ℂ)/h z‖ = 1/‖h z‖ := by rw [norm_div, norm_one]
    rw [h1] at hmaxz
    have hpos1 : 0 < ‖h z‖ := norm_pos_iff.mpr (hne' z hz)
    rw [div_le_div_iff₀ hpos1 hcpos] at hmaxz
    linarith
  calc (c / 9) * ‖(z - x) * (z - x - 1) * (z - x + 1)‖
      ≤ ‖h z‖ * ‖(z - x) * (z - x - 1) * (z - x + 1)‖ :=
        mul_le_mul_of_nonneg_right hc9 (norm_nonneg _)
    _ = ‖f z‖ := by rw [← norm_mul, hPz]

/-! ## The main theorem -/

set_option maxHeartbeats 4000000 in
theorem divisorLowerDisc : ∃ c : ℝ, 0 < c ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 → c * Real.exp (2 * Real.pi * τ.im) * ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
  obtain ⟨c₁, hc₁, hsphere⟩ := sphereBound
  refine ⟨c₁ / 9, by positivity, ?_⟩
  intro τ ζ hτ hζdist
  set x : ℂ := (τ : ℂ) with hx
  set f : ℂ → ℂ := fun z => jLift z - Work.Kernels.jInvariantFun τ with hfdef
  have hxim2 : 2 ≤ x.im := by rw [hx, UpperHalfPlane.coe_im]; exact Funnel.im_two hτ
  have hxim : 0 < x.im := lt_of_lt_of_le (by norm_num) hxim2
  have hjx : jLift x = Work.Kernels.jInvariantFun τ := by
    rw [hx]; simp only [jLift, UpperHalfPlane.ofComplex_apply]
  have hfx0 : f x = 0 := by simp only [hfdef, hjx, sub_self]
  have hfx1 : f (x+1) = 0 := by simp only [hfdef, jLift_periodic x hxim, hjx, sub_self]
  have hx1im : 0 < (x-1).im := by
    have h3 : (x-1).im = x.im := by rw [Complex.sub_im]; simp
    linarith
  have hfxm1 : f (x-1) = 0 := by
    have h : jLift (x-1) = jLift x := by
      have h2 := jLift_periodic (x-1) hx1im
      rw [show (x-1)+1 = x by ring] at h2
      exact h2.symm
    simp only [hfdef, h, hjx, sub_self]
  have hmem1 : Metric.ball x 2 ∈ 𝓝 (x + 1) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; norm_num)
  have hmem2 : Metric.ball x 2 ∈ 𝓝 (x - 1) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; norm_num)
  have hball_sub : Metric.ball x 2 ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h2 : ‖z - x‖ < 2 := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    have h3 : |z.im - x.im| ≤ ‖z - x‖ := by
      have h4 := Complex.abs_im_le_norm (z - x)
      rwa [Complex.sub_im] at h4
    have h4m : -(‖z - x‖) ≤ z.im - x.im := (abs_le.mp h3).1
    show 0 < z.im
    linarith
  have hfdiff : DifferentiableOn ℂ f (Metric.ball x 2) := by
    rw [hfdef]
    exact (jLift_diff.mono hball_sub).sub_const (Work.Kernels.jInvariantFun τ)
  have hzpos_of : ∀ z ∈ Metric.closedBall x (29/20), 0 < z.im := by
    intro z hz
    have h1 : ‖z - x‖ ≤ 29/20 := by rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have h2 : |z.im - x.im| ≤ ‖z - x‖ := by
      have h3 := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im] at h3
      exact h3
    linarith [(abs_le.mp (le_trans h2 h1)).1, hxim2]
  have hne : ∀ z ∈ Metric.closedBall x (29/20),
      dslope (dslope (dslope f x) (x + 1)) (x - 1) z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z x with rfl | hz0
    · rw [dslope3_center hfx0 hfx1 hfxm1]
      have h1 : deriv f x = deriv jLift x := by
        rw [hfdef]
        exact deriv_sub_const (Work.Kernels.jInvariantFun τ)
      rw [h1]
      exact neg_ne_zero.mpr (deriv_jLift_ne_zero τ (Funnel.im_two hτ))
    · rcases eq_or_ne z (x+1) with rfl | hz1
      · rw [dslope3_at_c1 hfx0 hfx1 hfxm1 (hfdiff.differentiableAt hmem1)]
        refine div_ne_zero ?_ (by norm_num)
        have h1 : deriv f (x+1) = deriv jLift (x+1) := by
          rw [hfdef]
          exact deriv_sub_const (Work.Kernels.jInvariantFun τ)
        rw [h1]
        have h2 : deriv jLift (x+1) ≠ 0 := by
          have h3 := deriv_jLift_ne_zero ((1:ℝ) +ᵥ τ) (by
            rw [UpperHalfPlane.vadd_im]; exact Funnel.im_two hτ)
          rwa [show ((((1:ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = x + 1 by
            rw [UpperHalfPlane.coe_vadd, hx]; push_cast; ring] at h3
        exact h2
      · rcases eq_or_ne z (x-1) with rfl | hzm1
        · have hd1' : DifferentiableOn ℂ (dslope f x) (Metric.ball x 2) :=
            (Complex.differentiableOn_dslope (Metric.ball_mem_nhds x (by norm_num))).mpr hfdiff
          rw [dslope3_at_cm1 hfx0 hfx1 hfxm1
            (hd1'.differentiableAt hmem2) (hfdiff.differentiableAt hmem2)]
          refine div_ne_zero ?_ (by norm_num)
          have h1 : deriv f (x-1) = deriv jLift (x-1) := by
            rw [hfdef]
            exact deriv_sub_const (Work.Kernels.jInvariantFun τ)
          rw [h1]
          have h2 : deriv jLift (x-1) ≠ 0 := by
            have h3 := deriv_jLift_ne_zero ((-1:ℝ) +ᵥ τ) (by
              rw [UpperHalfPlane.vadd_im]; exact Funnel.im_two hτ)
            rwa [show ((((-1:ℝ) +ᵥ τ : UpperHalfPlane)) : ℂ) = x - 1 by
              rw [UpperHalfPlane.coe_vadd, hx]; push_cast; ring] at h3
          exact h2
        · rw [dslope3_form hfx0 hfx1 hfxm1 hz0 hz1 hzm1]
          refine div_ne_zero ?_ ?_
          · intro hfz
            have hzpos : 0 < z.im := hzpos_of z hz
            have hjj : Work.Kernels.jInvariantFun ⟨z, hzpos⟩ = Work.Kernels.jInvariantFun τ := by
              have e : Work.Kernels.jInvariantFun ⟨z, hzpos⟩ - Work.Kernels.jInvariantFun τ = 0 := by
                have e2 : f z = jLift z - Work.Kernels.jInvariantFun τ := by rw [hfdef]
                have e3 : jLift z = Work.Kernels.jInvariantFun ⟨z, hzpos⟩ := jLift_of_pos hzpos
                rw [← e3, ← e2, hfz]
              exact sub_eq_zero.mp e
            have hdist : ‖((⟨z, hzpos⟩ : UpperHalfPlane) : ℂ) - (τ : ℂ)‖ ≤ 29/20 := by
              have h1 : ‖z - x‖ ≤ 29/20 := by
                rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
              rw [hx] at h1
              simpa using h1
            rcases fiber_orbit_gap τ ⟨z, hzpos⟩ (Funnel.im_two hτ) hdist hjj with hh | hh | hh
            · apply hzm1
              rw [show z = (τ : ℂ) - 1 by simpa using hh, hx]
            · apply hz0
              rw [show z = (τ : ℂ) by simpa using hh, hx]
            · apply hz1
              rw [show z = (τ : ℂ) + 1 by simpa using hh, hx]
          · rw [show z - x - 1 = z - (x+1) by ring, show z - x + 1 = z - (x-1) by ring]
            exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz0) (sub_ne_zero.mpr hz1))
              (sub_ne_zero.mpr hzm1)
  have hbd : ∀ z ∈ Metric.sphere x (29/20), c₁ * Real.exp (2 * Real.pi * τ.im) ≤ ‖f z‖ := by
    intro z hz
    have hznorm : ‖z - x‖ = 29/20 := by
      rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hz
    have hzpos : 0 < z.im := by
      have h1 : |z.im - x.im| ≤ ‖z - x‖ := by
        have h3 := Complex.abs_im_le_norm (z - x)
        rw [Complex.sub_im] at h3
        exact h3
      rw [hznorm] at h1
      linarith [(abs_le.mp h1).1, hxim2]
    have hsp := hsphere τ ⟨z, hzpos⟩ hτ (by rw [← hx]; simpa using hznorm)
    have hfz : f z = jLift z - Work.Kernels.jInvariantFun τ := by rw [hfdef]
    have hjz : jLift z = Work.Kernels.jInvariantFun ⟨z, hzpos⟩ := jLift_of_pos hzpos
    rw [hfz, hjz, norm_sub_rev]
    exact hsp
  have hmain := disc_lower (x := x) (f := f) (c := c₁ * Real.exp (2 * Real.pi * τ.im))
    (by positivity) hfx0 hfx1 hfxm1 hfdiff hne hbd
  have hzballζ : (ζ:ℂ) ∈ Metric.closedBall x (29/20) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hζdist
  have hz := hmain (ζ:ℂ) hzballζ
  have hfζ : f (ζ:ℂ) = Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ := by
    change jLift (ζ : ℂ) - Work.Kernels.jInvariantFun τ
      = Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ
    rw [jLift_of_pos ζ.im_pos]
  have hPn : ((ζ:ℂ) - (τ:ℂ)) * ((ζ:ℂ) - ((τ:ℂ) - 1)) * ((ζ:ℂ) - ((τ:ℂ) + 1))
      = ((ζ:ℂ) - x) * ((ζ:ℂ) - x - 1) * ((ζ:ℂ) - x + 1) := by rw [hx]; ring
  rw [hPn]
  calc c₁ / 9 * Real.exp (2 * Real.pi * τ.im) * ‖((ζ:ℂ) - x) * ((ζ:ℂ) - x - 1) * ((ζ:ℂ) - x + 1)‖
      = (c₁ * Real.exp (2 * Real.pi * τ.im) / 9) * ‖((ζ:ℂ) - x) * ((ζ:ℂ) - x - 1) * ((ζ:ℂ) - x + 1)‖ := by ring
    _ ≤ ‖f (ζ:ℂ)‖ := hz
    _ = ‖Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ‖ := by rw [hfζ]
    _ = ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := norm_sub_rev _ _

end

end Work.Asymptotics.SpikeCircle
