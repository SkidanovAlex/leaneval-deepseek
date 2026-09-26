import Mathlib
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.E_aux
import Submission.Work.Asymptotics.CuspDecay.j_annulus_lower
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Asymptotics.EJL.low_height_j
import Submission.Work.Asymptotics.EJL.exp_bound_of_im_nonneg

noncomputable section
set_option maxHeartbeats 1000000
open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Manifold

namespace Work.Asymptotics.EjdiffAux
open Work.Asymptotics.CuspDecay
open Work.Kernels

/-- `F u = j u - (q u)⁻¹ - 744`, the remainder in the cusp expansion of `j`. -/
def jResid (u : ℍ) : ℂ := jInvariantFun u - (qParamFun u)⁻¹ - 744

/-- The lift of `jResid` to `ℂ` (via `UpperHalfPlane.ofComplex`). -/
def jResidLift (z : ℂ) : ℂ := jResid (UpperHalfPlane.ofComplex z)

lemma jResidLift_ofComplex (z : ℂ) (hz : 0 < z.im) :
    jResidLift z = jResid ⟨z, hz⟩ := by
  unfold jResidLift
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma jResidLift_of_self (u : ℍ) : jResidLift (u : ℂ) = jResid u := by
  unfold jResidLift
  rw [UpperHalfPlane.ofComplex_apply]

/-- `jResid` is invariant under integer translations. -/
lemma jResid_vadd_int (k : ℤ) (u : ℍ) : jResid ((k : ℝ) +ᵥ u) = jResid u := by
  simp only [jResid, jInvariantFun_vadd_int, qParamFun_vadd_int]

lemma jResidLift_differentiableOn :
    DifferentiableOn ℂ jResidLift {z : ℂ | 0 < z.im} := by
  have hDne : ∀ w : ℍ, DeltaFun w ≠ 0 := fun w => by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero w
  have hj : MDiff jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant) hDne
  have hq : MDiff (fun w : ℍ => (qParamFun w)⁻¹) := by
    have h1 : MDiff qParamFun := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have hg : DifferentiableOn ℂ
          (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) {z : ℂ | 0 < z.im} :=
        (by fun_prop : Differentiable ℂ
          (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))).differentiableOn
      refine hg.congr (fun z hz => ?_)
      simp only [Function.comp_apply, qParamFun_eq_exp]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact h1.inv fun w => Complex.exp_ne_zero _
  have hF : MDiff (fun w : ℍ => jInvariantFun w - (qParamFun w)⁻¹ - 744) :=
    (hj.sub hq).sub mdifferentiable_const
  exact (UpperHalfPlane.mdifferentiable_iff).mp hF

/-- **Cauchy's estimate for the derivative of the lift.** -/
lemma jResidLift_deriv_bound {C : ℝ} (hC : 0 < C)
    (hbd : ∀ u : ℍ, 1 ≤ u.im → ‖jResid u‖ ≤ C * ‖qParamFun u‖) :
    ∀ z : ℂ, 3 / 2 ≤ z.im →
      ‖deriv jResidLift z‖ ≤ 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
  intro z hz
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hball : Metric.ball z (1 / 2) ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
    rw [Complex.sub_im] at h3
    show (0 : ℝ) < w.im
    linarith
  have hcl : closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hw1 := Metric.closure_ball_subset_closedBall hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw1
    have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
    rw [Complex.sub_im] at h3
    show (0 : ℝ) < w.im
    linarith
  have hdiff : DiffContOnCl ℂ jResidLift (Metric.ball z (1 / 2)) :=
    ⟨jResidLift_differentiableOn.mono hball,
      jResidLift_differentiableOn.continuousOn.mono hcl⟩
  have hsphere : ∀ w ∈ Metric.sphere z (1 / 2),
      ‖jResidLift w‖ ≤ C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
    intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have him : 1 ≤ w.im := by
      have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
      rw [Complex.sub_im] at h3
      linarith
    have hwpos : 0 < w.im := by linarith
    rw [jResidLift_ofComplex w hwpos]
    have h1 := hbd ⟨w, hwpos⟩ him
    rw [norm_qParamFun_eq_exp] at h1
    have hwk : z.im - 1 / 2 ≤ w.im := by
      have habs : |(w - z).im| ≤ 1 / 2 := by rw [← hw]; exact Complex.abs_im_le_norm _
      rw [Complex.sub_im, abs_le] at habs
      linarith [habs.1]
    have hexp : Real.exp (-(2 * Real.pi * w.im))
        ≤ Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hwk]
    calc ‖jResid (⟨w, hwpos⟩ : ℍ)‖ ≤ C * Real.exp (-(2 * Real.pi * w.im)) := h1
      _ ≤ C * (Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) :=
          mul_le_mul_of_nonneg_left hexp hC.le
      _ = C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by ring
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff hsphere
  rw [div_eq_mul_inv] at hmain
  calc ‖deriv jResidLift z‖
      ≤ (C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) * (1 / 2)⁻¹ := hmain
    _ = 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by norm_num; ring

/-- **Mean-value bound for the lift.** -/
lemma jResidLift_mvt {C : ℝ} (hC : 0 < C)
    (hbd : ∀ u : ℍ, 1 ≤ u.im → ‖jResid u‖ ≤ C * ‖qParamFun u‖)
    (a b : ℂ) (ha : 3 / 2 ≤ a.im) (hb : 3 / 2 ≤ b.im) :
    ‖jResidLift a - jResidLift b‖
      ≤ 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * min a.im b.im)) * ‖a - b‖ := by
  set m : ℝ := min a.im b.im with hm
  have hm32 : 3 / 2 ≤ m := le_min ha hb
  have hconv : Convex ℝ {w : ℂ | m ≤ w.im} := by
    intro x hx y hy p q hp hq hpq
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    nlinarith
  have hdiff : ∀ w ∈ {w : ℂ | m ≤ w.im}, DifferentiableAt ℂ jResidLift w := by
    intro w hw
    have hwm : m ≤ w.im := hw
    have hwpos : 0 < w.im := by linarith
    exact jResidLift_differentiableOn.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simpa using hwpos))
  have hbd' : ∀ w ∈ {w : ℂ | m ≤ w.im},
      ‖deriv jResidLift w‖ ≤ 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * m)) := by
    intro w hw
    have hwm : m ≤ w.im := hw
    have h := jResidLift_deriv_bound hC hbd w (by linarith)
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hwm])
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd' hconv (x := b) (y := a)
    (by simpa [hm] using min_le_right a.im b.im) (by simpa [hm] using min_le_left a.im b.im)
  calc ‖jResidLift a - jResidLift b‖
      ≤ 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * m)) * ‖a - b‖ := hmain
    _ = 2 * C * Real.exp Real.pi * Real.exp (-(2 * Real.pi * min a.im b.im)) * ‖a - b‖ := by
        rw [hm]

/-- The `k`-shift of the exponential factor does not change its modulus. -/
lemma norm_one_sub_exp_neg_sub_int (z : ℂ) (k : ℤ) :
    ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (z - (k : ℂ))))‖
      = ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * z))‖ := by
  have h : -(2 * (Real.pi : ℂ) * Complex.I * (z - (k : ℂ)))
      = -(2 * (Real.pi : ℂ) * Complex.I * z) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `jResidLift` at `u + m` (an integer translate) is `jResid u`. -/
lemma jResidLift_add_int (u : ℍ) (m : ℤ) : jResidLift ((u : ℂ) + (m : ℂ)) = jResid u := by
  have him : 0 < ((u : ℂ) + (m : ℂ)).im := by
    rw [Complex.add_im]; simp [u.im_pos]
  rw [jResidLift_ofComplex _ him]
  have hcoe : (((⟨(u : ℂ) + (m : ℂ), him⟩ : ℍ)) : ℂ) = ((((m : ℝ) +ᵥ u : ℍ)) : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  have h : (⟨(u : ℂ) + (m : ℂ), him⟩ : ℍ) = ((m : ℝ) +ᵥ u) := UpperHalfPlane.ext hcoe
  rw [h, jResid_vadd_int]

/-- **The `q`-difference computed exactly.** -/
lemma norm_inv_q_sub (τ σ : ℍ) (k : ℤ) (hσre : σ.re = 0) :
    ‖(qParamFun τ)⁻¹ - (qParamFun σ)⁻¹‖
      = Real.exp (2 * Real.pi * σ.im)
        * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖ := by
  have hσcoe : (σ : ℂ) = (σ.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.mul_re, hσre]
    · simp [Complex.mul_im]
  have hA : (qParamFun τ)⁻¹ = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))) := by
    rw [qParamFun_eq_exp, ← Complex.exp_neg]
  have hB : (qParamFun σ)⁻¹ = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ))) := by
    rw [qParamFun_eq_exp, ← Complex.exp_neg]
  have hw1 : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))) := by
    have h : -(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ) - (k : ℂ)))
        = -(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))
          + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hA, hB, hw1]
  set B : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ))) with hBdef
  set Cc : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))) with hCdef
  have hfact : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))) = B * Cc := by
    rw [hBdef, hCdef, ← Complex.exp_add]
    congr 1
    ring
  have hBnorm : ‖B‖ = Real.exp (2 * Real.pi * σ.im) := by
    rw [hBdef, Complex.norm_exp]
    congr 1
    rw [hσcoe]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hfact]
  have hfac2 : B * Cc - B = B * (Cc - 1) := by ring
  rw [hfac2, norm_mul, hBnorm, norm_sub_rev Cc 1]

/-- **The target's left hand side in terms of the `q`-difference.** -/
lemma exp_im_mul_norm_one_sub_exp (τ σ : ℍ) :
    Real.exp (2 * Real.pi * τ.im)
        * ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))‖
      = Real.exp (2 * Real.pi * σ.im)
        * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ))))‖ := by
  set x : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)) with hx
  have hfac : 1 - Complex.exp x = -Complex.exp x * (1 - Complex.exp (-x)) := by
    rw [Complex.exp_neg]
    field_simp
    ring
  have hnx : ‖1 - Complex.exp x‖
      = Real.exp (-(2 * Real.pi * (τ.im - σ.im))) * ‖1 - Complex.exp (-x)‖ := by
    rw [hfac, norm_mul, norm_neg, Complex.norm_exp]
    have hre : x.re = -(2 * Real.pi * (τ.im - σ.im)) := by
      rw [hx]
      norm_num [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    rw [hre]
  calc Real.exp (2 * Real.pi * τ.im) * ‖1 - Complex.exp x‖
      = Real.exp (2 * Real.pi * τ.im)
          * (Real.exp (-(2 * Real.pi * (τ.im - σ.im))) * ‖1 - Complex.exp (-x)‖) := by rw [hnx]
    _ = Real.exp (2 * Real.pi * σ.im) * ‖1 - Complex.exp (-x)‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- The left hand side of the target with the `k`-translate inserted. -/
lemma lhs_eq (τ σ : ℍ) (k : ℤ) :
    Real.exp (2 * Real.pi * τ.im)
        * ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))‖
      = Real.exp (2 * Real.pi * σ.im)
        * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
            * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖ := by
  rw [exp_im_mul_norm_one_sub_exp]
  congr 1
  have h : (τ : ℂ) - (σ : ℂ) = ((τ : ℂ) - (σ : ℂ) - (k : ℂ)) + (k : ℂ) := by ring
  rw [h, norm_one_sub_exp_neg_sub_int]


/-- **The `q`-cleared difference identity.** -/
lemma qmul_jdiff (τ σ : ℍ) (k : ℤ) :
    qParamFun σ * (jInvariantFun τ - jInvariantFun σ)
      = Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
            * ((τ : ℂ) - (σ : ℂ) - (k : ℂ)))) - 1)
        + (Psi τ - Psi ((k : ℝ) +ᵥ σ)) := by
  have hkey : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)) := by
    rw [← Complex.exp_add]
    have h2 : 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)
        + -(2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ) - (k : ℂ)))
        = 2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)
          + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [Psi_vadd_int k σ, Psi_apply, Psi_apply, qParamFun_eq_exp (u := τ),
    qParamFun_eq_exp (u := σ), ← hkey]
  ring

/-! ## Explicit exponential bounds -/

/-- `e^x ≥ 2.7182818283^m (1+r)` when `x ≥ m + r`, `r ≥ 0`. -/
lemma exp_ge_pow_mul (x r : ℝ) (m : ℕ) (hx : (m : ℝ) + r ≤ x) (hr : 0 ≤ r) :
    (2.7182818283 : ℝ) ^ m * (1 + r) ≤ Real.exp x := by
  have hx' : Real.exp ((m : ℝ) + r) ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hsplit : Real.exp ((m : ℝ) + r) = Real.exp (m : ℝ) * Real.exp r := Real.exp_add _ _
  have hpow : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [show (m : ℝ) = (m : ℕ) * 1 by push_cast; ring, Real.exp_nat_mul]
  have h1 : (2.7182818283 : ℝ) ^ m ≤ (Real.exp 1) ^ m :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) m
  have h2 : 1 + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h3 : (2.7182818283 : ℝ) ^ m * (1 + r) ≤ (Real.exp 1) ^ m * Real.exp r :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  calc (2.7182818283 : ℝ) ^ m * (1 + r) ≤ (Real.exp 1) ^ m * Real.exp r := h3
    _ = Real.exp ((m : ℝ) + r) := by rw [← hpow, ← hsplit]
    _ ≤ Real.exp x := hx'

lemma exp_two_pi_ge : (515 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have hπ : (6 : ℝ) + 0.28 ≤ 2 * Real.pi := by
    have : (6 : ℝ) + 0.28 = 6.28 := by norm_num
    rw [this]; linarith [Real.pi_gt_d20]
  have h := exp_ge_pow_mul (2 * Real.pi) 0.28 6 hπ (by norm_num)
  exact le_trans (by norm_num) h

lemma exp_pi_ge : (22 : ℝ) ≤ Real.exp Real.pi := by
  have hπ : (3 : ℝ) + 0.14 ≤ Real.pi := by
    have : (3 : ℝ) + 0.14 = 3.14 := by norm_num
    rw [this]; linarith [Real.pi_gt_d20]
  have h := exp_ge_pow_mul Real.pi 0.14 3 hπ (by norm_num)
  exact le_trans (by norm_num) h

lemma exp_three_pi_ge : (11000 : ℝ) ≤ Real.exp (3 * Real.pi) := by
  have hπ : (9 : ℝ) + 0.42 ≤ 3 * Real.pi := by
    have : (9 : ℝ) + 0.42 = 9.42 := by norm_num
    rw [this]; linarith [Real.pi_gt_d20]
  have h := exp_ge_pow_mul (3 * Real.pi) 0.42 9 hπ (by norm_num)
  exact le_trans (by norm_num) h

lemma exp_four_pi_ge : (100000 : ℝ) ≤ Real.exp (4 * Real.pi) := by
  have hπ : (12 : ℝ) + 0.56 ≤ 4 * Real.pi := by
    have : (12 : ℝ) + 0.56 = 12.56 := by norm_num
    rw [this]; linarith [Real.pi_gt_d20]
  have h := exp_ge_pow_mul (4 * Real.pi) 0.56 12 hπ (by norm_num)
  exact le_trans (by norm_num) h

/-- The numerical comparison used in the mean-value regime. -/
lemma mvt_numeric : (128 : ℝ) * 10 ^ 7 ≤ 252 * Real.exp (5 * Real.pi) := by
  have h1 := exp_two_pi_ge
  have h2 := exp_pi_ge
  have hsplit : Real.exp (5 * Real.pi)
      = Real.exp (2 * Real.pi) * Real.exp (2 * Real.pi) * Real.exp Real.pi := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hsplit]
  nlinarith [h1, h2]

/-- The numerical comparison used in the pointwise regime `t < 3/2`. -/
lemma pointwise_numeric :
    64 * 10 ^ 7 * (Real.exp (-(4 * Real.pi)) + Real.exp (-(2 * Real.pi)))
      ≤ 63 * (Real.exp (4 * Real.pi) - Real.exp (3 * Real.pi)) := by
  have h4 := exp_four_pi_ge
  have h2 := exp_two_pi_ge
  have h3 := exp_three_pi_ge
  have hp := exp_pi_ge
  have he4 : Real.exp (-(4 * Real.pi)) ≤ 1 / 100000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h4
  have he2 : Real.exp (-(2 * Real.pi)) ≤ 1 / 500 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (le_trans (by norm_num) h2)
  have hd : 231000 ≤ Real.exp (4 * Real.pi) - Real.exp (3 * Real.pi) := by
    have hfac : Real.exp (4 * Real.pi) = Real.exp (3 * Real.pi) * Real.exp Real.pi := by
      rw [← Real.exp_add]; congr 1; ring
    have h21 : (21 : ℝ) ≤ Real.exp Real.pi - 1 := by linarith [hp]
    have hmul := mul_le_mul_of_nonneg_right h21 (le_of_lt (Real.exp_pos (3 * Real.pi)))
    rw [hfac]
    nlinarith [h3, hmul, Real.exp_pos (3 * Real.pi)]
  nlinarith [he4, he2, hd]

/-! ## Numerical scalar consequences -/

/-- `‖A‖ - ‖B‖ ≤ ‖A + B‖`. -/
lemma norm_sub_le_norm_add (A B : ℂ) : ‖A‖ - ‖B‖ ≤ ‖A + B‖ := by
  have h := norm_add_le (A + B) (-B)
  have h2 : A + B + -B = A := by ring
  rw [h2, norm_neg] at h
  linarith

/-- The scalar comparison used in the mean-value regime. -/
lemma mvt_scalar (s : ℝ) (hs : 3 / 2 ≤ s) :
    (2 : ℝ) * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * s))
      ≤ (63 / 64) * (4 * Real.exp (2 * Real.pi * s)) := by
  have h1 : (32 : ℝ) * 10 ^ 7 ≤ 63 * Real.exp (5 * Real.pi) := by linarith [mvt_numeric]
  have h2 : (63 : ℝ) * Real.exp (5 * Real.pi) * Real.exp Real.pi
      = 63 * Real.exp (6 * Real.pi) := by
    rw [mul_assoc, ← Real.exp_add]; ring
  have h3 : Real.exp (6 * Real.pi) ≤ Real.exp (4 * Real.pi * s) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos, hs]
  have h4 : Real.exp (4 * Real.pi * s)
      = Real.exp (2 * Real.pi * s) * Real.exp (2 * Real.pi * s) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : (32 : ℝ) * 10 ^ 7 * Real.exp Real.pi
      ≤ 63 * (Real.exp (2 * Real.pi * s) * Real.exp (2 * Real.pi * s)) := by
    have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos Real.pi))
    rw [h2] at hm
    linarith [hm, h3, h4.le, h4.ge]
  have hE : Real.exp (-(2 * Real.pi * s)) = (Real.exp (2 * Real.pi * s))⁻¹ := Real.exp_neg _
  have h7 : (32 : ℝ) * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * s))
      ≤ 63 * Real.exp (2 * Real.pi * s) := by
    have hm := mul_le_mul_of_nonneg_right h5 (le_of_lt (Real.exp_pos (-(2 * Real.pi * s))))
    have e1 : (63 * (Real.exp (2 * Real.pi * s) * Real.exp (2 * Real.pi * s)))
        * Real.exp (-(2 * Real.pi * s)) = 63 * Real.exp (2 * Real.pi * s) := by
      rw [hE]; field_simp
    have e2 : ((32 : ℝ) * 10 ^ 7 * Real.exp Real.pi) * Real.exp (-(2 * Real.pi * s))
        = (32 : ℝ) * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * s)) := by ring
    linarith [hm, e1.le, e1.ge, e2.le, e2.ge]
  nlinarith [h7]

/-- The scalar comparison used in the pointwise regime `t < 3/2`. -/
lemma pointwise_scalar (c : ℝ) (hc : c ≤ 1 / 64) :
    ∀ y t : ℝ, 2 ≤ y → 1 ≤ t → t < 3 / 2 →
      10 ^ 7 * (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * t)))
        ≤ (1 - c) * (Real.exp (2 * Real.pi * y) - Real.exp (2 * Real.pi * t)) := by
  intro y t hy ht ht2
  have h1 : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-(4 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hy])
  have h2 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])
  have h3 : Real.exp (2 * Real.pi * t) ≤ Real.exp (3 * Real.pi) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht2])
  have h4 : Real.exp (4 * Real.pi) ≤ Real.exp (2 * Real.pi * y) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hy])
  have h5 : (1 : ℝ) - c ≥ 63 / 64 := by linarith
  have hp1 : (0 : ℝ) ≤ Real.exp (-(4 * Real.pi)) + Real.exp (-(2 * Real.pi)) := by positivity
  have hp2 : (0 : ℝ) ≤ Real.exp (4 * Real.pi) - Real.exp (3 * Real.pi) := by
    have hlt : Real.exp (3 * Real.pi) ≤ Real.exp (4 * Real.pi) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [Real.exp_pos (4 * Real.pi), hlt]
  nlinarith [h1, h2, h3, h4, h5, pointwise_numeric, hp1, hp2]

/-! ## The main comparison -/

/-- **The engine.**  If `‖j - q⁻¹ - 744‖ ≤ 10⁷‖q‖` on `Im ≥ 1`, then the `j`-difference of
`τ` (of height `≥ 2`) and of `σ` on the imaginary axis dominates the `q`-difference. -/
theorem jdiff_engine (hbd : ∀ u : ℍ, 1 ≤ u.im → ‖jResid u‖ ≤ 10 ^ 7 * ‖qParamFun u‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ σ : ℍ) (k : ℤ), 2 ≤ τ.im → 1 ≤ σ.im → σ.re = 0 →
      |τ.re - (k : ℝ)| ≤ 1 / 2 →
        c * Real.exp (2 * Real.pi * σ.im)
            * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
                * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖
          ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := by
  obtain ⟨cA, hcApos, hcA⟩ := j_annulus_lower
  refine ⟨min (1 / 64) (cA / 4), lt_min (by norm_num) (by linarith), ?_⟩
  intro τ σ k hτ hσ hσre hk
  have ht1 : 1 ≤ σ.im := hσ
  have hy2 : 2 ≤ τ.im := hτ
  set w : ℂ := (τ : ℂ) - (σ : ℂ) - (k : ℂ) with hw
  have hwre : w.re = τ.re - (k : ℝ) := by rw [hw]; simp [hσre]
  have hwim : w.im = τ.im - σ.im := by rw [hw]; simp
  have hwabs : |w.re| ≤ 1 / 2 := by rw [hwre]; exact hk
  have hXnorm : ‖(qParamFun τ)⁻¹ - (qParamFun σ)⁻¹‖
      = Real.exp (2 * Real.pi * σ.im)
        * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by
    rw [hw]; exact norm_inv_q_sub τ σ k hσre
  have hsplit : jInvariantFun τ - jInvariantFun σ
      = ((qParamFun τ)⁻¹ - (qParamFun σ)⁻¹) + (jResid τ - jResid σ) := by
    unfold jResid; ring
  have hc1 : min (1 / 64) (cA / 4) ≤ 1 / 64 := min_le_left _ _
  have hc2 : min (1 / 64) (cA / 4) ≤ cA / 4 := min_le_right _ _
  have hc4 : min (1 / 64) (cA / 4) ≤ 1 / 4 := by linarith
  have hc0 : (0 : ℝ) < min (1 / 64) (cA / 4) := lt_min (by norm_num) (by linarith)
  -- the common finishing step through the triangle inequality
  have finish : ∀ (hY : ‖jResid τ - jResid σ‖ ≤ (1 - min (1 / 64) (cA / 4))
        * (Real.exp (2 * Real.pi * σ.im)
            * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖)),
      min (1 / 64) (cA / 4) * Real.exp (2 * Real.pi * σ.im)
          * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
        ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := by
    intro hY
    rw [hsplit]
    have htri := norm_sub_le_norm_add ((qParamFun τ)⁻¹ - (qParamFun σ)⁻¹)
      (jResid τ - jResid σ)
    nlinarith [htri, hY, hXnorm, hc1, hc0]
  have key : min (1 / 64) (cA / 4) * Real.exp (2 * Real.pi * σ.im)
        * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
      ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := by
    by_cases ht2 : 2 ≤ σ.im
    · -- Case I: `2 ≤ Im σ`
      by_cases hclose : 0 ≤ w.im ∨ ‖w‖ ≤ 2
      · -- Case I.a: the `Ψ`-route
        have hident := qmul_jdiff τ σ k
        have hPsi_ge : (3 / 4 : ℝ) ≤ ‖Psi τ‖ := by
          have h := Psi_sub_one_le_quarter τ hτ
          have h2 := abs_norm_sub_norm_le (Psi τ) (1 : ℂ)
          rw [norm_one, abs_le] at h2
          linarith [h2.1]
        have hLip : ‖Psi τ - Psi ((k : ℝ) +ᵥ σ)‖ ≤ (1 / 8) * ‖w‖ := by
          have him : 2 ≤ ((k : ℝ) +ᵥ σ).im := by
            have hcoe : ((((k : ℝ) +ᵥ σ : ℍ)) : ℂ) = ((k : ℂ) + (σ : ℂ)) := by
              rw [UpperHalfPlane.coe_vadd]; push_cast; ring
            have h2 : ((((k : ℝ) +ᵥ σ : ℍ)) : ℂ).im = σ.im := by
              rw [hcoe, Complex.add_im, Complex.intCast_im, zero_add, UpperHalfPlane.coe_im]
            rw [← UpperHalfPlane.coe_im, h2]
            exact ht2
          have h := Psi_lipschitz_eighth τ ((k : ℝ) +ᵥ σ) hτ him
          have hcoe : ((τ : ℂ) - (((k : ℝ) +ᵥ σ : ℍ) : ℂ)) = w := by
            rw [UpperHalfPlane.coe_vadd, hw]; push_cast; ring
          rwa [hcoe] at h
        have hF0ge : (1 / 4) * ‖w‖
            ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by
          rcases hclose with hν | hw2
          · have h4 := Work.Asymptotics.EJL.exp_bound_of_im_nonneg w hwabs hν
            linarith [h4, norm_nonneg w]
          · have h4 := norm_one_sub_expm_ge_third w hwabs hw2
            linarith [h4, norm_nonneg w]
        have hchain : (1 / 4) * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
            ≤ ‖qParamFun σ‖ * ‖jInvariantFun τ - jInvariantFun σ‖ := by
          have hnm : ‖qParamFun σ * (jInvariantFun τ - jInvariantFun σ)‖
              = ‖qParamFun σ‖ * ‖jInvariantFun τ - jInvariantFun σ‖ := norm_mul _ _
          rw [← hnm, hident]
          have hA : (3 / 4) * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
              ≤ ‖Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)‖ := by
            rw [norm_mul, norm_sub_rev (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))) 1]
            exact mul_le_mul_of_nonneg_right hPsi_ge (norm_nonneg _)
          have htri := norm_sub_le_norm_add
            (Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1))
            (Psi τ - Psi ((k : ℝ) +ᵥ σ))
          linarith [hA, hLip, htri, hF0ge]
        have hqpos : 0 < ‖qParamFun σ‖ := by
          rw [norm_qParamFun_eq_exp]; exact Real.exp_pos _
        have h2 : (1 / 4) * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
            / ‖qParamFun σ‖ = (1 / 4) * (Real.exp (2 * Real.pi * σ.im)
              * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖) := by
          rw [div_eq_mul_inv, inv_eq_one_div, one_div_norm_qParamFun σ]; ring
        have hfinal : (1 / 4) * (Real.exp (2 * Real.pi * σ.im)
              * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖)
            ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := by
          rw [← h2, div_le_iff₀ hqpos]
          nlinarith [hchain]
        calc min (1 / 64) (cA / 4) * Real.exp (2 * Real.pi * σ.im)
              * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
            = min (1 / 64) (cA / 4) * (Real.exp (2 * Real.pi * σ.im)
                * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖) := by ring
          _ ≤ (1 / 4) * (Real.exp (2 * Real.pi * σ.im)
                * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖) :=
              mul_le_mul_of_nonneg_right hc4 (by positivity)
          _ ≤ ‖jInvariantFun τ - jInvariantFun σ‖ := hfinal
      · -- Case I.b: the annulus bound
        have hfar := not_or.mp hclose
        have hν : w.im < 0 := not_le.mp hfar.1
        have hw2 : 2 < ‖w‖ := not_le.mp hfar.2
        have hwl : (1 : ℝ) / 2 ≤ ‖w‖ := by linarith [hw2]
        have hann := hcA τ σ k hσre ht2 hτ hk hwl
        have hF0le : ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ ≤ 2 := by
          have hlt : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ < 1 := by
            rw [Complex.norm_exp]
            have hre : (-(2 * (Real.pi : ℂ) * Complex.I * w)).re = 2 * Real.pi * w.im := by
              simp [Complex.mul_re, Complex.mul_im]
            rw [hre]
            exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hν])
          calc ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
              ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ :=
                norm_sub_le _ _
            _ = 1 + ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by rw [norm_one]
            _ ≤ 2 := by linarith
        have hle1 : min (1 / 64) (cA / 4) * Real.exp (2 * Real.pi * σ.im)
              * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
            ≤ (cA / 4) * Real.exp (2 * Real.pi * σ.im) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc2 (le_of_lt (Real.exp_pos _))) hF0le
            (norm_nonneg _) (by positivity)
        have hEF : (cA / 4) * Real.exp (2 * Real.pi * σ.im) * 2 ≤ cA / ‖qParamFun σ‖ := by
          have hE := (one_div_norm_qParamFun σ).symm
          have hq : (0 : ℝ) ≤ 1 / ‖qParamFun σ‖ := le_of_lt (one_div_pos.mpr (by
            rw [norm_qParamFun_eq_exp]; exact Real.exp_pos _))
          have hcle : cA / 2 ≤ cA := by linarith
          calc (cA / 4) * Real.exp (2 * Real.pi * σ.im) * 2
              = (cA / 2) * (1 / ‖qParamFun σ‖) := by rw [hE]; ring
            _ ≤ cA * (1 / ‖qParamFun σ‖) := mul_le_mul_of_nonneg_right hcle hq
            _ = cA / ‖qParamFun σ‖ := by ring
        linarith [hle1, hEF, hann]
    · -- Case II: `Im σ < 2`
      have ht2lt : σ.im < 2 := not_le.mp ht2
      have hν : 0 < w.im := by rw [hwim]; linarith
      have hXge : Real.exp (2 * Real.pi * τ.im) - Real.exp (2 * Real.pi * σ.im)
          ≤ ‖(qParamFun τ)⁻¹ - (qParamFun σ)⁻¹‖ := by
        have h1 : ‖(qParamFun τ)⁻¹‖ = Real.exp (2 * Real.pi * τ.im) := by
          rw [norm_inv, norm_qParamFun_eq_exp, Real.exp_neg, inv_inv]
        have h2 : ‖(qParamFun σ)⁻¹‖ = Real.exp (2 * Real.pi * σ.im) := by
          rw [norm_inv, norm_qParamFun_eq_exp, Real.exp_neg, inv_inv]
        calc Real.exp (2 * Real.pi * τ.im) - Real.exp (2 * Real.pi * σ.im)
            = ‖(qParamFun τ)⁻¹‖ - ‖(qParamFun σ)⁻¹‖ := by rw [h1, h2]
          _ ≤ ‖(qParamFun τ)⁻¹ - (qParamFun σ)⁻¹‖ := norm_sub_norm_le _ _
      by_cases ht32 : 3 / 2 ≤ σ.im
      · -- Case II.b: the mean-value bound
        have hF0ge : 4 * ‖w‖ ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ :=
          Work.Asymptotics.EJL.exp_bound_of_im_nonneg w hwabs (le_of_lt hν)
        have hYle : ‖jResid τ - jResid σ‖
            ≤ 2 * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * σ.im)) * ‖w‖ := by
          have hτk : jResidLift ((τ : ℂ) - (k : ℂ)) = jResid τ := by
            have h : (τ : ℂ) - (k : ℂ) = (τ : ℂ) + ((-k : ℤ) : ℂ) := by push_cast; ring
            rw [h]; exact jResidLift_add_int τ (-k)
          have hσc : jResidLift (σ : ℂ) = jResid σ := jResidLift_of_self σ
          have him1 : 3 / 2 ≤ (((τ : ℂ) - (k : ℂ))).im := by
            rw [Complex.sub_im, Complex.intCast_im, sub_zero]
            exact le_trans (by norm_num) hτ
          have him2 : 3 / 2 ≤ ((σ : ℂ)).im := by simpa using ht32
          have hmvt := jResidLift_mvt (by norm_num) hbd ((τ : ℂ) - (k : ℂ)) (σ : ℂ) him1 him2
          have hmin : min (((τ : ℂ) - (k : ℂ))).im ((σ : ℂ)).im = σ.im := by
            rw [Complex.sub_im, Complex.intCast_im, sub_zero, UpperHalfPlane.coe_im,
              UpperHalfPlane.coe_im]
            exact min_eq_right (by linarith [ht2lt, hτ])
          have hdist : ‖((τ : ℂ) - (k : ℂ)) - (σ : ℂ)‖ = ‖w‖ := by
            rw [hw]; congr 1; ring
          rw [hmin, hdist, hσc, hτk] at hmvt
          exact hmvt
        have hY : ‖jResid τ - jResid σ‖ ≤ (1 - min (1 / 64) (cA / 4))
            * (Real.exp (2 * Real.pi * σ.im)
                * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖) := by
          refine le_trans hYle ?_
          have hYb : 2 * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * σ.im)) * ‖w‖
              ≤ (1 - min (1 / 64) (cA / 4)) * (4 * Real.exp (2 * Real.pi * σ.im) * ‖w‖) := by
            have hsc := mvt_scalar σ.im ht32
            have h1c : (1 : ℝ) - min (1 / 64) (cA / 4) ≥ 63 / 64 := by linarith [hc1]
            have hA := mul_le_mul_of_nonneg_right hsc (norm_nonneg w)
            have hB : (63 / 64) * (4 * Real.exp (2 * Real.pi * σ.im)) * ‖w‖
                ≤ (1 - min (1 / 64) (cA / 4)) * (4 * Real.exp (2 * Real.pi * σ.im) * ‖w‖) := by
              have hpos : (0 : ℝ) ≤ 4 * Real.exp (2 * Real.pi * σ.im) * ‖w‖ := by positivity
              nlinarith [h1c, hpos]
            linarith [hA, hB]
          refine le_trans hYb ?_
          have h2 : 4 * Real.exp (2 * Real.pi * σ.im) * ‖w‖
              ≤ Real.exp (2 * Real.pi * σ.im)
                * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by
            have := mul_le_mul_of_nonneg_left hF0ge (le_of_lt (Real.exp_pos (2 * Real.pi * σ.im)))
            linarith [this]
          have hpos : (0 : ℝ) ≤ 1 - min (1 / 64) (cA / 4) := by linarith [hc1]
          exact mul_le_mul_of_nonneg_left h2 hpos
        exact finish hY
      · -- Case II.a: the pointwise bound
        have h32 : σ.im < 3 / 2 := not_le.mp ht32
        have hYle : ‖jResid τ - jResid σ‖
            ≤ 10 ^ 7 * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * σ.im))) := by
          have h1 := hbd τ (le_trans (by norm_num) hτ)
          have h2 := hbd σ ht1
          calc ‖jResid τ - jResid σ‖ ≤ ‖jResid τ‖ + ‖jResid σ‖ := norm_sub_le _ _
            _ ≤ 10 ^ 7 * ‖qParamFun τ‖ + 10 ^ 7 * ‖qParamFun σ‖ := add_le_add h1 h2
            _ = 10 ^ 7 * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * σ.im))) := by
                rw [norm_qParamFun_eq_exp, norm_qParamFun_eq_exp]; ring
        have hps := pointwise_scalar (min (1 / 64) (cA / 4)) hc1 τ.im σ.im hτ ht1 h32
        have hY : ‖jResid τ - jResid σ‖ ≤ (1 - min (1 / 64) (cA / 4))
            * (Real.exp (2 * Real.pi * σ.im)
                * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖) := by
          refine le_trans (le_trans hYle hps) ?_
          have hE1 : Real.exp (2 * Real.pi * σ.im)
              * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖
              = ‖(qParamFun τ)⁻¹ - (qParamFun σ)⁻¹‖ := hXnorm.symm
          rw [hE1]
          exact mul_le_mul_of_nonneg_left hXge (by linarith [hc1])
        exact finish hY
  exact key

end Work.Asymptotics.EjdiffAux

namespace Work.Asymptotics

/-- **`Work.Asymptotics.E_jdiff_large`.**  On the cusp-`0` tile `E = KEpsilon` the difference
`j w - j (i t)` dominates `e^{2π Im (S • w)} |1 - e^{2πi(S • w - i t)}|`, uniformly in `w ∈ E`
and `t ≥ 1`. -/
theorem E_jdiff_large :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t →
        c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
            * ‖1 - Complex.exp (2 * Real.pi * Complex.I
                * ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖
          ≤ ‖Work.Kernels.jInvariantFun w
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨c, hcpos, hc⟩ :=
    EjdiffAux.jdiff_engine (fun u hu => Work.Asymptotics.EJL.low_height_j u hu)
  refine ⟨c, hcpos, ?_⟩
  intro w t ht hwE ht1
  set τ : UpperHalfPlane := ModularGroup.S • w with hτdef
  set σ : UpperHalfPlane := Work.Kernels.imagAxis t ht with hσdef
  have hτ2 : 2 ≤ τ.im := hwE.2
  have hσim : σ.im = t := by rw [hσdef]; simp [Work.Kernels.imagAxis]
  have hσre : σ.re = 0 := by rw [hσdef]; simp [Work.Kernels.imagAxis]
  have hσcoe : ((σ : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := by
    rw [hσdef]; simp [Work.Kernels.imagAxis]
  set k : ℤ := ⌊τ.re + 1 / 2⌋ with hkdef
  have hk : |τ.re - (k : ℝ)| ≤ 1 / 2 := by
    have h1 : (k : ℝ) ≤ τ.re + 1 / 2 := by rw [hkdef]; exact Int.floor_le _
    have h2 : τ.re + 1 / 2 < (k : ℝ) + 1 := by rw [hkdef]; exact Int.lt_floor_add_one _
    rw [abs_le]; constructor <;> linarith
  have h := hc τ σ k hτ2 (by rw [hσim]; exact ht1) hσre hk
  have key : c * Real.exp (2 * Real.pi * τ.im)
        * ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))‖
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := by
    have h1 : Real.exp (2 * Real.pi * τ.im)
          * ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))‖
        = Real.exp (2 * Real.pi * t)
          * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
              * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖ := by
      rw [EjdiffAux.lhs_eq, hσim]
    calc c * Real.exp (2 * Real.pi * τ.im)
          * ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) - (σ : ℂ)))‖
        = c * (Real.exp (2 * Real.pi * t)
            * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
                * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖) := by rw [← h1]; ring
      _ = c * Real.exp (2 * Real.pi * σ.im)
            * ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I
                * ((τ : ℂ) - (σ : ℂ) - (k : ℂ))))‖ := by rw [hσim]; ring
      _ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := h
  rw [← hσcoe]
  have hjsmul : Work.Kernels.jInvariantFun (ModularGroup.S • w) = Work.Kernels.jInvariantFun w :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul w
  have hright : ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun σ‖
      = ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := by
    rw [hτdef, hjsmul]
  rw [hright]
  exact key
end Work.Asymptotics
