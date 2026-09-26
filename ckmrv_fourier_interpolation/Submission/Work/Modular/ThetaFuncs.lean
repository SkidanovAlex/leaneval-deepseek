import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice

/-!
# The Jacobi theta functions `θ₂`, `θ₃`, `θ₄` as functions on `ℍ`

We package the classical one-dimensional theta functions

* `theta3 τ = θ₃(τ) = ∑_{n ∈ ℤ} exp (π i n² τ)`,
* `theta4 τ = θ₄(τ) = ∑_{n ∈ ℤ} (-1)^n exp (π i n² τ)`,
* `theta2 τ = θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)`

in terms of Mathlib's two-variable Jacobi theta function `jacobiTheta₂` and prove the
elementary periodicity (translation by `1`) and differentiability statements, as well as
the modular `S`-transformation of `theta3` (which is Mathlib's `jacobiTheta_S_smul`).
-/

open UpperHalfPlane Filter
open scoped Real MatrixGroups Manifold Topology

namespace Work.Modular

/-- `θ₃(τ) = ∑_{n ∈ ℤ} exp (π i n² τ)`. -/
noncomputable def theta3 (τ : ℍ) : ℂ := jacobiTheta (τ : ℂ)

/-- `θ₄(τ) = ∑_{n ∈ ℤ} (-1)^n exp (π i n² τ) = θ₃(τ + 1)`. -/
noncomputable def theta4 (τ : ℍ) : ℂ := jacobiTheta₂ (1 / 2) (τ : ℂ)

/-- `θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)`, written as
`exp (π i τ / 4) · jacobiTheta₂ (τ / 2) τ`. -/
noncomputable def theta2 (τ : ℍ) : ℂ :=
  Complex.exp (π * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)

/-! ### Elementary arithmetic of the exponential -/

lemma exp_pi_I_sq (n : ℤ) :
    Complex.exp (π * Complex.I * (n : ℂ) ^ 2) = Complex.exp (π * Complex.I * (n : ℂ)) := by
  have h : (n : ℂ) ^ 2 = (n : ℂ) + ((n * (n - 1) : ℤ) : ℂ) := by push_cast; ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n * (n - 1) = 2 * m := by
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
    exact ⟨k, by linear_combination hk⟩
  have h2 : Complex.exp (π * Complex.I * ((2 * m : ℤ) : ℂ)) = 1 := by
    rw [show π * Complex.I * ((2 * m : ℤ) : ℂ) = (m : ℂ) * (2 * π * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [h, hm]
  rw [show π * Complex.I * ((n : ℂ) + ((2 * m : ℤ) : ℂ)) =
      π * Complex.I * (n : ℂ) + π * Complex.I * ((2 * m : ℤ) : ℂ) by ring, Complex.exp_add,
    h2, mul_one]

lemma exp_pi_I_sq_add (n : ℤ) :
    Complex.exp (π * Complex.I * ((n : ℂ) ^ 2 + n)) = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, n * (n + 1) = 2 * m := by
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    exact ⟨k, by linear_combination hk⟩
  rw [show π * Complex.I * ((n : ℂ) ^ 2 + n) = π * Complex.I * ((n * (n + 1) : ℤ) : ℂ) by
    push_cast; ring]
  rw [hm]
  rw [show π * Complex.I * ((2 * m : ℤ) : ℂ) = (m : ℂ) * (2 * π * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

lemma exp_pi_I_add_sq (n : ℤ) :
    Complex.exp (π * Complex.I * (n : ℂ) + π * Complex.I * (n : ℂ) ^ 2) = 1 := by
  rw [show π * Complex.I * (n : ℂ) + π * Complex.I * (n : ℂ) ^ 2 =
      π * Complex.I * ((n : ℂ) ^ 2 + n) by ring]
  exact exp_pi_I_sq_add n

/-- The half-integer shift: `exp (π i (n + 1/2)²) = exp (π i / 4)`. -/
lemma exp_pi_I_half (n : ℤ) :
    Complex.exp (π * Complex.I * ((n : ℂ) + 1 / 2) ^ 2) = Complex.exp (π * Complex.I / 4) := by
  rw [show π * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 =
      π * Complex.I / 4 + π * Complex.I * ((n : ℂ) ^ 2 + n) by ring,
    Complex.exp_add, exp_pi_I_sq_add n, mul_one]

/-! ### Translation by `1` -/

lemma theta3_T_smul (τ : ℍ) : theta3 (ModularGroup.T • τ) = theta4 τ := by
  rw [theta3, theta4]
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  simp only [hT]
  rw [jacobiTheta_eq_jacobiTheta₂]
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term, mul_zero, zero_add]
  rw [show π * Complex.I * (n : ℂ) ^ 2 * ((τ : ℂ) + 1) =
        π * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ) + π * Complex.I * (n : ℂ) ^ 2 by ring,
      show (2 : ℂ) * π * Complex.I * n * (1 / 2) + π * Complex.I * n ^ 2 * τ =
        π * Complex.I * n + π * Complex.I * n ^ 2 * τ by ring]
  rw [Complex.exp_add, Complex.exp_add, exp_pi_I_sq n]
  ring

lemma theta4_T_smul (τ : ℍ) : theta4 (ModularGroup.T • τ) = theta3 τ := by
  rw [theta3, theta4]
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  simp only [hT]
  rw [jacobiTheta_eq_jacobiTheta₂]
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  rw [show (2 : ℂ) * π * Complex.I * n * (1 / 2) + π * Complex.I * n ^ 2 * ((τ : ℂ) + 1) =
        (π * Complex.I * n + π * Complex.I * n ^ 2) + π * Complex.I * n ^ 2 * (τ : ℂ) by ring]
  rw [Complex.exp_add, exp_pi_I_add_sq n, one_mul]
  simp

/-! ### The series representation of `theta2` -/

lemma theta2_eq_tsum (τ : ℍ) :
    theta2 τ = ∑' n : ℤ, Complex.exp (π * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2) := by
  rw [theta2, jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  rw [← Complex.exp_add]
  congr 1
  ring

lemma theta2_T_smul (τ : ℍ) :
    theta2 (ModularGroup.T • τ) = Complex.exp (π * Complex.I / 4) * theta2 τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  rw [theta2_eq_tsum, theta2_eq_tsum]
  rw [hT, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [show π * Complex.I * ((τ : ℂ) + 1) * ((n : ℂ) + 1 / 2) ^ 2 =
        π * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 +
        π * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 by ring]
  rw [Complex.exp_add, exp_pi_I_half n]
  ring

/-! ### Differentiability -/

lemma mdifferentiable_theta3 : MDiff theta3 := by
  unfold theta3
  simpa only [Function.comp_def] using mdifferentiable_jacobiTheta

lemma mdifferentiable_theta4 : MDiff theta4 := by
  intro τ
  rw [mdifferentiableAt_iff]
  have hev : (theta4 ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun w : ℂ => jacobiTheta₂ (1 / 2) w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply, theta4, ofComplex_apply_of_im_pos hw]
  exact (hev.differentiableAt_iff).mpr (differentiableAt_jacobiTheta₂_snd (1 / 2) τ.im_pos)

lemma mdifferentiable_theta2 : MDiff theta2 := by
  intro τ
  rw [mdifferentiableAt_iff]
  have hev : (theta2 ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun w : ℂ => Complex.exp (π * Complex.I * w / 4) * jacobiTheta₂ (w / 2) w) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply, theta2, ofComplex_apply_of_im_pos hw]
  refine (hev.differentiableAt_iff).mpr ?_
  have hG : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) ((τ : ℂ) / 2, (τ : ℂ)) :=
    (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.im_pos).differentiableAt
  have hF : DifferentiableAt ℂ (fun w : ℂ => (w / 2, w)) (τ : ℂ) := by fun_prop
  have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (π * Complex.I * w / 4)) (τ : ℂ) := by
    fun_prop
  have hcomp : DifferentiableAt ℂ
      ((fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) ∘ (fun w : ℂ => (w / 2, w))) (τ : ℂ) :=
    DifferentiableAt.comp (τ : ℂ) hG hF
  have hmain : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ (w / 2) w) (τ : ℂ) := by
    simpa only [Function.comp_def] using hcomp
  exact hexp.mul hmain

/-! ### Series representations -/

lemma theta3_eq_tsum (τ : ℍ) :
    theta3 τ = ∑' n : ℤ, Complex.exp (π * Complex.I * (n : ℂ) ^ 2 * (τ : ℂ)) := by
  rw [theta3, jacobiTheta]

lemma theta4_eq_tsum (τ : ℍ) :
    theta4 τ = ∑' n : ℤ,
      Complex.exp (2 * π * Complex.I * n * (1 / 2) + π * Complex.I * n ^ 2 * (τ : ℂ)) := by
  rw [theta4, jacobiTheta₂]
  simp only [jacobiTheta₂_term]

/-! ### The `S`-transformation of `theta3` -/

lemma theta3_S_smul (τ : ℍ) :
    theta3 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * theta3 τ := by
  simpa only [theta3] using jacobiTheta_S_smul τ

/-! ### Limits at the cusp `i∞` -/

lemma tendsto_theta3_atImInfty :
    Filter.Tendsto theta3 UpperHalfPlane.atImInfty (𝓝 1) := by
  have hπ : Filter.Tendsto (fun y : ℝ => π * y) Filter.atTop Filter.atTop :=
    tendsto_id.const_mul_atTop Real.pi_pos
  have hneg : Filter.Tendsto (fun y : ℝ => -(π * y)) Filter.atTop Filter.atBot :=
    tendsto_neg_atBot_iff.mpr hπ
  have hexp : Filter.Tendsto (fun y : ℝ => Real.exp (-(π * y))) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have h0 : Filter.Tendsto (fun τ : ℂ => Real.exp (-π * τ.im))
      (Filter.comap Complex.im Filter.atTop) (𝓝 0) := by
    have h := hexp.comp (Filter.tendsto_comap (f := Complex.im) (x := Filter.atTop))
    simpa only [Function.comp_def, neg_mul] using h
  have hsub : Filter.Tendsto (fun τ : ℂ => jacobiTheta τ - 1)
      (Filter.comap Complex.im Filter.atTop) (𝓝 0) :=
    isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto h0
  have hjac : Filter.Tendsto jacobiTheta (Filter.comap Complex.im Filter.atTop) (𝓝 1) := by
    have h := hsub.add_const 1
    simpa only [zero_add, sub_add_cancel] using h
  have hcomp := hjac.comp UpperHalfPlane.tendsto_coe_atImInfty
  unfold theta3
  simpa only [Function.comp_def] using hcomp

lemma tendsto_theta4_atImInfty :
    Filter.Tendsto theta4 UpperHalfPlane.atImInfty (𝓝 1) := by
  have hshift : Filter.Tendsto (fun τ : ℍ => (↑ModularGroup.T : GL (Fin 2) ℝ) • τ)
      UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty :=
    UpperHalfPlane.tendsto_smul_atImInfty (by simp)
  have h := tendsto_theta3_atImInfty.comp hshift
  have hfun : (fun τ : ℍ => theta3 ((↑ModularGroup.T : GL (Fin 2) ℝ) • τ)) = theta4 := by
    funext τ
    rw [← ModularGroup.sl_moeb]
    exact theta3_T_smul τ
  simpa only [Function.comp_def, hfun] using h

end Work.Modular
