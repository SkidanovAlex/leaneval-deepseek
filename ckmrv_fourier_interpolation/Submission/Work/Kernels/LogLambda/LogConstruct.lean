/-
# Construction of the logarithm data `(𝓛, 𝓛_S)` of CKMRV

This file constructs the pair of holomorphic functions `𝓛`, `𝓛_S` of CKMRV
(Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)), Section 2.1.5:
the normalised logarithms of `λ = θ₁₀⁴/θ₀₀⁴` and `λ_S = θ₀₁⁴/θ₀₀⁴`, satisfying
`e^𝓛 = λ`, `e^{𝓛_S} = λ_S` and the transformation laws (2.9)

  `𝓛|₀T = 𝓛 - 𝓛_S + πi`, `𝓛_S|₀T = -𝓛_S`, `𝓛|₀S = 𝓛_S`, `𝓛_S|₀S = 𝓛`.

The point of `λ(S τ) = λ_S(τ)` and `λ_S(S τ) = λ(τ)` is that `𝓛_S` is simply `𝓛 ∘ S`, so only the
two `T`-laws need work; they are equivalent to the two integer constants `P`, `Q` defined by

  `2πiP = 𝓛(τ+1) - 𝓛(τ) + 𝓛_S(τ) - πi`, `2πiQ = 𝓛_S(τ+1) + 𝓛_S(τ)`

vanishing.  Both are computed by evaluating the (constant) left-hand sides at `τ = iT` and
letting `T → ∞`, which is legitimate once `𝓛` is normalised so that on `{im τ > 1}` it is given by
the explicit branch

  `𝓛(z) = πiz + 4log 2 + 4log(θ₁₀(z)/(2e^{πiz/4})) - 4log θ₀₀(z)`
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound
import Submission.Work.Analysis.BranchLog.holomorphic_of_exp
import Submission.Work.Analysis.DiscreteValues.eq_const_of_isPreconnected

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

/-- The upper half plane, as a subset of `ℂ`. -/
def U : Set ℂ := {z : ℂ | 0 < z.im}

lemma isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_U : IsPreconnected U := by
  have hc : Convex ℝ U := convex_halfSpace_im_gt 0
  exact hc.isPreconnected

/-- The extension of `θ₀₀` to `ℂ`. -/
def thetaC00 (z : ℂ) : ℂ := jacobiTheta z
/-- The extension of `θ₀₁` to `ℂ`. -/
def thetaC01 (z : ℂ) : ℂ := jacobiTheta₂ (1/2) z
/-- The extension of `θ₁₀` to `ℂ`. -/
def thetaC10 (z : ℂ) : ℂ := Complex.exp (Real.pi * Complex.I * z / 4) * jacobiTheta₂ (z/2) z

lemma thetaC00_of_mem {z : ℂ} (hz : z ∈ U) : thetaC00 z = theta00Fun ⟨z, hz⟩ := rfl
lemma thetaC01_of_mem {z : ℂ} (hz : z ∈ U) : thetaC01 z = theta01Fun ⟨z, hz⟩ := rfl
lemma thetaC10_of_mem {z : ℂ} (hz : z ∈ U) : thetaC10 z = theta10Fun ⟨z, hz⟩ := rfl

/-- The extension of `λ` to `ℂ`. -/
def lamC (z : ℂ) : ℂ := (thetaC10 z)^4 / (thetaC00 z)^4

/-- The extension of `λ_S` to `ℂ`. -/
def lamSC (z : ℂ) : ℂ := (thetaC01 z)^4 / (thetaC00 z)^4

lemma lamC_of_mem {z : ℂ} (hz : z ∈ U) : lamC z = lambdaFun ⟨z, hz⟩ := rfl
lemma lamSC_of_mem {z : ℂ} (hz : z ∈ U) : lamSC z = lambdaSFun ⟨z, hz⟩ := rfl


/-! ## Holomorphy of the extended theta functions -/

lemma differentiableOn_thetaC00 : DifferentiableOn ℂ thetaC00 U := fun z hz =>
  (differentiableAt_jacobiTheta (by simpa [U] using hz)).differentiableWithinAt

lemma differentiableOn_thetaC01 : DifferentiableOn ℂ thetaC01 U := fun z hz =>
  (differentiableAt_jacobiTheta₂_snd (1/2) (by simpa [U] using hz)).differentiableWithinAt

lemma differentiableAt_thetaC02 (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ (w/2) w) z := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (z/2, z) :=
    (hasFDerivAt_jacobiTheta₂ (z/2) (by simpa using hz)).differentiableAt
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (w/2, w)) z := by fun_prop
  exact DifferentiableAt.comp (x := z) (f := fun w : ℂ => (w/2, w))
    (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) h1 h2

lemma differentiableOn_thetaC10 : DifferentiableOn ℂ thetaC10 U := fun z hz => by
  have h2 := differentiableAt_thetaC02 z (by simpa [U] using hz)
  have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Real.pi * Complex.I * w / 4)) z := by
    fun_prop
  exact (h1.mul h2).differentiableWithinAt

/-! ## The explicit branch of `log λ` on `{im z > 1}`

On the half plane `im z > 1` both `θ₀₀(z)` and `θ₁₀(z)/(2 e^{πiz/4})` lie in the disc of radius
`1` around `1`, so the principal logarithm is holomorphic there and the function

  `LU(z) = πiz + 4log 2 + 4log(θ₁₀(z)/(2e^{πiz/4})) - 4log θ₀₀(z)`

is a holomorphic logarithm of `λ` with `LU(z) - πiz → 4 log 2` as `im z → ∞`. -/

/-- The half plane `{z | 1 < im z}`, on which the explicit branch `LU` is defined. -/
def V : Set ℂ := {z : ℂ | 1 < z.im}

lemma V_subset_U : V ⊆ U := fun z hz => by
  simp only [U, V, Set.mem_setOf_eq] at hz ⊢
  linarith

/-- The explicit branch of `log λ`. -/
def LU (z : ℂ) : ℂ :=
  Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)
    + 4 * Complex.log (thetaC10 z / (2 * Complex.exp (Real.pi * Complex.I * z / 4)))
    - 4 * Complex.log (thetaC00 z)

/-- The ratio `θ₁₀(z)/(2e^{πiz/4}) = θ₂(z/2,z)/2`. -/
lemma thetaC10_div_exp (z : ℂ) :
    thetaC10 z / (2 * Complex.exp (Real.pi * Complex.I * z / 4)) = jacobiTheta₂ (z/2) z / 2 := by
  have h2 : (2 : ℂ) * Complex.exp (Real.pi * Complex.I * z / 4) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  rw [thetaC10]
  field_simp

lemma ratio_bound_lt_one (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-(2 * Real.pi * t)) / (1 - Real.exp (-(2 * Real.pi * t))) < 1 := by
  have h2 : (2:ℝ) < Real.exp (2 * Real.pi * t) := by
    have h := Real.add_one_le_exp (2 * Real.pi * t)
    nlinarith [Real.pi_pos, ht, Real.pi_gt_three]
  have he : Real.exp (-(2 * Real.pi * t)) < 1/2 := by
    have h3 : Real.exp (-(2 * Real.pi * t)) = (Real.exp (2 * Real.pi * t))⁻¹ := by
      rw [← Real.exp_neg]
    rw [h3, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simp only [inv_inv]
    exact h2
  rw [div_lt_one (by linarith)]
  linarith

lemma im_ratio_small {z : ℂ} (hz : 1 ≤ z.im) :
    ‖jacobiTheta₂ (z/2) z / 2 - 1‖ < 1 := by
  have h := ThetaLower.ratio_estimate z (by linarith)
  refine lt_of_le_of_lt h ?_
  exact ratio_bound_lt_one z.im hz


/-! ## The explicit branch is a logarithm of `λ` -/

lemma thetaC00_ne_zero_of_im_gt {z : ℂ} (hz : 1 < z.im) : thetaC00 z ≠ 0 := by
  show jacobiTheta z ≠ 0
  intro h0
  have h := norm_jacobiTheta_sub_one_le (τ := z) (by linarith)
  rw [h0] at h
  simp only [zero_sub, norm_neg, norm_one] at h
  have h2 : 2 * Real.exp (-Real.pi * z.im) / (1 - Real.exp (-Real.pi * z.im)) < 1 := by
    have h3 : Real.exp (-Real.pi * z.im) < 1/3 := by
      have h4 : (3:ℝ) < Real.exp (Real.pi * z.im) := by
        have := Real.add_one_le_exp (Real.pi * z.im)
        nlinarith [Real.pi_pos, hz, Real.pi_gt_three]
      have h5 : Real.exp (-Real.pi * z.im) = (Real.exp (Real.pi * z.im))⁻¹ := by
        rw [show -Real.pi * z.im = -(Real.pi * z.im) by ring, Real.exp_neg]
      rw [h5, show (1:ℝ)/3 = (3:ℝ)⁻¹ by norm_num, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      simp only [inv_inv]
      exact h4
    rw [div_lt_one (by linarith)]
    linarith
  have h' : (1:ℝ) ≤ 2 * Real.exp (-Real.pi*z.im) / (1 - Real.exp (-Real.pi*z.im)) := by
    calc (1:ℝ) ≤ 2 / (1 - Real.exp (-Real.pi*z.im)) * Real.exp (-Real.pi*z.im) := h
      _ = 2 * Real.exp (-Real.pi*z.im) / (1 - Real.exp (-Real.pi*z.im)) := by ring
  linarith

lemma exp_four_log {w : ℂ} (hw : w ≠ 0) :
    Complex.exp ((4 : ℂ) * Complex.log w) = w^4 := by
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul, Complex.exp_log hw]

lemma exp_neg_four_log {w : ℂ} (hw : w ≠ 0) :
    Complex.exp ((-4 : ℂ) * Complex.log w) = (w^4)⁻¹ := by
  rw [show (-4 : ℂ) = ((-4 : ℤ) : ℂ) by norm_num, Complex.exp_int_mul, Complex.exp_log hw,
    zpow_neg]
  rfl

lemma exp_four_log_two : Complex.exp ((4 : ℂ) * (Real.log 2 : ℂ)) = 16 := by
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul, ← Complex.ofReal_exp,
    Real.exp_log (by norm_num)]
  norm_num

lemma exp_LU (z : ℂ) (hz : 1 < z.im) : Complex.exp (LU z) = lamC z := by
  have hz0 : 0 < z.im := by linarith
  have ht0 : thetaC00 z ≠ 0 := thetaC00_ne_zero_of_im_gt hz
  have hrmid : ‖jacobiTheta₂ (z/2) z / 2 - 1‖ < 1 := im_ratio_small (le_of_lt hz)
  have hr0 : jacobiTheta₂ (z/2) z / 2 ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at hrmid
    linarith
  have he1 : Complex.exp (Real.pi * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  have hexpand : Complex.exp (LU z)
      = Complex.exp (Real.pi * Complex.I * z) * 16
        * (jacobiTheta₂ (z/2) z / 2)^4 * (thetaC00 z ^ 4)⁻¹ := by
    rw [LU, thetaC10_div_exp]
    rw [show Real.pi * Complex.I * z + 4 * ↑(Real.log 2) + 4 * Complex.log (jacobiTheta₂ (z / 2) z / 2) - 4 * Complex.log (thetaC00 z)
        = Real.pi * Complex.I * z + (4 * ↑(Real.log 2) + (4 * Complex.log (jacobiTheta₂ (z/2) z / 2) + (-4) * Complex.log (thetaC00 z))) by ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, exp_four_log hr0, exp_neg_four_log ht0, exp_four_log_two]
    ring
  have hratio : Complex.exp (Real.pi * Complex.I * z) * 16 * (jacobiTheta₂ (z/2) z / 2)^4
      = thetaC10 z ^ 4 := by
    rw [← thetaC10_div_exp]
    have hexp4 : (Complex.exp (Real.pi * Complex.I * z / 4))^4
        = Complex.exp (Real.pi * Complex.I * z) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [div_pow, mul_pow, hexp4]
    have h16 : (2:ℂ)^4 = 16 := by norm_num
    rw [h16]
    field_simp
  rw [hexpand, hratio]
  show thetaC10 z ^ 4 * (thetaC00 z ^ 4)⁻¹ = lamC z
  rw [lamC, div_eq_mul_inv]


/-! ## Non-vanishing of the extended `λ` and the existence of a global logarithm -/

lemma isSimplyConnected_U : IsSimplyConnected U := by
  have hc : Convex ℝ U := convex_halfSpace_im_gt 0
  have hne : U.Nonempty := ⟨Complex.I, by simp [U]⟩
  haveI := hc.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

lemma thetaC00_ne_zero {z : ℂ} (hz : 0 < z.im) : thetaC00 z ≠ 0 := by
  obtain ⟨C, hC, h⟩ := ThetaLower.theta_lower_bound
  intro h0
  have h1 := h ⟨z, hz⟩ 0
  rw [show thetaVec 0 ⟨z, hz⟩ = thetaC00 z from rfl, h0, norm_zero] at h1
  exact absurd h1 (not_le.mpr (Real.exp_pos _))

lemma thetaC10_ne_zero {z : ℂ} (hz : 0 < z.im) : thetaC10 z ≠ 0 := by
  obtain ⟨C, hC, h⟩ := ThetaLower.theta_lower_bound
  intro h0
  have h1 := h ⟨z, hz⟩ 2
  rw [show thetaVec 2 ⟨z, hz⟩ = thetaC10 z from rfl, h0, norm_zero] at h1
  exact absurd h1 (not_le.mpr (Real.exp_pos _))

lemma lamC_ne_zero {z : ℂ} (hz : 0 < z.im) : lamC z ≠ 0 := by
  rw [lamC, div_ne_zero_iff]
  exact ⟨pow_ne_zero 4 (thetaC10_ne_zero hz), pow_ne_zero 4 (thetaC00_ne_zero hz)⟩

lemma differentiableOn_lamC : DifferentiableOn ℂ lamC U := by
  show DifferentiableOn ℂ (fun z => (thetaC10 z)^4 / (thetaC00 z)^4) U
  exact (differentiableOn_thetaC10.pow 4).div (differentiableOn_thetaC00.pow 4)
    (fun z hz => pow_ne_zero 4 (thetaC00_ne_zero hz))

/-- There is a continuous (hence holomorphic) logarithm of `λ` on the upper half plane. -/
lemma exists_log_lamC : ∃ f : ℂ → ℂ, ContinuousOn f U ∧ DifferentiableOn ℂ f U ∧
    ∀ z ∈ U, Complex.exp (f z) = lamC z := by
  have hne : 0 ∉ lamC '' U := by
    rintro ⟨z, hz, h0⟩
    exact lamC_ne_zero hz h0
  obtain ⟨f, hfc, hfe⟩ := Complex.exists_continuousOn_eqOn_exp_comp isSimplyConnected_U
    isOpen_U differentiableOn_lamC.continuousOn hne
  exact ⟨f, hfc, Work.Analysis.BranchLog.holomorphic_of_exp hfc differentiableOn_lamC
    (fun z hz => lamC_ne_zero hz) hfe, hfe⟩


/-! ## The asymptotics of `LU` at the cusp `∞` -/

lemma tendsto_exp_neg_pi : Tendsto (fun T : ℝ => Real.exp (-(Real.pi*T))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (by
    rw [tendsto_atBot]
    intro b
    filter_upwards [eventually_ge_atTop (-b/Real.pi)] with T hT
    have h2 : -b ≤ Real.pi * T := by
      rw [div_le_iff₀ Real.pi_pos] at hT
      linarith
    linarith)

lemma tendsto_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.exp (-(c*T))) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (by
    rw [tendsto_atBot]
    intro b
    filter_upwards [eventually_ge_atTop (-b/c)] with T hT
    have h2 : -b ≤ c * T := by
      rw [div_le_iff₀ hc] at hT
      linarith
    linarith)

lemma tendsto_bound_zero (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => a * Real.exp (-(c*T)) / (1 - Real.exp (-(c*T)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => Real.exp (-(c*T))) atTop (𝓝 0) := tendsto_exp_neg_mul c hc
  have hnum : Tendsto (fun T : ℝ => a * Real.exp (-(c*T))) atTop (𝓝 (a*0)) :=
    tendsto_const_nhds.mul h1
  have hden : Tendsto (fun T : ℝ => 1 - Real.exp (-(c*T))) atTop (𝓝 (1-0)) :=
    tendsto_const_nhds.sub h1
  have hmain := hnum.div hden (by norm_num)
  have heq : (fun T : ℝ => a * Real.exp (-(c*T)) / (1 - Real.exp (-(c*T))))
      = ((fun T : ℝ => a * Real.exp (-(c*T))) / (fun T : ℝ => 1 - Real.exp (-(c*T)))) := by
    funext T; rw [Pi.div_apply]
  rw [heq]
  simpa only [mul_zero, sub_zero, div_one] using hmain

lemma tendsto_thetaC00_imag (c : ℝ) :
    Tendsto (fun T : ℝ => thetaC00 ((T:ℂ)*Complex.I + c)) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_bound_zero 2 Real.pi Real.pi_pos) (Eventually.of_forall (fun T => norm_nonneg _)) ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have him : ((T:ℂ)*Complex.I + c).im = T := by simp
  have h := norm_jacobiTheta_sub_one_le (τ := (T:ℂ)*Complex.I + c) (by rw [him]; linarith)
  rw [him, show -Real.pi * T = -(Real.pi*T) by ring] at h
  show ‖thetaC00 ((T:ℂ)*Complex.I + c) - 1‖ ≤ 2 * Real.exp (-(Real.pi*T)) / (1 - Real.exp (-(Real.pi*T)))
  rw [show thetaC00 ((T:ℂ)*Complex.I + c) = jacobiTheta ((T:ℂ)*Complex.I + c) from rfl]
  convert h using 1
  ring

lemma tendsto_ratio_imag (c : ℝ) :
    Tendsto (fun T : ℝ => jacobiTheta₂ (((T:ℂ)*Complex.I + c)/2) ((T:ℂ)*Complex.I + c)/2)
      atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_bound_zero 1 (2*Real.pi) (by positivity)) (Eventually.of_forall (fun T => norm_nonneg _)) ?_
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have him : ((T:ℂ)*Complex.I + c).im = T := by simp
  have h := ThetaLower.ratio_estimate ((T:ℂ)*Complex.I + c) (by rw [him]; linarith)
  rw [him] at h
  simpa using h

lemma tendsto_log_thetaC00_imag (c : ℝ) :
    Tendsto (fun T : ℝ => Complex.log (thetaC00 ((T:ℂ)*Complex.I + c))) atTop (𝓝 0) := by
  have h1 : (1:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp
  have h := (continuousAt_clog h1).tendsto.comp (tendsto_thetaC00_imag c)
  have h' : Tendsto (fun T : ℝ => Complex.log (thetaC00 ((T:ℂ)*Complex.I + c))) atTop (𝓝 (Complex.log 1)) := h
  simpa using h'

lemma tendsto_log_ratio_imag (c : ℝ) :
    Tendsto (fun T : ℝ => Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I + c)/2) ((T:ℂ)*Complex.I + c)/2))
      atTop (𝓝 0) := by
  have h1 : (1:ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp
  have h := (continuousAt_clog h1).tendsto.comp (tendsto_ratio_imag c)
  have h' : Tendsto (fun T : ℝ => Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I + c)/2) ((T:ℂ)*Complex.I + c)/2)) atTop (𝓝 (Complex.log 1)) := h
  simpa using h'

/-- `LU(z+1) - LU(z) → πi` as `im z → ∞` along the imaginary axis. -/
lemma tendsto_LU_diff :
    Tendsto (fun T : ℝ => LU ((T:ℂ)*Complex.I + 1) - LU ((T:ℂ)*Complex.I)) atTop
      (𝓝 (Real.pi * Complex.I)) := by
  have h0 : (fun T : ℝ => LU ((T:ℂ)*Complex.I + 1) - LU ((T:ℂ)*Complex.I))
      = fun T : ℝ => Real.pi*Complex.I
          + (4*Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I + 1)/2) ((T:ℂ)*Complex.I + 1)/2)
             - 4*Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I)/2) ((T:ℂ)*Complex.I)/2))
          - (4*Complex.log (thetaC00 ((T:ℂ)*Complex.I + 1)) - 4*Complex.log (thetaC00 ((T:ℂ)*Complex.I))) := by
    funext T
    rw [LU, LU, thetaC10_div_exp, thetaC10_div_exp]
    ring
  rw [h0]
  have hr : Tendsto (fun T : ℝ => 4*Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I + 1)/2) ((T:ℂ)*Complex.I + 1)/2)
      - 4*Complex.log (jacobiTheta₂ (((T:ℂ)*Complex.I)/2) ((T:ℂ)*Complex.I)/2)) atTop (𝓝 0) := by
    have h := (Filter.Tendsto.const_mul (4:ℂ) (tendsto_log_ratio_imag 1)).sub
      (Filter.Tendsto.const_mul (4:ℂ) (tendsto_log_ratio_imag 0))
    simpa using h
  have ht : Tendsto (fun T : ℝ => 4*Complex.log (thetaC00 ((T:ℂ)*Complex.I + 1))
      - 4*Complex.log (thetaC00 ((T:ℂ)*Complex.I))) atTop (𝓝 0) := by
    have h := (Filter.Tendsto.const_mul (4:ℂ) (tendsto_log_thetaC00_imag 1)).sub
      (Filter.Tendsto.const_mul (4:ℂ) (tendsto_log_thetaC00_imag 0))
    simpa using h
  have hconst : Tendsto (fun _ : ℝ => Real.pi * Complex.I) atTop (𝓝 (Real.pi * Complex.I)) :=
    tendsto_const_nhds
  have := (hconst.add hr).sub ht
  simpa using this


/-! ## Continuity of `LU` on `{im > 1}` and the chosen logarithm `L` -/

lemma norm_thetaC00_sub_one_lt {z : ℂ} (hz : 1 < z.im) : ‖thetaC00 z - 1‖ < 1 := by
  have h := norm_jacobiTheta_sub_one_le (τ := z) (by linarith)
  have h3 : Real.exp (-Real.pi * z.im) < 1/3 := by
    have h4 : (3:ℝ) < Real.exp (Real.pi * z.im) := by
      have := Real.add_one_le_exp (Real.pi * z.im)
      nlinarith [Real.pi_pos, hz, Real.pi_gt_three]
    have h5 : Real.exp (-Real.pi * z.im) = (Real.exp (Real.pi * z.im))⁻¹ := by
      rw [show -Real.pi * z.im = -(Real.pi * z.im) by ring, Real.exp_neg]
    rw [h5, show (1:ℝ)/3 = (3:ℝ)⁻¹ by norm_num, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simp only [inv_inv]
    exact h4
  have h2 : 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) < 1 := by
    rw [show 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im)
        = 2 * Real.exp (-Real.pi * z.im) / (1 - Real.exp (-Real.pi * z.im)) by ring,
      div_lt_one (by linarith)]
    linarith
  rw [show thetaC00 z - 1 = jacobiTheta z - 1 from rfl]
  exact lt_of_le_of_lt h h2

lemma thetaC00_mem_slitPlane {z : ℂ} (hz : 1 < z.im) : thetaC00 z ∈ Complex.slitPlane :=
  Work.Analysis.BranchLog.mem_slitPlane_of_norm_sub_one_lt (norm_thetaC00_sub_one_lt hz)

lemma ratio_mem_slitPlane {z : ℂ} (hz : 1 < z.im) :
    jacobiTheta₂ (z/2) z / 2 ∈ Complex.slitPlane :=
  Work.Analysis.BranchLog.mem_slitPlane_of_norm_sub_one_lt (im_ratio_small (le_of_lt hz))

lemma continuousOn_ratio : ContinuousOn (fun z : ℂ => jacobiTheta₂ (z/2) z / 2) V := by
  have h1 : ContinuousOn (fun z : ℂ => thetaC10 z / (2*Complex.exp (Real.pi*Complex.I*z/4))) V :=
    (differentiableOn_thetaC10.mono V_subset_U).continuousOn.div (by fun_prop)
      (fun z _ => mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))
  refine h1.congr (fun z _ => ?_)
  exact (thetaC10_div_exp z).symm

lemma continuousOn_LU : ContinuousOn LU V := by
  have h1 : ContinuousOn (fun z : ℂ => Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)) V := by fun_prop
  have h2 : ContinuousOn (fun z : ℂ => 4 * Complex.log (jacobiTheta₂ (z/2) z / 2)) V :=
    (continuousOn_ratio.clog (fun z hz => ratio_mem_slitPlane hz)).const_mul 4
  have h3 : ContinuousOn (fun z : ℂ => 4 * Complex.log (thetaC00 z)) V :=
    ((differentiableOn_thetaC00.mono V_subset_U).continuousOn.clog
      (fun z hz => thetaC00_mem_slitPlane hz)).const_mul 4
  have h4 : ContinuousOn (fun z : ℂ => Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)
      + 4 * Complex.log (jacobiTheta₂ (z/2) z / 2) - 4 * Complex.log (thetaC00 z)) V :=
    (h1.add h2).sub h3
  refine h4.congr (fun z _ => ?_)
  show LU z = Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)
      + 4 * Complex.log (jacobiTheta₂ (z/2) z / 2) - 4 * Complex.log (thetaC00 z)
  rw [LU, thetaC10_div_exp]


/-- The chosen logarithm `L` of `λ`, normalised so that `L = LU` on `{im > 1}`. -/
lemma exists_L : ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ (∀ z ∈ U, Complex.exp (L z) = lamC z)
    ∧ (∀ z ∈ V, L z = LU z) := by
  obtain ⟨f, hfc, hfd, hfe⟩ := exists_log_lamC
  have hVpre : IsPreconnected V := (convex_halfSpace_im_gt 1).isPreconnected
  have hval : ∀ z ∈ V, ∃ n : ℤ, (f - LU) z = n * (2 * Real.pi * Complex.I) := by
    intro z hz
    have hzU : z ∈ U := V_subset_U hz
    have h1 : Complex.exp ((f - LU) z) = 1 := by
      rw [Pi.sub_apply, Complex.exp_sub, hfe z hzU, exp_LU z hz]
      exact div_self (lamC_ne_zero hzU)
    exact Complex.exp_eq_one_iff.mp h1
  have hcont : ContinuousOn (f - LU) V :=
    (hfd.mono V_subset_U).continuousOn.sub continuousOn_LU
  have hz0 : (2 * Complex.I : ℂ) ∈ V := by simp [V]
  have hconst := Work.Analysis.DiscreteValues.eq_const_of_isPreconnected hVpre hcont hval hz0
  obtain ⟨n, hn⟩ := hval (2*Complex.I) hz0
  have hexp0 : Complex.exp (f (2*Complex.I) - LU (2*Complex.I)) = 1 := by
    rw [Pi.sub_apply] at hn
    rw [hn, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨fun z => f z - (f (2*Complex.I) - LU (2*Complex.I)), hfd.sub_const _, ?_, ?_⟩
  · intro z hz
    rw [Complex.exp_sub, hexp0, div_one]
    exact hfe z hz
  · intro z hz
    have hzc := hconst z hz
    rw [Pi.sub_apply, Pi.sub_apply] at hzc
    show f z - (f (2*Complex.I) - LU (2*Complex.I)) = LU z
    rw [← hzc]
    ring

end Work.Kernels.LogLambda
