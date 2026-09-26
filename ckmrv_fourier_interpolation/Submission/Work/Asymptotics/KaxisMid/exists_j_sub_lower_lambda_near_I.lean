import Mathlib
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.TildeFacts.E6Fun_eq_theta
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Rigidity.lambda_fiber_orbit
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.Asymptotics.KaxisMid

open UpperHalfPlane Work.Kernels
open Filter
open scoped Topology

noncomputable section

/-! ## `j` as the explicit rational function of `λ`

The modular `j`-invariant is the degree-six rational function `256 (x²-x+1)³/(x²(1-x)²)` of
`λ = θ₁₀⁴/θ₀₀⁴`.  We need this explicit formula (the proof of `Work.Asymptotics.KaxisMid.jInvariantFun_eq_lambda`
is not exported), and then rewrite it in the variable `u = λ - 1/2`, where it becomes the even
rational function `256 (3/4+u²)³/(1/4-u²)²`. -/

private lemma alg_theta (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a = c + b) :
    ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 / (a ^ 2 * b ^ 2 * c ^ 2 / 256)
      = 256 * ((b / a) ^ 2 - (b / a) + 1) ^ 3 / ((b / a) ^ 2 * (1 - b / a) ^ 2) := by
  subst hq
  have h1 : ((c + b) ^ 2 + b ^ 2 + c ^ 2) / 2 = (c + b) ^ 2 - (c + b) * b + b ^ 2 := by ring
  have h2 : (b / (c + b)) ^ 2 - b / (c + b) + 1
      = ((c + b) ^ 2 - (c + b) * b + b ^ 2) / (c + b) ^ 2 := by
    field_simp
    ring
  have h3 : 1 - b / (c + b) = c / (c + b) := by
    field_simp
    ring
  rw [h1, h2, h3]
  field_simp

private lemma jInvariantFun_eq_lambda (τ : ℍ) :
    jInvariantFun τ = 256 * (lambdaFun τ ^ 2 - lambdaFun τ + 1) ^ 3 /
      (lambdaFun τ ^ 2 * (1 - lambdaFun τ) ^ 2) := by
  have hE4 := Work.Residues.KMinusT_E4Fun_eq_theta τ
  have hD := Work.Residues.KMinusT_DeltaFun_eq_theta τ
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  have ha : UFun τ ≠ 0 := Work.Rigidity.UFun_ne_zero τ
  have hb : VFun τ ≠ 0 := Work.Rigidity.VFun_ne_zero τ
  have hc : WFun τ ≠ 0 := Work.Rigidity.WFun_ne_zero τ
  have hmain := alg_theta (UFun τ) (VFun τ) (WFun τ) ha hb hc hq
  rw [show jInvariantFun τ
      = ((UFun τ ^ 2 + VFun τ ^ 2 + WFun τ ^ 2) / 2) ^ 3
        / (UFun τ ^ 2 * VFun τ ^ 2 * WFun τ ^ 2 / 256) by
    rw [jInvariantFun, hE4, hD]]
  rw [hmain]

/-- The rational function of `u = λ - 1/2` computing `j`: `256 (3/4+u²)³/(1/4-u²)²`. -/
private def Phi (u : ℂ) : ℂ := 256 * (3 / 4 + u ^ 2) ^ 3 / (1 / 4 - u ^ 2) ^ 2

private lemma jInvariantFun_eq_Phi (τ : ℍ) : jInvariantFun τ = Phi (lambdaFun τ - 1 / 2) := by
  rw [jInvariantFun_eq_lambda τ]
  unfold Phi
  rw [show lambdaFun τ ^ 2 - lambdaFun τ + 1 = 3 / 4 + (lambdaFun τ - 1 / 2) ^ 2 by ring,
      show lambdaFun τ ^ 2 * (1 - lambdaFun τ) ^ 2
            = (1 / 4 - (lambdaFun τ - 1 / 2) ^ 2) ^ 2 by ring]

/-! ## The factorization of `j τ - j z`

With `u = λ τ - 1/2`, `v = λ z - 1/2` we have `u² - v² = (λ τ - λ z)(λ τ + λ z - 1)`, and the
difference `Phi u - Phi v` factors through `u² - v²` because the two "numerator" polynomials
agree at `u² = v²`.  Concretely, the polynomial identity

  `(3/4+A)³(1/4-B)² - (3/4+B)³(1/4-A)² = (A-B) T(A,B)`

with `T` the explicit polynomial below, is the whole algebraic content.  The value
`T(0,0) = 81/256` is non-zero, which is what makes the two `λ`-factors `λ τ - λ z` and
`λ τ + λ z - 1` control `j τ - j z` near `τ = z = i` (`u = v = 0`). -/

/-- The polynomial `T` with `(A-B) T(A,B) = (3/4+A)³(1/4-B)² - (3/4+B)³(1/4-A)²`. -/
private def Tp (A B : ℂ) : ℂ :=
  81 / 256 - 9 / 32 * (A + B) + 1 / 16 * (A ^ 2 + B ^ 2) - 11 / 4 * (A * B)
    - 1 / 2 * (A * B * (A + B)) + A ^ 2 * B ^ 2

private lemma Tp_spec (A B : ℂ) :
    (3 / 4 + A) ^ 3 * (1 / 4 - B) ^ 2 - (3 / 4 + B) ^ 3 * (1 / 4 - A) ^ 2
      = (A - B) * Tp A B := by
  unfold Tp; ring

/-- The explicit function `Ψ` with `Phi u - Phi v = (u - v)(u + v) Ψ u v`. -/
private def Psi (a b : ℂ) : ℂ :=
  256 * Tp (a ^ 2) (b ^ 2) / ((1 / 4 - a ^ 2) ^ 2 * (1 / 4 - b ^ 2) ^ 2)

private lemma Phi_sub (a b : ℂ) (ha : 1 / 4 - a ^ 2 ≠ 0) (hb : 1 / 4 - b ^ 2 ≠ 0) :
    Phi a - Phi b = (a - b) * (a + b) * Psi a b := by
  have hnum : (3 / 4 + a ^ 2) ^ 3 * (1 / 4 - b ^ 2) ^ 2
        - (3 / 4 + b ^ 2) ^ 3 * (1 / 4 - a ^ 2) ^ 2
      = (a - b) * (a + b) * Tp (a ^ 2) (b ^ 2) := by
    have := Tp_spec (a ^ 2) (b ^ 2); rw [this]; ring
  unfold Phi Psi
  rw [div_sub_div _ _ (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)]
  rw [show 256 * (3 / 4 + a ^ 2) ^ 3 * (1 / 4 - b ^ 2) ^ 2
        - (1 / 4 - a ^ 2) ^ 2 * (256 * (3 / 4 + b ^ 2) ^ 3)
      = 256 * ((3 / 4 + a ^ 2) ^ 3 * (1 / 4 - b ^ 2) ^ 2
        - (3 / 4 + b ^ 2) ^ 3 * (1 / 4 - a ^ 2) ^ 2) by ring]
  rw [hnum]
  ring

/-- **Exact factorization of the `j`-difference near the diagonal.** -/
private lemma jSub_eq (τ z : ℍ) :
    jInvariantFun τ - jInvariantFun z
      = (lambdaFun τ - lambdaFun z) * (lambdaFun τ + lambdaFun z - 1)
        * Psi (lambdaFun τ - 1 / 2) (lambdaFun z - 1 / 2) := by
  have h1 : (1 : ℂ) / 4 - (lambdaFun τ - 1 / 2) ^ 2 ≠ 0 := by
    have hfac : (1 : ℂ) / 4 - (lambdaFun τ - 1 / 2) ^ 2
        = lambdaFun τ * (1 - lambdaFun τ) := by ring
    rw [hfac]
    exact mul_ne_zero (Work.Rigidity.lambdaFun_ne_zero τ)
      (sub_ne_zero.mpr (Work.Rigidity.lambdaFun_ne_one τ).symm)
  have h2 : (1 : ℂ) / 4 - (lambdaFun z - 1 / 2) ^ 2 ≠ 0 := by
    have hfac : (1 : ℂ) / 4 - (lambdaFun z - 1 / 2) ^ 2
        = lambdaFun z * (1 - lambdaFun z) := by ring
    rw [hfac]
    exact mul_ne_zero (Work.Rigidity.lambdaFun_ne_zero z)
      (sub_ne_zero.mpr (Work.Rigidity.lambdaFun_ne_one z).symm)
  have hmain := Phi_sub (lambdaFun τ - 1 / 2) (lambdaFun z - 1 / 2) h1 h2
  have e1 : (lambdaFun τ - 1 / 2) - (lambdaFun z - 1 / 2) = lambdaFun τ - lambdaFun z := by ring
  have e2 : (lambdaFun τ - 1 / 2) + (lambdaFun z - 1 / 2)
      = lambdaFun τ + lambdaFun z - 1 := by ring
  rw [jInvariantFun_eq_Phi τ, jInvariantFun_eq_Phi z, hmain, e1, e2]

/-! ## Analytic inputs: `Ψ` is continuous and non-zero at the origin

`Psi 0 0 = 256 · (81/256) / (1/4)⁴ = 20736 ≠ 0`, so by continuity `‖Psi a b‖ ≥ 20736/2` on a
neighbourhood of the origin. -/

private lemma Psi_zero : Psi 0 0 = 20736 := by
  unfold Psi Tp; norm_num

private lemma Tp_continuous : Continuous fun p : ℂ × ℂ => Tp (p.1 ^ 2) (p.2 ^ 2) := by
  unfold Tp; fun_prop

private lemma Psi_den_continuous : Continuous fun p : ℂ × ℂ =>
    (1 / 4 - p.1 ^ 2) ^ 2 * (1 / 4 - p.2 ^ 2) ^ 2 := by
  fun_prop

private lemma continuousAt_Psi : ContinuousAt (fun p : ℂ × ℂ => Psi p.1 p.2) (0, 0) := by
  have hnum : ContinuousAt (fun p : ℂ × ℂ => (256 : ℂ) * Tp (p.1 ^ 2) (p.2 ^ 2)) (0, 0) :=
    (continuous_const.mul Tp_continuous).continuousAt
  have hne : (1 / 4 - (0 : ℂ) ^ 2) ^ 2 * (1 / 4 - (0 : ℂ) ^ 2) ^ 2 ≠ 0 := by norm_num
  exact hnum.div Psi_den_continuous.continuousAt hne

/-- On a Euclidean neighbourhood of the origin, `‖Ψ‖` is bounded below by `10368 = 20736/2`. -/
private lemma exists_delta_Psi :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℂ, ‖a‖ < δ → ‖b‖ < δ → (10368 : ℝ) ≤ ‖Psi a b‖ := by
  have h := (Metric.continuousAt_iff.mp continuousAt_Psi) 10368 (by norm_num)
  obtain ⟨δ, hδpos, hδ⟩ := h
  refine ⟨δ, hδpos, fun a b ha hb => ?_⟩
  have hp : dist ((a, b) : ℂ × ℂ) ((0, 0) : ℂ × ℂ) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_zero_right]
    exact max_lt ha hb
  have h2 := hδ hp
  rw [Psi_zero] at h2
  rw [dist_eq_norm] at h2
  have h4 : ‖(20736 : ℂ)‖ - ‖Psi a b‖ ≤ ‖(20736 : ℂ) - Psi a b‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at h4
  have h20736 : ‖(20736 : ℂ)‖ = (20736 : ℝ) := by norm_num
  rw [h20736] at h4
  linarith

/-- `λ(i) = 1/2` and `λ` is continuous at `i`; hence a Euclidean neighbourhood of `i` is mapped
into the `δ`-ball of `1/2`. -/
private lemma exists_rho_near_I (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : ℍ, ‖(τ : ℂ) - Complex.I‖ < ρ →
      ‖lambdaFun τ - 1 / 2‖ < δ := by
  have hI : 0 < Complex.I.im := by simp
  have hval : Work.Kernels.LogLambda.lamC Complex.I = 1 / 2 := by
    have hEq : (-1 : ℂ) / Complex.I = Complex.I := by
      rw [neg_div, one_div, Complex.inv_I, neg_neg]
    have h := Work.Rigidity.lamC_neg_inv Complex.I hI
    rw [hEq] at h
    linear_combination (1 / 2 : ℂ) * h
  have hcont : ContinuousAt (fun w : ℂ => Work.Kernels.LogLambda.lamC w) Complex.I :=
    (Work.Kernels.LogLambda.differentiableOn_lamC.continuousOn).continuousAt
      (Work.Kernels.LogLambda.isOpen_U.mem_nhds hI)
  have hnb : Metric.ball (1 / 2 : ℂ) δ ∈ 𝓝 (Work.Kernels.LogLambda.lamC Complex.I) := by
    rw [hval]; exact Metric.ball_mem_nhds _ hδ
  have hev : ∀ᶠ w in 𝓝 Complex.I, ‖Work.Kernels.LogLambda.lamC w - 1 / 2‖ < δ := by
    have h : ∀ᶠ w in 𝓝 Complex.I, Work.Kernels.LogLambda.lamC w ∈ Metric.ball (1 / 2 : ℂ) δ :=
      hcont.eventually hnb
    simpa only [Metric.mem_ball, dist_eq_norm] using h
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρpos, hρ⟩ := hev
  refine ⟨ρ, hρpos, fun τ hτ => ?_⟩
  have hd : dist (τ : ℂ) Complex.I < ρ := by rwa [dist_eq_norm]
  have h1 : ‖Work.Kernels.LogLambda.lamC (τ : ℂ) - 1 / 2‖ < δ := hρ hd
  rwa [Work.Rigidity.lamC_coe τ] at h1

/-! ## The theorem -/

/-- **The `j`-difference near `i` is comparable to the product of the two `λ`-distances.**  Near
`τ = z = i` one has the exact factorization
`j τ - j z = 256 (λ τ - λ z)(λ τ + λ z - 1) R`, where `R` is the divided difference of the explicit
rational function `s ↦ s ((9/4-s)/(1/4-s))²` (equivalently `j = 256(1-λ+λ²)³/(λ²(1-λ)²)`), and
`R = 81 ≠ 0` at `s = t = 0`; hence the product of the two `λ`-factors controls `‖j τ - j z‖`. -/
theorem exists_j_sub_lower_lambda_near_I :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
      c * ‖Work.Kernels.lambdaFun τ - Work.Kernels.lambdaFun z‖
        * ‖Work.Kernels.lambdaFun τ + Work.Kernels.lambdaFun z - 1‖
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_Psi
  obtain ⟨ρ, hρpos, hρ⟩ := exists_rho_near_I δ hδpos
  refine ⟨ρ, hρpos, 10368, by norm_num, fun τ z hτ hz => ?_⟩
  have hτ' : ‖lambdaFun τ - 1 / 2‖ < δ := hρ τ hτ
  have hz' : ‖lambdaFun z - 1 / 2‖ < δ := hρ z hz
  have hPsi := hδ (lambdaFun τ - 1 / 2) (lambdaFun z - 1 / 2) hτ' hz'
  rw [jSub_eq τ z, norm_mul, norm_mul]
  have h1 : (0 : ℝ) ≤ ‖lambdaFun τ - lambdaFun z‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖lambdaFun τ + lambdaFun z - 1‖ := norm_nonneg _
  calc (10368 : ℝ) * ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖
      = 10368 * (‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖) := by ring
    _ ≤ ‖Psi (lambdaFun τ - 1 / 2) (lambdaFun z - 1 / 2)‖
          * (‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖) :=
        mul_le_mul_of_nonneg_right hPsi (mul_nonneg h1 h2)
    _ = ‖lambdaFun τ - lambdaFun z‖ * ‖lambdaFun τ + lambdaFun z - 1‖
          * ‖Psi (lambdaFun τ - 1 / 2) (lambdaFun z - 1 / 2)‖ := by ring

end

end Work.Asymptotics.KaxisMid
