import Mathlib
import Submission.Work.Rigidity.LambdaFiberDefs
import Submission.Work.Rigidity.lambdaFun_div_qParam_tendsto
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries
import Submission.Work.Rigidity.lambda_local_surjective
import Submission.Work.Rigidity.lambda_local_inverse

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups

namespace Work.Rigidity

open Work.Kernels

/-!
# Continuity of the fibres of `λ` in the value

`λ : ℍ → ℂ ∖ {0,1}` has the fundamental domain `FDom` of `Γ(2)`, and `λ` is a local
biholomorphism.  The lemma `lambda_fiber_close` says that the preimage of a value `w'` close to
a given value `w` inside `FDom` consists of points close to the preimage of `w`.

The proof is a compactness argument: a sequence `τ'_n ∈ FDom` with `λ(τ'_n) → w` cannot escape
to the cusps (`λ → 0` at `i∞`, `λ → 1` at `0` and `|λ| → ∞` at `±1`), so it stays in a fixed
compact piece of `FDom`, where a convergent subsequence converges to a point `τ` with
`λ τ = w`.

This file develops the cusp asymptotics of `λ` along the fundamental domain and the final
compactness argument.
-/

/-! ## Cusp asymptotics of `λ` -/

/-- The "cone at `a`" condition `|Re z - a| ≤ 2 (Im z)²`.  Points of `FDom` tending to the cusp
`0` or `1` eventually satisfy it (`a = 0` resp. `a = 1`), which is exactly what is needed to
control the imaginary part of `-1/z`. -/
def ConeAt (a : ℝ) (z : ℂ) : Prop := |z.re - a| ≤ 2 * z.im ^ 2

/-- For `z` with `|Re z| ≤ 2 (Im z)²` and `Im z ≤ 1/2`, the translate `-1/z` has
`Im (-1/z) ≥ 1/(2 Im z)`. -/
lemma cone_zero_inv_im {z : ℂ} (him : 0 < z.im) (him2 : z.im ≤ 1/2)
    (hcone : |z.re| ≤ 2 * z.im ^ 2) : 1/(2*z.im) ≤ (-z⁻¹).im := by
  have hz : z ≠ 0 := by intro h; rw [h] at him; simp at him
  have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  rw [show (-z⁻¹).im = z.im / Complex.normSq z by
    rw [Complex.neg_im, Complex.inv_im]; simp [div_eq_mul_inv]]
  rw [div_le_div_iff₀ (by positivity) hns]
  rw [Complex.normSq_apply]
  have h1 : z.re ^ 2 ≤ z.im ^ 2 := by
    have him2' : z.im ^ 2 ≤ 1/4 := by nlinarith
    nlinarith [abs_le.mp hcone, sq_nonneg z.im, sq_abs z.re]
  nlinarith

/-- **Decay of `λ` at the cusp `i∞`**, uniform in the real part: for `Im τ ≥ R` the value
`λ τ` is small in modulus.  This is immediate from the `q`-expansion
`λ(τ) = lambdaSeries (e^{π i τ})` together with `lambdaSeries ζ → 0` as `ζ → 0`. -/
lemma lambdaFun_norm_lt_of_im_large (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ : ℍ, R ≤ τ.im → ‖lambdaFun τ‖ < ε := by
  have hcont : ContinuousAt lambdaSeries 0 :=
    lambdaSeries_hasStrictDerivAt.hasDerivAt.continuousAt
  have hball : Metric.ball (0:ℂ) ε ∈ 𝓝 (lambdaSeries 0) := by
    rw [lambdaSeries_zero]; exact Metric.ball_mem_nhds 0 hε
  have hev : ∀ᶠ ζ in 𝓝 (0:ℂ), lambdaSeries ζ ∈ Metric.ball 0 ε := hcont.eventually hball
  obtain ⟨r, hr, hrf⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨Real.log (1/r) / Real.pi + 1, fun τ hτ => ?_⟩
  have hre : (↑Real.pi * Complex.I * ↑τ : ℂ).re = -(Real.pi * τ.im) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
    ring
  have hexp : ‖Complex.exp (↑Real.pi * Complex.I * ↑τ)‖ < r := by
    rw [Complex.norm_exp, hre]
    have hmono : Real.exp (-(Real.pi * τ.im))
        ≤ Real.exp (-(Real.pi * (Real.log (1/r) / Real.pi + 1))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hτ, Real.pi_pos]
    refine lt_of_le_of_lt hmono ?_
    have key : -(Real.pi * (Real.log (1/r) / Real.pi + 1)) = Real.log r - Real.pi := by
      rw [one_div, Real.log_inv]; field_simp; ring
    rw [key, Real.exp_sub, Real.exp_log hr]
    rw [div_lt_iff₀ (Real.exp_pos Real.pi)]
    nlinarith [hr, Real.one_lt_exp_iff.mpr Real.pi_pos]
  calc ‖lambdaFun τ‖ = ‖lambdaSeries (Complex.exp (↑Real.pi * Complex.I * ↑τ))‖ := by
        rw [lambdaFun_eq_lambdaSeries]
    _ < ε := by
        have h := hrf (y := Complex.exp (↑Real.pi * Complex.I * ↑τ))
          (by simpa [dist_eq_norm] using hexp)
        simpa [Metric.mem_ball, dist_eq_norm] using h

/-- **`λ` approaches the cusp `0`**: points of `FDom` tending to `0` satisfy the cone condition
at `0`. -/
lemma cone_zero_of_FDom_tendsto_zero (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ConeAt 0 (τ n : ℂ) := by
  rw [Filter.eventually_atTop]
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have hnorm : ‖(τ n : ℂ)‖ < 1/2 := by
    have := hN n hn; rwa [dist_zero_right] at this
  have hre_lt : |(τ n : ℂ).re| < 1/2 := lt_of_le_of_lt (Complex.abs_re_le_norm _) hnorm
  have hns : Complex.normSq (τ n : ℂ) ≥ |(τ n : ℂ).re| := by
    rw [Complex.normSq_eq_norm_sq]; exact (hFD n).2
  rw [ConeAt, sub_zero]
  rw [Complex.normSq_apply] at hns
  have hx2 : (τ n : ℂ).re ^ 2 ≤ |(τ n : ℂ).re| / 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (τ n : ℂ).re, hre_lt]
  nlinarith [abs_nonneg (τ n : ℂ).re]

/-- **`λ` approaches the cusp `1`**: points of `FDom` tending to `1` satisfy the cone condition
at `1`. -/
lemma cone_one_of_FDom_tendsto_one (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, ConeAt 1 (τ n : ℂ) := by
  rw [Filter.eventually_atTop]
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have hnorm : ‖(τ n : ℂ) - 1‖ < 1/2 := by
    have := hN n hn; rwa [dist_eq_norm] at this
  have hre_gt : 1/2 < (τ n : ℂ).re := by
    have h1 : |(τ n : ℂ).re - 1| ≤ ‖(τ n : ℂ) - 1‖ := by
      have := Complex.abs_re_le_norm ((τ n : ℂ) - 1); simpa using this
    have := abs_lt.mp (lt_of_le_of_lt h1 hnorm)
    linarith [this.2]
  have hns : Complex.normSq (τ n : ℂ) ≥ |(τ n : ℂ).re| := by
    rw [Complex.normSq_eq_norm_sq]; exact (hFD n).2
  have hre_le : (τ n : ℂ).re ≤ 1 := le_trans (le_abs_self _) (hFD n).1
  have hre_pos : 0 < (τ n : ℂ).re := by linarith
  change |(τ n : ℂ).re - 1| ≤ 2 * (τ n : ℂ).im ^ 2
  rw [Complex.normSq_apply] at hns
  rw [abs_of_pos hre_pos] at hns
  rw [abs_of_nonpos (by linarith : (τ n : ℂ).re - 1 ≤ 0)]
  nlinarith

/-- The translation `T²` acts on `ℍ` as `τ ↦ τ + 2`. -/
lemma T2_smul_coe (τ : ℍ) : ((ModularGroup.T ^ 2 • τ : ℍ) : ℂ) = (τ : ℂ) + 2 := by
  have h : (ModularGroup.T ^ 2 • τ : ℍ) = (2:ℝ) +ᵥ τ := by
    rw [pow_two, mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_T_smul,
      ← add_vadd]; norm_num
  rw [h, coe_vadd]; push_cast; ring

/-- **`λ` approaches the cusp `-1`**: points of `FDom` tending to `-1` satisfy the cone
condition at `1` after translation by `2`. -/
lemma cone_one_of_FDom_tendsto_neg_one (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 (-1))) :
    ∀ᶠ n in atTop, ConeAt 1 ((τ n : ℂ) + 2) := by
  rw [Filter.eventually_atTop]
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have hnorm : ‖(τ n : ℂ) - (-1)‖ < 1/2 := by
    have := hN n hn; rwa [dist_eq_norm] at this
  have hre_le : (τ n : ℂ).re ≤ -1/2 := by
    have h1 : |(τ n : ℂ).re - (-1)| ≤ ‖(τ n : ℂ) - (-1)‖ := by
      have := Complex.abs_re_le_norm ((τ n : ℂ) - (-1)); simpa using this
    have := (abs_lt.mp (lt_of_le_of_lt h1 hnorm)).2
    linarith
  have hre_ge : -1 ≤ (τ n : ℂ).re := by
    have := (abs_le.mp (hFD n).1).1
    linarith
  have hns : Complex.normSq (τ n : ℂ) ≥ |(τ n : ℂ).re| := by
    rw [Complex.normSq_eq_norm_sq]; exact (hFD n).2
  have hre_neg : (τ n : ℂ).re < 0 := by linarith
  change |((τ n : ℂ) + 2).re - 1| ≤ 2 * ((τ n : ℂ) + 2).im ^ 2
  have hre2 : ((τ n : ℂ) + 2).re = (τ n : ℂ).re + 2 := by simp
  have him2 : ((τ n : ℂ) + 2).im = (τ n : ℂ).im := by simp
  rw [hre2, him2, Complex.normSq_apply] at *
  rw [abs_of_neg hre_neg] at hns
  rw [show (τ n : ℂ).re + 2 - 1 = (τ n : ℂ).re + 1 by ring]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (τ n : ℂ).re + 1)]
  nlinarith

/-- If `f n → 0` in norm in the `∀ε` sense then `f → 0`. -/
lemma tendsto_zero_of_eventually_norm_lt {f : ℕ → ℂ}
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ‖f n‖ < ε) : Tendsto f atTop (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h ε hε)
  refine ⟨N, fun n hn => ?_⟩
  simpa [Real.dist_eq, dist_eq_norm, abs_of_nonneg (norm_nonneg _)] using hN n hn

/-- Along the cone at `0` the imaginary part of `-1/z` tends to `+∞`. -/
lemma tendsto_neg_inv_im_atTop_of_cone_zero (σ : ℕ → ℍ)
    (h0 : Tendsto (fun n => (σ n : ℂ)) atTop (𝓝 0))
    (hcone : ∀ᶠ n in atTop, ConeAt 0 (σ n : ℂ)) :
    Tendsto (fun n => (-((σ n : ℂ))⁻¹).im) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  set c : ℝ := max b 0 + 1 with hc
  have hcb : b ≤ c := by rw [hc]; linarith [le_max_left b 0]
  have hcpos : 0 < c := by rw [hc]; linarith [le_max_right b 0]
  set M : ℝ := min (1/2) (1/(2*c)) with hM
  have hMpos : 0 < M := lt_min (by norm_num) (by positivity)
  have hinev : ∀ᶠ n in atTop, (σ n : ℂ).im < M := by
    rw [Metric.tendsto_atTop] at h0
    filter_upwards [Filter.eventually_atTop.2 (h0 M hMpos)] with n hn
    rw [dist_zero_right] at hn
    exact lt_of_le_of_lt (Complex.im_le_norm _) hn
  filter_upwards [hcone, hinev] with n hcon him
  have himpos : 0 < (σ n : ℂ).im := (σ n).im_pos
  have him2 : (σ n : ℂ).im ≤ 1/2 := le_of_lt (lt_of_lt_of_le him (min_le_left _ _))
  have himle : (σ n : ℂ).im ≤ 1/(2*c) := le_of_lt (lt_of_lt_of_le him (min_le_right _ _))
  have hstep : 1/(2*(σ n : ℂ).im) ≤ (-((σ n : ℂ))⁻¹).im := by
    refine cone_zero_inv_im himpos him2 ?_
    simpa only [ConeAt, sub_zero] using hcon
  have hc_le : c ≤ 1/(2*(σ n : ℂ).im) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*(σ n : ℂ).im)]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2*c)] at himle
    linarith
  linarith

/-- **`λ → 1` along the cone at `0`.** -/
lemma tendsto_lambdaFun_one_of_cone_zero (σ : ℕ → ℍ)
    (h0 : Tendsto (fun n => (σ n : ℂ)) atTop (𝓝 0))
    (hcone : ∀ᶠ n in atTop, ConeAt 0 (σ n : ℂ)) :
    Tendsto (fun n => lambdaFun (σ n)) atTop (𝓝 1) := by
  have hS := tendsto_neg_inv_im_atTop_of_cone_zero σ h0 hcone
  have hg : Tendsto (fun n => lambdaFun (ModularGroup.S • σ n)) atTop (𝓝 0) := by
    apply tendsto_zero_of_eventually_norm_lt
    intro ε hε
    obtain ⟨R, hR⟩ := lambdaFun_norm_lt_of_im_large ε hε
    filter_upwards [hS.eventually (eventually_ge_atTop R)] with n hn
    have him : (ModularGroup.S • σ n : ℍ).im = (-((σ n : ℂ))⁻¹).im := by
      rw [← UpperHalfPlane.coe_im, Work.Kernels.coe_S_smul, inv_neg]
    refine hR (ModularGroup.S • σ n) ?_
    rw [him]; exact hn
  have hrel : ∀ n, lambdaFun (σ n) = 1 - lambdaFun (ModularGroup.S • σ n) := by
    intro n
    have h1 := lambdaFun_add_lambdaSFun (σ n)
    have h2 := Work.Kernels.LogLambda.lambdaFun_S (σ n)
    rw [← h2] at h1
    rw [eq_sub_iff_add_eq]
    exact h1
  have hfin : Tendsto (fun n => 1 - lambdaFun (ModularGroup.S • σ n)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hg
  rw [sub_zero] at hfin
  exact Tendsto.congr (fun n => (hrel n).symm) hfin

/-- **`λ → ∞` along the cone at `1`.**  Writing `σ = 1 + v` we have `λ(σ) = -λ(v)/(λ_S v)`
with `λ(v) → 1` and `λ_S(v) → 0`. -/
lemma tendsto_lambdaFun_norm_atTop_of_cone_one (σ : ℕ → ℍ)
    (h1 : Tendsto (fun n => (σ n : ℂ)) atTop (𝓝 1))
    (hcone : ∀ᶠ n in atTop, ConeAt 1 (σ n : ℂ)) :
    Tendsto (fun n => ‖lambdaFun (σ n)‖) atTop atTop := by
  let v : ℕ → ℍ := fun n => (-1 : ℝ) +ᵥ σ n
  have hvcoe : ∀ n, (v n : ℂ) = (σ n : ℂ) - 1 := by
    intro n
    show (((-1:ℝ) +ᵥ σ n : ℍ) : ℂ) = (σ n : ℂ) - 1
    rw [coe_vadd]; push_cast; ring
  have hv0 : Tendsto (fun n => (v n : ℂ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => (σ n : ℂ) - 1) atTop (𝓝 ((1:ℂ) - 1)) :=
      h1.sub tendsto_const_nhds
    rw [sub_self] at h2
    exact Tendsto.congr (fun n => (hvcoe n).symm) h2
  have hvcone : ∀ᶠ n in atTop, ConeAt 0 (v n : ℂ) := by
    filter_upwards [hcone] with n hn
    have hre : (v n : ℂ).re = (σ n : ℂ).re - 1 := by
      rw [hvcoe, Complex.sub_re, Complex.one_re]
    have him : (v n : ℂ).im = (σ n : ℂ).im := by
      rw [hvcoe, Complex.sub_im, Complex.one_im, sub_zero]
    rw [ConeAt] at hn ⊢
    rw [hre, him, sub_zero]
    exact hn
  have hvlam : Tendsto (fun n => lambdaFun (v n)) atTop (𝓝 1) :=
    tendsto_lambdaFun_one_of_cone_zero v hv0 hvcone
  have hlamS : Tendsto (fun n => lambdaSFun (v n)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 1 - lambdaFun (v n)) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub hvlam
    rw [sub_self] at h2
    refine Tendsto.congr (fun n => ?_) h2
    have h3 := lambdaFun_add_lambdaSFun (v n)
    rw [sub_eq_iff_eq_add, add_comm]
    exact h3.symm
  rw [tendsto_atTop]
  intro a
  have hge : ∀ᶠ n in atTop, (1:ℝ)/2 ≤ ‖lambdaFun (v n)‖ := by
    have hball : Metric.ball (1:ℂ) (1/2) ∈ 𝓝 (1:ℂ) := Metric.ball_mem_nhds 1 (by norm_num)
    filter_upwards [hvlam.eventually hball] with n hn
    rw [dist_eq_norm] at hn
    have h := abs_norm_sub_norm_le (lambdaFun (v n)) (1:ℂ)
    simp only [norm_one] at h
    have := (abs_le.mp h).1
    linarith
  have hsmall : ∀ᶠ n in atTop, ‖lambdaSFun (v n)‖ < 1/(2*((|a|)+1)) := by
    have hε : (0:ℝ) < 1/(2*((|a|)+1)) := by positivity
    have hmem := hlamS.eventually (Metric.ball_mem_nhds (0:ℂ) hε)
    filter_upwards [hmem] with n hn
    rw [dist_zero_right] at hn
    exact hn
  filter_upwards [hge, hsmall] with n hge_n hsmall_n
  have hσeq : σ n = ModularGroup.T • v n := by
    show σ n = ModularGroup.T • ((-1:ℝ) +ᵥ σ n)
    rw [UpperHalfPlane.modular_T_smul]
    show σ n = (1:ℝ) +ᵥ ((-1:ℝ) +ᵥ σ n)
    rw [← add_vadd]; norm_num
  rw [hσeq, Work.Kernels.LogLambda.lambdaFun_T, norm_div, norm_neg]
  rw [le_div_iff₀ (norm_pos_iff.mpr (lambdaSFun_ne_zero (v n)))]
  have hD : ((|a|)+1) * (1/(2*((|a|)+1))) = 1/2 := by field_simp
  have ha : a ≤ (|a|)+1 := by linarith [le_abs_self a]
  have hsnn : 0 ≤ ‖lambdaSFun (v n)‖ := norm_nonneg _
  have step1 : a * ‖lambdaSFun (v n)‖ ≤ ((|a|)+1) * ‖lambdaSFun (v n)‖ :=
    mul_le_mul_of_nonneg_right ha hsnn
  have step2 : ((|a|)+1) * ‖lambdaSFun (v n)‖ ≤ ((|a|)+1) * (1/(2*((|a|)+1))) :=
    mul_le_mul_of_nonneg_left hsmall_n.le (by positivity)
  rw [hD] at step2
  linarith

/-- `λ → 1` for a sequence in `FDom` converging to the cusp `0`. -/
lemma lambdaFun_tendsto_one_of_FDom_tendsto_zero (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun n => lambdaFun (τ n)) atTop (𝓝 1) :=
  tendsto_lambdaFun_one_of_cone_zero τ h (cone_zero_of_FDom_tendsto_zero τ hFD h)

/-- `|λ| → ∞` for a sequence in `FDom` converging to the cusp `1`. -/
lemma lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_one (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 1)) :
    Tendsto (fun n => ‖lambdaFun (τ n)‖) atTop atTop :=
  tendsto_lambdaFun_norm_atTop_of_cone_one τ h (cone_one_of_FDom_tendsto_one τ hFD h)

/-- `|λ| → ∞` for a sequence in `FDom` converging to the cusp `-1`. -/
lemma lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_neg_one (τ : ℕ → ℍ) (hFD : ∀ n, τ n ∈ FDom)
    (h : Tendsto (fun n => (τ n : ℂ)) atTop (𝓝 (-1))) :
    Tendsto (fun n => ‖lambdaFun (τ n)‖) atTop atTop := by
  have hσ : Tendsto (fun n => ((ModularGroup.T ^ 2 • τ n : ℍ) : ℂ)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun n => (τ n : ℂ) + 2) atTop (𝓝 ((-1:ℂ) + 2)) :=
      h.add (tendsto_const_nhds (x := (2:ℂ)))
    have h4 : ((-1:ℂ) + 2) = 1 := by norm_num
    rw [h4] at h3
    exact Tendsto.congr (fun n => (T2_smul_coe (τ n)).symm) h3
  have hconev : ∀ᶠ n in atTop, ConeAt 1 (((ModularGroup.T ^ 2 • τ n : ℍ)) : ℂ) := by
    filter_upwards [cone_one_of_FDom_tendsto_neg_one τ hFD h] with n hn
    rw [T2_smul_coe (τ n)]
    exact hn
  have hmain := tendsto_lambdaFun_norm_atTop_of_cone_one (fun n => ModularGroup.T ^ 2 • τ n)
    hσ hconev
  exact Tendsto.congr (fun n => by rw [lambdaFun_T2]) hmain

/-! ## The compact piece of `FDom` -/

/-- The piece of (the closure of) `FDom` between the imaginary parts `δ` and `M`, as a subset
of `ℂ`.  For `δ > 0` it is compact and contained in `ℍ`. -/
def KF (δ M : ℝ) : Set ℂ :=
  {z | |z.re| ≤ 1 ∧ Complex.normSq z ≥ |z.re| ∧ δ ≤ z.im ∧ z.im ≤ M}

lemma isCompact_KF (δ M : ℝ) : IsCompact (KF δ M) := by
  have hA : IsClosed {z : ℂ | |z.re| ≤ (1:ℝ)} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
  have hB : IsClosed {z : ℂ | Complex.normSq z ≥ |z.re|} :=
    isClosed_le (continuous_abs.comp Complex.continuous_re) Complex.continuous_normSq
  have hC : IsClosed {z : ℂ | δ ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hD : IsClosed {z : ℂ | z.im ≤ M} := isClosed_le Complex.continuous_im continuous_const
  have hclosed : IsClosed (KF δ M) := by
    rw [show KF δ M = {z : ℂ | |z.re| ≤ (1:ℝ)} ∩ {z : ℂ | Complex.normSq z ≥ |z.re|} ∩
      {z : ℂ | δ ≤ z.im} ∩ {z : ℂ | z.im ≤ M} from by
        ext z; simp [KF, and_assoc]]
    exact ((hA.inter hB).inter hC).inter hD
  have hbdd : Bornology.IsBounded (KF δ M) := by
    refine (Metric.isBounded_closedBall (x := (0:ℂ)) (r := |M| + |δ| + 1)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |z.re| ≤ (1:ℝ) := hz.1
    have hδ : δ ≤ z.im := hz.2.2.1
    have hM : z.im ≤ M := hz.2.2.2
    have him : |z.im| ≤ |M| + |δ| := by
      rw [abs_le]
      constructor
      · linarith [abs_nonneg M, abs_nonneg δ, neg_abs_le δ, hδ]
      · linarith [abs_nonneg M, abs_nonneg δ, le_abs_self M, hM]
    have hns : Complex.normSq z ≤ (|M| + |δ| + 1)^2 := by
      rw [Complex.normSq_apply]
      have hre : z.re * z.re ≤ 1 := by nlinarith [abs_le.mp h1]
      nlinarith [abs_le.mp him, sq_nonneg (|M| + |δ|)]
    have hX : 0 ≤ |M| + |δ| + 1 := by positivity
    have hsq : ‖z‖ ^ 2 ≤ (|M| + |δ| + 1) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]; exact hns
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg hX] at this
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

/-! ## The lower bound on the imaginary part -/

/-- **`FDom ∩ λ⁻¹(neighbourhood of w)` is bounded away from the real axis**, for `w ∉ {0,1}`:
otherwise a sequence of such points with imaginary part tending to `0` would converge to one of
the cusps `0, ±1` of `FDom`, where `λ` tends to `1` or has modulus tending to `∞`. -/
lemma FDom_im_lower_bound (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    ∃ d : ℝ, 0 < d ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ τ : ℍ, τ ∈ FDom → ‖lambdaFun τ - w‖ < d → δ ≤ τ.im := by
  have hw1pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set d : ℝ := min (‖w‖/2) (‖w - 1‖/2) with hd
  have hdpos : 0 < d := by
    rw [hd]; exact lt_min (by linarith) (by linarith)
  refine ⟨d, hdpos, ?_⟩
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ τ : ℍ, τ ∈ FDom ∧ ‖lambdaFun τ - w‖ < d ∧ τ.im < 1/(n+1) := by
    intro n
    obtain ⟨τ, hFD, hcl, him⟩ := hcon (1/(n+1)) (by positivity)
    exact ⟨τ, hFD, hcl, him⟩
  choose τ hFD hclose him using hseq
  have hmem : ∀ n, (((τ n : ℍ) : ℂ)) ∈ KF 0 1 := by
    intro n
    refine ⟨(hFD n).1, ?_, ?_, ?_⟩
    · rw [Complex.normSq_eq_norm_sq]; exact (hFD n).2
    · rw [UpperHalfPlane.coe_im]; exact le_of_lt (τ n).im_pos
    · rw [UpperHalfPlane.coe_im]
      have h1 : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
      linarith [him n]
  obtain ⟨p, hpK, ψ, hψmono, hψtend⟩ :=
    (isCompact_KF 0 1).tendsto_subseq (x := fun n => ((τ n : ℍ) : ℂ)) hmem
  have htim : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ).im) atTop (𝓝 p.im) :=
    (Complex.continuous_im.tendsto p).comp hψtend
  have htim0 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ).im) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_)
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hψmono.tendsto_atTop)
    · rw [UpperHalfPlane.coe_im]; exact (τ (ψ n)).im_pos.le
    · rw [UpperHalfPlane.coe_im]; exact (him (ψ n)).le
  have hpim : p.im = 0 := tendsto_nhds_unique htim htim0
  have hpre : |p.re| ≤ 1 := hpK.1
  have hns : Complex.normSq p ≥ |p.re| := hpK.2.1
  have hp_real : p = (p.re : ℂ) := Complex.ext rfl (by simp [hpim])
  have hre2 : p.re ^ 2 ≥ |p.re| := by
    rw [Complex.normSq_apply] at hns
    simpa [hpim, pow_two] using hns
  have habs : |p.re| = 0 ∨ |p.re| = 1 := by
    have h1 : |p.re| ≤ 1 := hpre
    have h3 : 0 ≤ |p.re| := abs_nonneg _
    have h4 : |p.re| ^ 2 ≥ |p.re| := by simpa [sq_abs] using hre2
    rcases eq_or_lt_of_le h3 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm h1 ?_)
      by_contra hlt
      push Not at hlt
      nlinarith
  rcases habs with h0 | h1
  · -- `p = 0`
    have hpr : p.re = 0 := abs_eq_zero.mp h0
    have hp0 : p = 0 := by rw [hp_real, hpr]; norm_num
    have htend0 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 0) := by
      rw [hp0] at hψtend; exact hψtend
    have hone := lambdaFun_tendsto_one_of_FDom_tendsto_zero (fun n => τ (ψ n))
      (fun n => hFD (ψ n)) htend0
    have hlim : Tendsto (fun n => ‖lambdaFun (τ (ψ n)) - w‖) atTop (𝓝 ‖(1:ℂ) - w‖) :=
      (hone.sub tendsto_const_nhds).norm
    have hle := le_of_tendsto hlim (Filter.Eventually.of_forall (fun n => (hclose (ψ n)).le))
    have hdw : d < ‖w - 1‖ := by
      have h2 : d ≤ ‖w - 1‖/2 := by rw [hd]; exact min_le_right _ _
      linarith
    rw [norm_sub_rev] at hle
    linarith
  · -- `p = 1` or `p = -1`
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h1 with h1' | h1'
    · have hp1 : p = 1 := by rw [hp_real, h1']; norm_num
      have htend1 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 1) := by
        rw [hp1] at hψtend; exact hψtend
      have hinf := lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_one (fun n => τ (ψ n))
        (fun n => hFD (ψ n)) htend1
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.1
        (hinf.eventually (eventually_ge_atTop (‖w‖ + d + 1)))
      have hbd : ‖lambdaFun (τ (ψ n))‖ ≤ ‖w‖ + d := by
        have h2 := norm_add_le (lambdaFun (τ (ψ n)) - w) w
        have h3 : lambdaFun (τ (ψ n)) - w + w = lambdaFun (τ (ψ n)) := by ring
        rw [h3] at h2
        linarith [hclose (ψ n)]
      linarith [hn n le_rfl]
    · have hpm1 : p = -1 := by rw [hp_real, h1']; norm_num
      have htend1 : Tendsto (fun n => (((τ (ψ n) : ℍ)) : ℂ)) atTop (𝓝 (-1)) := by
        rw [hpm1] at hψtend; exact hψtend
      have hinf := lambdaFun_norm_tendsto_atTop_of_FDom_tendsto_neg_one (fun n => τ (ψ n))
        (fun n => hFD (ψ n)) htend1
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.1
        (hinf.eventually (eventually_ge_atTop (‖w‖ + d + 1)))
      have hbd : ‖lambdaFun (τ (ψ n))‖ ≤ ‖w‖ + d := by
        have h2 := norm_add_le (lambdaFun (τ (ψ n)) - w) w
        have h3 : lambdaFun (τ (ψ n)) - w + w = lambdaFun (τ (ψ n)) := by ring
        rw [h3] at h2
        linarith [hclose (ψ n)]
      linarith [hn n le_rfl]

/-! ## The main lemma -/

theorem lambda_fiber_close (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w' : ℂ, ‖w' - w‖ < ε → ∀ τ' : UpperHalfPlane,
      τ' ∈ Work.Rigidity.FDom → Work.Kernels.lambdaFun τ' = w' →
        ∃ τ : UpperHalfPlane, τ ∈ Work.Rigidity.FDom ∧ Work.Kernels.lambdaFun τ = w ∧
          dist (τ : ℂ) (τ' : ℂ) < η := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨R, hR⟩ := lambdaFun_norm_lt_of_im_large (‖w‖/2) (by linarith)
  obtain ⟨d, hdpos, δ, hδpos, hlow⟩ := FDom_im_lower_bound w hw0 hw1
  set c : ℝ := min (‖w‖/2) d with hc
  have hcpos : 0 < c := lt_min (by linarith) hdpos
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ (w' : ℂ) (τ' : ℍ), ‖w' - w‖ < 1/(n+1) ∧ τ' ∈ FDom ∧
      lambdaFun τ' = w' ∧
      ∀ τ : ℍ, τ ∈ FDom → lambdaFun τ = w → η ≤ dist (τ : ℂ) (τ' : ℂ) := by
    intro n
    obtain ⟨w', hw', τ', hFD, hlam, hno⟩ := hcon (1/(n+1)) (by positivity)
    exact ⟨w', τ', hw', hFD, hlam, hno⟩
  choose w' τ' hw' hFD hlam hno using hseq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1:ℝ)/((N:ℝ)+1) < c := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1/c)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    have h : (1/c) * c < (N:ℝ) * c := mul_lt_mul_of_pos_right hN hcpos
    rw [div_mul_cancel₀ 1 (ne_of_gt hcpos)] at h
    linarith
  have hbound : ∀ k : ℕ, (1:ℝ)/(((N + k : ℕ):ℝ)+1) < c := by
    intro k
    have h1 : (1:ℝ)/(((N + k : ℕ):ℝ)+1) ≤ 1/((N:ℝ)+1) := by
      have h2 : (N:ℝ) + 1 ≤ ((N + k : ℕ):ℝ) + 1 := by
        have := Nat.le_add_right N k
        push_cast
        linarith
      exact one_div_le_one_div_of_le (by positivity) h2
    linarith
  have hmem : ∀ k : ℕ, (((τ' (N + k) : ℍ)) : ℂ) ∈ KF δ (max R 1 + 1) := by
    intro k
    refine ⟨(hFD (N + k)).1, ?_, ?_, ?_⟩
    · rw [Complex.normSq_eq_norm_sq]; exact (hFD (N + k)).2
    · apply hlow (τ' (N + k)) (hFD (N + k))
      rw [hlam (N + k)]
      calc ‖w' (N + k) - w‖ < (1:ℝ)/(((N + k : ℕ):ℝ)+1) := hw' (N + k)
        _ < c := hbound k
        _ ≤ d := min_le_right _ _
    · have himR : (τ' (N + k)).im < R := by
        by_contra hge
        push Not at hge
        have h1 := hR (τ' (N + k)) hge
        have h2 : ‖w‖/2 < ‖lambdaFun (τ' (N + k))‖ := by
          have h3 : ‖w‖ ≤ ‖w' (N + k) - w‖ + ‖w' (N + k)‖ := by
            have h4 := norm_add_le (w - w' (N + k)) (w' (N + k))
            have h5 : w - w' (N + k) + w' (N + k) = w := by ring
            rw [h5] at h4
            rwa [norm_sub_rev] at h4
          have h5 : ‖w' (N + k) - w‖ < ‖w‖/2 :=
            lt_of_lt_of_le (lt_trans (hw' (N + k)) (hbound k)) (min_le_left (‖w‖/2) d)
          have h6 : ‖w‖/2 < ‖w' (N + k)‖ := by linarith
          rwa [← hlam (N + k)] at h6
        linarith
      have hRmax : R ≤ max R 1 + 1 := by linarith [le_max_left R 1]
      rw [UpperHalfPlane.coe_im]
      linarith
  obtain ⟨p, hpK, ψ, hψmono, hψtend0⟩ :=
    (isCompact_KF δ (max R 1 + 1)).tendsto_subseq
      (x := fun k => ((τ' (N + k) : ℍ) : ℂ)) hmem
  have hψtend : Tendsto (fun k => ((τ' (N + ψ k) : ℍ) : ℂ)) atTop (𝓝 p) := hψtend0
  have hppos : 0 < p.im := lt_of_lt_of_le hδpos hpK.2.2.1
  have hpFD : (⟨p, hppos⟩ : ℍ) ∈ FDom := by
    refine ⟨hpK.1, ?_⟩
    rw [← Complex.normSq_eq_norm_sq]
    exact hpK.2.1
  have hwtend : Tendsto (fun k => w' (N + ψ k)) atTop (𝓝 w) := by
    have hall : Tendsto w' atTop (𝓝 w) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [dist_eq_norm]
      exact (hw' n).le
    rw [Metric.tendsto_atTop] at hall ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hall ε hε
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
      (hψmono.tendsto_atTop.eventually (eventually_ge_atTop M))
    refine ⟨K, fun k hk => ?_⟩
    exact hM (N + ψ k) (by have := hK k hk; omega)
  have hlam_p : lambdaFun (⟨p, hppos⟩ : ℍ) = w := by
    have hcomp : Tendsto (fun k => Work.Kernels.LogLambda.lamC ((τ' (N + ψ k) : ℍ) : ℂ))
        atTop (𝓝 (Work.Kernels.LogLambda.lamC p)) :=
      ((Work.Kernels.LogLambda.differentiableOn_lamC.continuousOn).continuousAt
        (Work.Kernels.LogLambda.isOpen_U.mem_nhds hppos)).tendsto.comp hψtend
    have heq : (fun k => Work.Kernels.LogLambda.lamC ((τ' (N + ψ k) : ℍ) : ℂ))
        = fun k => w' (N + ψ k) := by
      funext k
      rw [lamC_coe (τ' (N + ψ k)), hlam (N + ψ k)]
    rw [heq] at hcomp
    have hwp : Work.Kernels.LogLambda.lamC p = w := tendsto_nhds_unique hcomp hwtend
    rw [← lamC_coe (⟨p, hppos⟩ : ℍ)]
    exact hwp
  have hdist0 : Tendsto
      (fun k => dist ((⟨p, hppos⟩ : ℍ) : ℂ) ((τ' (N + ψ k) : ℍ) : ℂ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k => (p : ℂ) - ((τ' (N + ψ k) : ℍ) : ℂ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => (p : ℂ)) atTop (𝓝 (p : ℂ)) := tendsto_const_nhds
      have h1 : Tendsto (fun k => (p : ℂ) - ((τ' (N + ψ k) : ℍ) : ℂ)) atTop
          (𝓝 ((p : ℂ) - p)) := hc.sub hψtend
      rwa [sub_self] at h1
    have h1 : Tendsto (fun k => ‖(p : ℂ) - ((τ' (N + ψ k) : ℍ) : ℂ)‖) atTop (𝓝 0) := by
      have h2 := h0.norm
      rwa [norm_zero] at h2
    exact h1.congr (fun k => by simp [dist_eq_norm])
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      dist ((⟨p, hppos⟩ : ℍ) : ℂ) ((τ' (N + ψ k) : ℍ) : ℂ) < η := by
    rw [Metric.tendsto_atTop] at hdist0
    obtain ⟨k0, hk0⟩ := hdist0 η hη
    refine ⟨k0, ?_⟩
    have h := hk0 k0 le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at h
  have hcontra := hno (N + ψ k) (⟨p, hppos⟩ : ℍ) hpFD hlam_p
  linarith

end Work.Rigidity
