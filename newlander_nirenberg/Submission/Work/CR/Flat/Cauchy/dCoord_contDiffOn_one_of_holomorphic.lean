import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic
import Submission.Work.CR.Flat.Cauchy.dbarCoord_setIntegral_shift
import Submission.Work.CR.Flat.Cauchy.fderiv_eq_dzC_add_dbarC
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Metric MeasureTheory Set

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat

/-! ## Helper lemmas copied from `holderNorm_le_sup_of_holomorphic_open`
(that module does not currently build, so the short ingredients used below are reproduced
here verbatim). -/

/-- If `f : ℂ → ℂ` is real-differentiable at `z` and `∂̄f z = 0`, then `f` is complex
differentiable at `z`. -/
lemma dcr_differentiableAt_complex_of_dbarC {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (h : Work.CR.Flat.dbarC f z = 0) : DifferentiableAt ℂ f z := by
  rw [differentiableAt_iff_restrictScalars ℝ hf]
  refine ⟨ContinuousLinearMap.toSpanSingleton ℂ (Work.CR.Flat.dzC f z), ?_⟩
  ext v
  change (ContinuousLinearMap.toSpanSingleton ℂ (Work.CR.Flat.dzC f z)) v = (fderiv ℝ f z) v
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  have hh := fderiv_eq_dzC_add_dbarC f z v hf
  rw [h, zero_mul, add_zero] at hh
  rw [hh, smul_eq_mul]; ring

/-- The `j`-th slice map `t ↦ Function.update y j t` is affine with derivative `Pi.single j`. -/
lemma dcr_hasFDerivAt_update {n : ℕ} (j : Fin n) (y : Fin n → ℂ) (w : ℂ) :
    HasFDerivAt (fun t : ℂ => Function.update y j t)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
  have hfun : (fun t : ℂ => Function.update y j t)
      = fun t : ℂ => Function.update y j 0
          + (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) t := by
    funext t
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
    (x := w)).const_add (Function.update y j 0)

/-- The real differential of the `j`-th slice at an arbitrary point. -/
lemma dcr_fderiv_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w
      = (fderiv ℝ g (Function.update y j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) :=
  (hg.hasFDerivAt.comp w (dcr_hasFDerivAt_update j y w)).fderiv

/-- Real differentiability of a slice at an arbitrary point. -/
lemma dcr_differentiableAt_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    DifferentiableAt ℝ (fun t : ℂ => g (Function.update y j t)) w :=
  (hg.hasFDerivAt.comp w (dcr_hasFDerivAt_update j y w)).differentiableAt

/-- The `(0,1)`-derivative of the `j`-th slice is the `j`-th `(0,1)`-derivative of `g`. -/
lemma dcr_dbarC_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    Work.CR.Flat.dbarC (fun t : ℂ => g (Function.update y j t)) w
      = dbarCoord j g (Function.update y j w) := by
  rw [Work.CR.Flat.dbarC, dbarCoord, dcr_fderiv_slice j hg]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]

/-- A slice at a point where `∂̄` vanishes is complex differentiable. -/
lemma dcr_differentiableAt_complex_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    {w : ℂ} (hg : DifferentiableAt ℝ g (Function.update y j w))
    (h : dbarCoord j g (Function.update y j w) = 0) :
    DifferentiableAt ℂ (fun t : ℂ => g (Function.update y j t)) w :=
  dcr_differentiableAt_complex_of_dbarC (dcr_differentiableAt_slice j hg)
    (by rw [dcr_dbarC_slice j hg]; exact h)

/-- The complex derivative of a slice is the `j`-th `(1,0)`-derivative of `g`. -/
lemma dcr_deriv_slice_eq_dCoord {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w))
    (h : dbarCoord j g (Function.update y j w) = 0) :
    deriv (fun t : ℂ => g (Function.update y j t)) w = dCoord j g (Function.update y j w) := by
  have hcd := dcr_differentiableAt_complex_slice j hg h
  have h1 : deriv (fun t : ℂ => g (Function.update y j t)) w
      = fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w 1 := by
    rw [show deriv (fun t : ℂ => g (Function.update y j t)) w
        = (fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w) 1 from rfl]
    calc (fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w) 1
        = ((fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w).restrictScalars ℝ) 1 := rfl
      _ = (fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w) 1 := by
          rw [hcd.fderiv_restrictScalars ℝ]
  rw [h1, dcr_fderiv_slice j hg]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [Work.CR.Flat.Holder.fderiv_single_eq g (Function.update y j w) j 1, h]
  simp

/-- **Cauchy integral formula for the derivative at an arbitrary interior point.** -/
lemma dcr_deriv_eq_smul_circleIntegral {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = (2 * (Real.pi : ℂ) * Complex.I) • deriv f w := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw)
  have hci : CircleIntegrable f c R :=
    (hc.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hderiv : HasDerivAt (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z) w :=
    Complex.hasDerivAt_circleIntegral_sub_inv_smul hci (by
      rw [Metric.mem_sphere, abs_of_pos hR]
      exact ne_of_lt (Metric.mem_ball.mp hw))
  have hev : (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      =ᶠ[𝓝 w] (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with t ht
    exact hc.circleIntegral_sub_inv_smul ht
  have hf2 : HasDerivAt (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t)
      ((2 * (Real.pi : ℂ) * Complex.I) • deriv f w) w := by
    have hfd : DifferentiableAt ℂ f w := hc.differentiableAt Metric.isOpen_ball hw
    exact hfd.hasDerivAt.const_smul (2 * (Real.pi : ℂ) * Complex.I)
  rw [← hderiv.deriv, hev.deriv_eq, hf2.deriv]

/-- The Cauchy formula for the derivative, solved for the derivative. -/
lemma dcr_two_pi_I_inv_smul_circleIntegral_deriv {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) • (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = deriv f w := by
  rw [dcr_deriv_eq_smul_circleIntegral hc hw, inv_smul_smul₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The slice of a holomorphic function is `DiffContOnCl` on a disc centred at `y j`. -/
lemma diffContOnCl_slice_at {n : ℕ} {Ω : Set (Fin n → ℂ)} {g : (Fin n → ℂ) → ℂ} {j : Fin n}
    {y : Fin n → ℂ} {R : ℝ}
    (hgd : ∀ z ∈ Ω, DifferentiableAt ℝ g z)
    (hhol : ∀ z ∈ Ω, dbarCoord j g z = 0)
    (hmem : ∀ t ∈ Metric.closedBall (y j) R, Function.update y j t ∈ Ω) :
    DiffContOnCl ℂ (fun t : ℂ => g (Function.update y j t)) (Metric.ball (y j) R) := by
  apply DifferentiableOn.diffContOnCl
  refine (?_ : DifferentiableOn ℂ (fun t : ℂ => g (Function.update y j t))
    (Metric.closedBall (y j) R)).mono Metric.closure_ball_subset_closedBall
  intro w hw
  exact (dcr_differentiableAt_complex_slice j (hgd _ (hmem w hw)) (hhol _ (hmem w hw))).differentiableWithinAt

/-! ## The local regularity step -/

/-- The integrand of the Cauchy integral, as a function of the parameter `y` and the angle `θ`. -/
private noncomputable def cint {n : ℕ} (j : Fin n) (R : ℝ) (g : (Fin n → ℂ) → ℂ)
    (y : Fin n → ℂ) (θ : ℝ) : ℂ :=
  deriv (circleMap (0 : ℂ) R) θ •
    ((circleMap (0 : ℂ) R θ) ^ (-2 : ℤ) •
      g (y + Pi.single j (R * Complex.exp (θ * Complex.I))))

/-- The real derivative of `cint` in the parameter. -/
private noncomputable def cintDeriv {n : ℕ} (j : Fin n) (R : ℝ) (g : (Fin n → ℂ) → ℂ)
    (y : Fin n → ℂ) (θ : ℝ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  deriv (circleMap (0 : ℂ) R) θ •
    ((circleMap (0 : ℂ) R θ) ^ (-2 : ℤ) •
      fderiv ℝ g (y + Pi.single j (R * Complex.exp (θ * Complex.I))))

private lemma hasFDerivAt_cint {n : ℕ} {g : (Fin n → ℂ) → ℂ} {j : Fin n} {R : ℝ}
    {y : Fin n → ℂ} {θ : ℝ}
    (hg : DifferentiableAt ℝ g (y + Pi.single j (R * Complex.exp (θ * Complex.I)))) :
    HasFDerivAt (fun y' : Fin n → ℂ => cint j R g y' θ) (cintDeriv j R g y θ) y := by
  have htrans : HasFDerivAt
      (fun y' : Fin n → ℂ => y' + Pi.single j (R * Complex.exp (θ * Complex.I)))
      (ContinuousLinearMap.id ℝ (Fin n → ℂ)) y := (hasFDerivAt_id y).add_const _
  have hc : HasFDerivAt
      (fun y' : Fin n → ℂ => g (y' + Pi.single j (R * Complex.exp (θ * Complex.I))))
      (fderiv ℝ g (y + Pi.single j (R * Complex.exp (θ * Complex.I)))) y := by
    have h := hg.hasFDerivAt.comp y htrans
    rwa [ContinuousLinearMap.comp_id] at h
  exact ((hc.const_smul ((circleMap (0 : ℂ) R θ) ^ (-2 : ℤ))).const_smul
    (deriv (circleMap (0 : ℂ) R) θ))

private lemma cintDeriv_smul_I {n : ℕ} {g : (Fin n → ℂ) → ℂ} {j : Fin n} (R : ℝ)
    {y : Fin n → ℂ} {θ : ℝ}
    (hhol : ∀ k, dbarCoord k g (y + Pi.single j (R * Complex.exp (θ * Complex.I))) = 0)
    (u : Fin n → ℂ) :
    cintDeriv j R g y θ (Complex.I • u) = Complex.I * cintDeriv j R g y θ u := by
  have hL := fderiv_smul_I hhol u
  simp only [cintDeriv, ContinuousLinearMap.smul_apply, smul_eq_mul, hL]
  ring

/-- `a ^ (-2)` written as a product (used to differentiate the Cauchy kernel). -/
private lemma zpow_neg_two_mul' (a : ℂ) : a ^ (-2 : ℤ) = a⁻¹ * a⁻¹ := by
  have h : a ^ (-2 : ℤ) = a⁻¹ ^ 2 := by
    rw [show (-2 : ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, inv_pow]; norm_num
  rw [h, pow_two]

private lemma smul_fun_eq {α N : Type*} [SMul ℂ N] (c : ℂ) (f : α → N) :
    (c • f : α → N) = fun x => c • f x := by
  funext x
  simp only [Pi.smul_apply, Pi.smul_apply']

/-- **Elliptic regularity step.** `(1,0)`-derivatives of `C¹` holomorphic functions on an open
set are again `C¹` and again holomorphic.  Proved locally by the Cauchy integral formula: on a
small ball around `z₀` the derivative `dCoord j g` equals the Cauchy integral `Ψ` of the slice,
and `Ψ` is `C¹` with `ℂ`-linear differential by differentiation under the integral sign. -/
private lemma local_step {n : ℕ} {Ω : Set (Fin n → ℂ)} {g : (Fin n → ℂ) → ℂ} {z₀ : Fin n → ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball z₀ ρ ⊆ Ω) (hΩ : IsOpen Ω)
    (hg : ContDiffOn ℝ 1 g Ω) (hhol : ∀ j, ∀ z ∈ Ω, dbarCoord j g z = 0) (j : Fin n) :
    ContDiffAt ℝ 1 (fun z => dCoord j g z) z₀ ∧
      (∀ k, dbarCoord k (fun z => dCoord j g z) z₀ = 0) := by
  have hgd : ∀ z ∈ Ω, DifferentiableAt ℝ g z := fun z hz =>
    (hg.differentiableOn (by norm_num)).differentiableAt (hΩ.mem_nhds hz)
  have hfderiv_cont : ContinuousOn (fun z => fderiv ℝ g z) Ω :=
    (hg.fderiv_of_isOpen (m := (0 : WithTop ℕ∞)) hΩ (by norm_num)).continuousOn
  have hKsub : Metric.closedBall z₀ (ρ / 2) ⊆ Ω := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : dist z z₀ ≤ ρ / 2 := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm] at h1
    linarith
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (ρ / 2)).exists_bound_of_continuousOn
    (hfderiv_cont.mono hKsub)
  have hnorm_circle : ∀ θ : ℝ, ‖circleMap (0 : ℂ) (ρ / 4) θ‖ = ρ / 4 := by
    intro θ
    rw [circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I θ, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hxbound : ∀ x : Fin n → ℂ, ‖x - z₀‖ < ρ / 4 → ∀ θ : ℝ,
      ‖x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)) - z₀‖ ≤ ρ / 2 := by
    intro x hx θ
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    rw [Pi.sub_apply, Pi.add_apply]
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same]
      have hexp : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I θ
      calc ‖x i + ((ρ / 4 : ℝ) : ℂ) * Complex.exp (θ * Complex.I) - z₀ i‖
          = ‖(x i - z₀ i) + (((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)‖ := by
            congr 1; ring
        _ ≤ ‖x i - z₀ i‖ + ‖(((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_add_le _ _
        _ = ‖x i - z₀ i‖ + ρ / 4 := by
              rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by positivity : (0:ℝ) < ρ / 4)]
        _ ≤ ‖x - z₀‖ + ρ / 4 := by
              gcongr
              calc ‖x i - z₀ i‖ = ‖(x - z₀) i‖ := by rw [Pi.sub_apply]
                _ ≤ ‖x - z₀‖ := norm_le_pi_norm _ i
        _ ≤ ρ / 2 := by linarith
    · rw [Pi.single_eq_of_ne hi, add_zero]
      calc ‖x i - z₀ i‖ = ‖(x - z₀) i‖ := by rw [Pi.sub_apply]
        _ ≤ ‖x - z₀‖ := norm_le_pi_norm _ i
        _ ≤ ρ / 2 := by linarith
  have hmem_all : ∀ x ∈ Metric.ball z₀ (ρ / 4), ∀ θ : ℝ,
      x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)) ∈ Ω := by
    intro x hx θ
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hx' : ‖x - z₀‖ < ρ / 4 := by
      have h := Metric.mem_ball.mp hx; rwa [dist_eq_norm] at h
    have := hxbound x hx' θ
    linarith
  have hpath : ∀ x : Fin n → ℂ, Continuous (fun θ : ℝ =>
      x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I))) := by
    intro x
    have hExp : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const Complex.I)
    have hcf : Continuous (fun θ : ℝ => (((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)) :=
      hExp.const_mul _
    exact continuous_const.add
      ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j).continuous.comp hcf)
  have hne : ∀ θ : ℝ, circleMap (0 : ℂ) (ρ / 4) θ ≠ 0 := by
    intro θ h
    have h1 := hnorm_circle θ
    rw [h, norm_zero] at h1
    have : (0:ℝ) < ρ / 4 := by positivity
    linarith
  have hcont_derivCirc : Continuous (fun θ : ℝ => deriv (circleMap (0 : ℂ) (ρ / 4)) θ) := by
    have h2 : (fun θ : ℝ => deriv (circleMap (0 : ℂ) (ρ / 4)) θ)
        = fun θ : ℝ => circleMap 0 (ρ / 4) θ * Complex.I := by
      funext θ; rw [deriv_circleMap]
    rw [h2]; exact (continuous_circleMap 0 (ρ / 4)).mul_const Complex.I
  have hcont_zpow : Continuous (fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ) ^ (-2 : ℤ)) := by
    have hinv : Continuous (fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ)⁻¹) :=
      (continuous_circleMap 0 (ρ / 4)).inv₀ hne
    have hgoal : (fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ) ^ (-2 : ℤ))
        = fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ)⁻¹ ^ 2 := by
      funext θ; rw [show (-2 : ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, inv_pow]; norm_num
    rw [hgoal]; exact hinv.pow 2
  have hcont_cint : ∀ x ∈ Metric.ball z₀ (ρ / 4),
      Continuous (fun θ : ℝ => cint j (ρ / 4) g x θ) := by
    intro x hx
    have hgc : Continuous (fun θ : ℝ =>
        g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)))) :=
      hg.continuousOn.comp_continuous (hpath x) (fun θ => hmem_all x hx θ)
    have h1 := hcont_derivCirc.smul (hcont_zpow.smul hgc)
    have h2 : ((fun θ : ℝ => deriv (circleMap (0 : ℂ) (ρ / 4)) θ) •
          ((fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ) ^ (-2 : ℤ)) • (fun θ : ℝ =>
            g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I))))))
        = fun θ : ℝ => deriv (circleMap (0 : ℂ) (ρ / 4)) θ •
            ((circleMap (0 : ℂ) (ρ / 4) θ) ^ (-2 : ℤ) •
              g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)))) := by
      funext θ; simp only [smul_eq_mul, Pi.mul_apply]
    rw [h2] at h1
    simpa only [cint] using h1
  have hcont_cintDeriv : ∀ x ∈ Metric.ball z₀ (ρ / 4),
      Continuous (fun θ : ℝ => cintDeriv j (ρ / 4) g x θ) := by
    intro x hx
    have hfd : Continuous (fun θ : ℝ =>
        fderiv ℝ g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)))) :=
      hfderiv_cont.comp_continuous (hpath x) (fun θ => hmem_all x hx θ)
    have h1 := hcont_derivCirc.smul (hcont_zpow.smul hfd)
    have h2 : ((fun θ : ℝ => deriv (circleMap (0 : ℂ) (ρ / 4)) θ) •
          ((fun θ : ℝ => (circleMap (0 : ℂ) (ρ / 4) θ) ^ (-2 : ℤ)) • (fun θ : ℝ =>
            fderiv ℝ g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I))))))
        = fun θ : ℝ => cintDeriv j (ρ / 4) g x θ := by
      funext θ; simp only [cintDeriv, Pi.smul_apply']
    rw [h2] at h1
    exact h1
  have hbound_pt : ∀ x ∈ Metric.ball z₀ (ρ / 4), ∀ t : ℝ,
      ‖cintDeriv j (ρ / 4) g x t‖ ≤ (ρ / 4) * ((ρ / 4) ^ (-2 : ℤ) * M) := by
    intro x hx t
    have hx' : ‖x - z₀‖ < ρ / 4 := by
      have h := Metric.mem_ball.mp hx; rwa [dist_eq_norm] at h
    have hL : ‖fderiv ℝ g (x + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (t * Complex.I)))‖
        ≤ M :=
      hM _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hxbound x hx' t)
    have ha : ‖deriv (circleMap (0 : ℂ) (ρ / 4)) t‖ = ρ / 4 := by
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, hnorm_circle t]
    have hb : ‖(circleMap (0 : ℂ) (ρ / 4) t) ^ (-2 : ℤ)‖ = (ρ / 4) ^ (-2 : ℤ) := by
      rw [norm_zpow, hnorm_circle t]
    have h1 : (0:ℝ) ≤ ρ / 4 := by positivity
    have h2 : (0:ℝ) ≤ (ρ / 4) ^ (-2 : ℤ) := by positivity
    simp only [cintDeriv, norm_smul, ha, hb]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL h2) h1
  have hPhi : ∀ y ∈ Metric.ball z₀ (ρ / 4),
      HasFDerivAt (fun y => ∫ θ in 0..2 * Real.pi, cint j (ρ / 4) g y θ)
        (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ) y := by
    intro y hy
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y θ => cint j (ρ / 4) g y θ)
      (F' := fun y θ => cintDeriv j (ρ / 4) g y θ)
      (bound := fun _ => (ρ / 4) * ((ρ / 4) ^ (-2 : ℤ) * M))
      (s := Metric.ball z₀ (ρ / 4)) (x₀ := y)
      (Metric.isOpen_ball.mem_nhds hy) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds hy] with x hx
      exact (hcont_cint x hx).aestronglyMeasurable
    · exact (hcont_cint y hy).intervalIntegrable _ _
    · exact (hcont_cintDeriv y hy).aestronglyMeasurable
    · filter_upwards with t ht x hx
      exact hbound_pt x hx t
    · exact intervalIntegrable_const
    · filter_upwards with t ht x hx
      exact hasFDerivAt_cint (j := j) (R := ρ / 4) (hgd _ (hmem_all x hx t))
  have hz₀ : z₀ ∈ Metric.ball z₀ (ρ / 4) := by rw [Metric.mem_ball, dist_self]; positivity
  set Ψ : (Fin n → ℂ) → ℂ := fun y =>
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) • (∫ θ in 0..2 * Real.pi, cint j (ρ / 4) g y θ)
    with hΨdef
  have hΨ_circ : ∀ y, Ψ y = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
      (∮ ζ in C(y j, ρ / 4), (ζ - y j) ^ (-2 : ℤ) • g (Function.update y j ζ)) := by
    intro y
    rw [hΨdef]
    simp only
    have hkey : (∫ θ in 0..2 * Real.pi, cint j (ρ / 4) g y θ)
        = ∫ θ in 0..2 * Real.pi, deriv (circleMap (y j) (ρ / 4)) θ •
            ((circleMap (y j) (ρ / 4) θ - y j) ^ (-2 : ℤ) •
              g (Function.update y j (circleMap (y j) (ρ / 4) θ))) := by
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      have h1 : deriv (circleMap (y j) (ρ / 4)) θ = deriv (circleMap (0 : ℂ) (ρ / 4)) θ := by
        rw [deriv_circleMap, deriv_circleMap]
      have h2 : circleMap (y j) (ρ / 4) θ - y j = circleMap (0 : ℂ) (ρ / 4) θ := by
        rw [circleMap, circleMap]; ring
      have h3 : Function.update y j (circleMap (y j) (ρ / 4) θ)
          = y + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (θ * Complex.I)) := by
        rw [circleMap]
        ext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
      rw [h1, h2, h3]
      rfl
    rw [hkey]
    rfl
  have hΨ_eq : ∀ y ∈ Metric.ball z₀ (ρ / 4), Ψ y = dCoord j g y := by
    intro y hy
    rw [hΨ_circ y]
    have hy' : ‖y - z₀‖ < ρ / 4 := by
      have h := Metric.mem_ball.mp hy; rwa [dist_eq_norm] at h
    have hmemΩ : y ∈ Ω := by
      apply hball; rw [Metric.mem_ball, dist_eq_norm]; linarith
    have hslice : DiffContOnCl ℂ (fun t : ℂ => g (Function.update y j t))
        (Metric.ball (y j) (ρ / 4)) := by
      refine diffContOnCl_slice_at hgd (fun z hz => hhol j z hz) ?_
      intro t ht
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      refine (pi_norm_lt_iff hρ).mpr (fun i => ?_)
      rw [Pi.sub_apply]
      have ht' : ‖t - y j‖ ≤ ρ / 4 := by
        have h := Metric.mem_closedBall.mp ht; rwa [dist_eq_norm] at h
      by_cases hi : i = j
      · subst hi
        rw [Function.update_self]
        calc ‖t - z₀ i‖ ≤ ‖t - y i‖ + ‖y i - z₀ i‖ := by
              rw [show t - z₀ i = (t - y i) + (y i - z₀ i) by ring]
              exact norm_add_le _ _
          _ ≤ ρ / 4 + ‖y - z₀‖ := add_le_add ht' (norm_le_pi_norm (y - z₀) i)
          _ < ρ / 4 + ρ / 4 := by linarith
          _ = ρ / 2 := by ring
          _ < ρ := by linarith
      · rw [Function.update_of_ne hi]
        calc ‖y i - z₀ i‖ = ‖(y - z₀) i‖ := by rw [Pi.sub_apply]
          _ ≤ ‖y - z₀‖ := norm_le_pi_norm _ i
          _ < ρ / 4 := hy'
          _ < ρ := by linarith
    have hw : y j ∈ Metric.ball (y j) (ρ / 4) := by
      rw [Metric.mem_ball, dist_self]; positivity
    have hderiv := dcr_two_pi_I_inv_smul_circleIntegral_deriv hslice hw
    have h1 : deriv (fun t : ℂ => g (Function.update y j t)) (y j) = dCoord j g y := by
      have hdiff : DifferentiableAt ℝ g (Function.update y j (y j)) := by
        rw [Function.update_eq_self]; exact hgd y hmemΩ
      have hdb : dbarCoord j g (Function.update y j (y j)) = 0 := by
        rw [Function.update_eq_self]; exact hhol j y hmemΩ
      have h := dcr_deriv_slice_eq_dCoord j hdiff hdb
      rwa [Function.update_eq_self] at h
    rw [hderiv, h1]
  have hcont_L0 : ContinuousOn
      (fun y : Fin n → ℂ => ∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ)
      (Metric.ball z₀ (ρ / 4)) := by
    intro y₀ hy₀
    refine intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun y θ => cintDeriv j (ρ / 4) g y θ)
      (bound := fun _ => (ρ / 4) * ((ρ / 4) ^ (-2 : ℤ) * M))
      (s := Metric.ball z₀ (ρ / 4)) (x₀ := y₀) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hcont_cintDeriv x hx).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with x hx
      filter_upwards with t ht
      exact hbound_pt x hx t
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      have hpath' : ContinuousAt (fun y : Fin n → ℂ =>
          y + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (t * Complex.I))) y₀ :=
        (continuousAt_id.add continuousAt_const)
      have hfdw : ContinuousWithinAt (fun y : Fin n → ℂ =>
          fderiv ℝ g (y + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (t * Complex.I))))
          (Metric.ball z₀ (ρ / 4)) y₀ :=
        (ContinuousAt.comp (x := y₀)
          (hfderiv_cont.continuousAt (hΩ.mem_nhds (hmem_all y₀ hy₀ t))) hpath').continuousWithinAt
      have h1 := (hfdw.const_smul ((circleMap (0 : ℂ) (ρ / 4) t) ^ (-2 : ℤ))).const_smul
        (deriv (circleMap (0 : ℂ) (ρ / 4)) t)
      have h2 : (deriv (circleMap (0 : ℂ) (ρ / 4)) t •
            ((circleMap (0 : ℂ) (ρ / 4) t) ^ (-2 : ℤ) •
              (fun y : Fin n → ℂ => fderiv ℝ g
                (y + Pi.single j ((((ρ / 4 : ℝ)) : ℂ) * Complex.exp (t * Complex.I))))))
          = fun y : Fin n → ℂ => cintDeriv j (ρ / 4) g y t := by
        funext y; simp only [cintDeriv, Pi.smul_apply]
      rw [h2] at h1
      exact h1
  have hlin : ∀ y ∈ Metric.ball z₀ (ρ / 4), ∀ u : Fin n → ℂ,
      (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ) (Complex.I • u)
        = Complex.I * (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ) u := by
    intro y hy u
    have hint : IntervalIntegrable (fun θ : ℝ => cintDeriv j (ρ / 4) g y θ) volume 0 (2 * Real.pi) :=
      (hcont_cintDeriv y hy).intervalIntegrable _ _
    rw [ContinuousLinearMap.intervalIntegral_apply hint]
    rw [show (fun θ : ℝ => cintDeriv j (ρ / 4) g y θ (Complex.I • u))
        = fun θ : ℝ => Complex.I * (cintDeriv j (ρ / 4) g y θ u) from
        funext (fun θ => cintDeriv_smul_I (ρ / 4) (fun k => hhol k _ (hmem_all y hy θ)) u)]
    rw [intervalIntegral.integral_const_mul]
    rw [ContinuousLinearMap.intervalIntegral_apply hint]
  refine ⟨?_, ?_⟩
  · refine contDiffAt_one_iff.mpr ⟨fun y => ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
        (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ),
      Metric.ball z₀ (ρ / 4), Metric.isOpen_ball.mem_nhds hz₀, ?_, ?_⟩
    · simpa only [smul_fun_eq] using hcont_L0.const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
    · intro y hy
      have h1 : HasFDerivAt Ψ (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
          (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g y θ)) y := by
        rw [hΨdef]
        simpa only [smul_fun_eq] using (hPhi y hy).const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
      have heq : (fun z => dCoord j g z) =ᶠ[𝓝 y] Ψ :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hy) (fun z hz => (hΨ_eq z hz).symm)
      exact h1.congr_of_eventuallyEq heq
  · intro k
    have hfderiv_eq : fderiv ℝ (fun z => dCoord j g z) z₀
        = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
            (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g z₀ θ) := by
      have h1 : HasFDerivAt Ψ (((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
          (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g z₀ θ)) z₀ := by
        rw [hΨdef]
        simpa only [smul_fun_eq] using (hPhi z₀ hz₀).const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
      have heq : (fun z => dCoord j g z) =ᶠ[𝓝 z₀] Ψ :=
        Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz₀) (fun z hz => (hΨ_eq z hz).symm)
      exact (h1.congr_of_eventuallyEq heq).fderiv
    have hU : (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g z₀ θ) (Complex.I • Pi.single k 1)
        = Complex.I * (∫ θ in 0..2 * Real.pi, cintDeriv j (ρ / 4) g z₀ θ) (Pi.single k 1) :=
      hlin z₀ hz₀ (Pi.single k 1)
    have hsingle : (Pi.single k (Complex.I : ℂ) : Fin n → ℂ) = Complex.I • Pi.single k 1 := by
      ext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    rw [Work.CR.Flat.dbarCoord, hfderiv_eq, hsingle]
    simp only [smul_apply, smul_eq_mul]
    rw [hU]
    have key : ∀ (c A : ℂ), (1/2 : ℂ) * (c * A + Complex.I * (c * (Complex.I * A))) = 0 := by
      intro c A
      rw [show Complex.I * (c * (Complex.I * A)) = (Complex.I * Complex.I) * (c * A) by ring,
        Complex.I_mul_I]
      ring
    exact key _ _

/-- **`(1,0)`-derivatives of holomorphic `C¹` functions are again holomorphic `C¹`.**

This is the elliptic-regularity step for the flat `∂̄`-operator in `ℂⁿ = Fin n → ℂ`: a function
`g` which is `C¹` (real) on an open `Ω` and satisfies the Cauchy–Riemann equations
`∂̄_j g = 0` on `Ω` has `(1,0)`-derivatives `∂_j g = dCoord j g` that are again `C¹` and again
holomorphic on `Ω`. -/
theorem dCoord_contDiffOn_one_of_holomorphic {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiffOn ℝ 1 g Ω)
    (hhol : ∀ j, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j g z = 0) (j : Fin n) :
    ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dCoord j g z) Ω ∧
      (∀ k, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord k (Work.CR.Flat.dCoord j g) z = 0) := by
  have hstep : ∀ z₀ ∈ Ω, ContDiffAt ℝ 1 (fun z => dCoord j g z) z₀ ∧
      (∀ k, dbarCoord k (fun z => dCoord j g z) z₀ = 0) := by
    intro z₀ hz₀
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
    exact local_step hρ hball hΩ hg hhol j
  exact ⟨(IsOpen.contDiffOn_iff hΩ).mpr (fun z hz => (hstep z hz).1),
    fun k z hz => (hstep z hz).2 k⟩


end Work.CR.Flat.Cauchy
