import Submission.FUP.DbarMollify
import Submission.Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
import Submission.Commons.MeasureTheory.tendsto_lintegral_ofReal_sq_one_sub_smul_cutoff
import Submission.Commons.MeasureTheory.memLp_volume_of_memLp_withDensity_of_hasCompactSupport
import Submission.Commons.MeasureTheory.locallyIntegrable_toLp_of_memLp_withDensity_of_hasCompactSupport
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq_weight_norm_general
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_oscillation_defect_sq_vec
import Submission.Commons.Analysis.Convolution.contDiff_integral_smul_sub
import Submission.Commons.Analysis.Convolution.hasCompactSupport_integral_smul_sub
import Submission.FUP.KMSmooth
import Submission.FUP.DbarAdjOp
import Submission.FUP.DbarCutoff
import Submission.FUP.DbarCutoff2
import Submission.Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The Friedrichs argument: the a priori estimate `hbound`

This module proves the a priori estimate

`‖⟪x, v⟫‖² ≤ etaKapNorm v φ κ · (‖∂̄₂ x‖² + ‖ϑ_φ x‖²)`

for every `x` in `Dom (dbarOp2 φ) ⊓ Dom (dbarAdjOp φ)`, which is the `hbound` input of the
abstract existence theorem `Commons.Analysis.InnerProductSpace.LinearPMap.exists_solution_of_bound`.

The estimate is first proved for *smooth compactly supported* forms (the Kohn--Morrey estimate,
`BoundSmooth.norm_inner_liftForm_sq_le` / `KMSmooth.norm_inner_liftForm_sq_le'`); the content of
this file is the approximation argument: a general `x` in the intersection of the two domains is
approximated, in the graph norm of the two weak `∂̄`-operators, by smooth compactly supported
forms.  The approximation is obtained by the usual two-step procedure: cut off `x` by `χ_R`
(product rules `dbarCutoff2.dbarWeak2_mul`, `dbarCutoff.dbarAdjWeak_mul`) and then mollify
(`dbarMollify.dbarWeak2_conv`, `dbarMollify.dbarAdjWeak_conv`).
-/

namespace Submission.FUP

variable {d : ℕ}

/-! ## 1. The smooth cut-off family -/

private lemma cutoffFam_ax (d : ℕ) :
    ∃ θ : ℝ → FormDu d → ℝ,
      (∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (θ r)) ∧
      (∀ r : ℝ, 0 < r → ∀ x, 0 ≤ θ r x ∧ θ r x ≤ 1) ∧
      (∀ r : ℝ, 0 < r → ∀ x, Metric.infDist x (Metric.closedBall (0 : FormDu d) 5)ᶜ ≤ r →
        θ r x = 0) ∧
      (∀ r : ℝ, 0 < r → ∀ x, 3 * r < Metric.infDist x (Metric.closedBall (0 : FormDu d) 5)ᶜ →
        θ r x = 1) ∧
      (∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ x,
        ‖iteratedFDeriv ℝ j (θ r) x‖ ≤ A / r ^ j) :=
  Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale
    (Metric.closedBall (0 : FormDu d) 5)

/-- The reference smooth cut-off family around the closed ball of radius `5` of `ℂᵈ`, whose
existence is the content of `exists_smooth_cutoff_infDist_scale`. -/
noncomputable def cutoffFam (d : ℕ) : ℝ → FormDu d → ℝ :=
  Classical.choose (cutoffFam_ax d)

lemma cutoffFam_spec (d : ℕ) :
    (∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (cutoffFam d r)) ∧
    (∀ r : ℝ, 0 < r → ∀ x, 0 ≤ cutoffFam d r x ∧ cutoffFam d r x ≤ 1) ∧
    (∀ r : ℝ, 0 < r → ∀ x, Metric.infDist x (Metric.closedBall (0 : FormDu d) 5)ᶜ ≤ r →
      cutoffFam d r x = 0) ∧
    (∀ r : ℝ, 0 < r → ∀ x, 3 * r < Metric.infDist x (Metric.closedBall (0 : FormDu d) 5)ᶜ →
      cutoffFam d r x = 1) ∧
    (∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ x,
      ‖iteratedFDeriv ℝ j (cutoffFam d r) x‖ ≤ A / r ^ j) :=
  Classical.choose_spec (cutoffFam_ax d)

/-- The cut-off `χ_R`: it equals `1` on the ball of radius `R`, vanishes outside the ball of
radius `5R`, and its derivative is bounded by `A / R` for a constant `A` independent of `R`. -/
noncomputable def cutFn (d : ℕ) (R : ℝ) : FormDu d → ℝ :=
  fun x => cutoffFam d 1 (R⁻¹ • x)

lemma cutFn_nonneg {d : ℕ} {R : ℝ} (hR : 0 < R) (x : FormDu d) : 0 ≤ cutFn d R x :=
  ((cutoffFam_spec d).2.1 1 one_pos (R⁻¹ • x)).1

lemma cutFn_le_one {d : ℕ} {R : ℝ} (hR : 0 < R) (x : FormDu d) : cutFn d R x ≤ 1 :=
  ((cutoffFam_spec d).2.1 1 one_pos (R⁻¹ • x)).2

lemma norm_inv_smul (R : ℝ) (hR : 0 < R) (x : FormDu d) :
    ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]

/-- `χ_R` equals `1` on the ball of radius `R`. -/
lemma cutFn_eq_one {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {x : FormDu d}
    (hx : ‖x‖ ≤ R) : cutFn d R x = 1 := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : Nontrivial (FormDu d) := inferInstance
  have hne : (Metric.closedBall (0 : FormDu d) 5)ᶜ.Nonempty := by
    obtain ⟨z, hz⟩ := exists_ne (0 : FormDu d)
    refine ⟨(5 / ‖z‖ + 1) • z, ?_⟩
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
    rw [dist_eq_norm, sub_zero, norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 5 / ‖z‖ + 1)]
    have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hkey : (5 / ‖z‖ + 1) * ‖z‖ = 5 + ‖z‖ := by
      field_simp
    rw [hkey]
    linarith
  have h4 : (4 : ℝ) ≤ Metric.infDist (R⁻¹ • x) (Metric.closedBall (0 : FormDu d) 5)ᶜ := by
    refine (Metric.le_infDist hne).mpr (fun z hz => ?_)
    have hz5 : 5 < ‖z‖ := by
      have h := hz
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at h
      simpa [dist_eq_norm] using h
    have hy1 : ‖R⁻¹ • x‖ ≤ 1 := by
      rw [norm_inv_smul R hR x, inv_mul_le_iff₀ hR]; simpa using hx
    have h := norm_sub_norm_le z (R⁻¹ • x)
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  exact (cutoffFam_spec d).2.2.2.1 1 one_pos (R⁻¹ • x) (by linarith)

/-- `χ_R` vanishes outside the ball of radius `5R`. -/
lemma cutFn_eq_zero {d : ℕ} {R : ℝ} (hR : 0 < R) {x : FormDu d} (hx : 5 * R < ‖x‖) :
    cutFn d R x = 0 := by
  refine (cutoffFam_spec d).2.2.1 1 one_pos (R⁻¹ • x) ?_
  have h5 : 5 < ‖R⁻¹ • x‖ := by
    rw [norm_inv_smul R hR x]
    have hmul := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
    have hkey : R⁻¹ * (5 * R) = 5 := by field_simp
    rw [hkey] at hmul
    linarith
  have hmem : R⁻¹ • x ∈ (Metric.closedBall (0 : FormDu d) 5)ᶜ := by
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
    simpa [dist_eq_norm] using h5
  calc Metric.infDist (R⁻¹ • x) (Metric.closedBall (0 : FormDu d) 5)ᶜ
      ≤ dist (R⁻¹ • x) (R⁻¹ • x) := Metric.infDist_le_dist_of_mem hmem
    _ = 0 := dist_self _
    _ ≤ 1 := by norm_num

lemma contDiff_cutFn {d : ℕ} {R : ℝ} (hR : 0 < R) : ContDiff ℝ ∞ (cutFn d R) := by
  have h1 : ContDiff ℝ ∞ (cutoffFam d 1) := (cutoffFam_spec d).1 1 one_pos
  have h2 : ContDiff ℝ ∞ (fun x : FormDu d => R⁻¹ • x) := by fun_prop
  exact h1.comp h2

lemma hasCompactSupport_cutFn {d : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutFn d R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : FormDu d) (5 * R))
    (fun x hx => ?_)
  have hx' : 5 * R < dist x 0 := by
    have h := hx
    rw [Metric.mem_closedBall] at h
    exact not_le.mp h
  exact cutFn_eq_zero hR (by simpa [dist_zero_right] using hx')

lemma norm_iteratedFDeriv_one_eq_norm_fderiv (f : FormDu d → ℝ) (x : FormDu d) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := by
  have h : (continuousMultilinearCurryFin1 ℝ (FormDu d) ℝ).symm (fderiv ℝ f x)
      = iteratedFDeriv ℝ 1 f x := by
    ext v
    rw [continuousMultilinearCurryFin1_symm_apply, iteratedFDeriv_one_apply]
  rw [← h, LinearIsometryEquiv.norm_map]

/-- The derivative of the cut-off `χ_R` is bounded by `A / R`, with `A` independent of `R`. -/
lemma exists_norm_fderiv_cutFn_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 < R → ∀ x : FormDu d,
      ‖fderiv ℝ (cutFn d R) x‖ ≤ A / R := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  haveI : Nontrivial (FormDu d) := inferInstance
  obtain ⟨A, hApos, hA⟩ := (cutoffFam_spec d).2.2.2.2 1
  refine ⟨A, hApos, fun R hR x => ?_⟩
  have hcd1 : ContDiff ℝ ∞ (cutoffFam d 1) := (cutoffFam_spec d).1 1 one_pos
  have hdiff1 : DifferentiableAt ℝ (cutoffFam d 1) (R⁻¹ • x) :=
    (hcd1.differentiable (by decide)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fun y : FormDu d => R⁻¹ • y) x := by fun_prop
  have hchain : fderiv ℝ (cutFn d R) x
      = (fderiv ℝ (cutoffFam d 1) (R⁻¹ • x)) ∘SL
        fderiv ℝ (fun y : FormDu d => R⁻¹ • y) x :=
    fderiv_comp x hdiff1 hdiff2
  have hfd : fderiv ℝ (fun y : FormDu d => R⁻¹ • y) x
      = (R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (FormDu d) := by
    conv_lhs => rw [show (fun y : FormDu d => R⁻¹ • y)
      = (R⁻¹ : ℝ) • (id : FormDu d → FormDu d) from rfl]
    rw [fderiv_const_smul differentiableAt_id (R⁻¹)]
    simp
  have h1 : ‖fderiv ℝ (cutoffFam d 1) (R⁻¹ • x)‖ ≤ A := by
    rw [← norm_iteratedFDeriv_one_eq_norm_fderiv]
    have := hA 1 one_pos (R⁻¹ • x)
    simpa using this
  have h2 : ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (FormDu d)‖ = R⁻¹ := by
    rw [norm_smul, ContinuousLinearMap.norm_id]
    simp [Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  rw [hchain, hfd]
  calc ‖(fderiv ℝ (cutoffFam d 1) (R⁻¹ • x)) ∘SL
        ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (FormDu d))‖
      ≤ ‖fderiv ℝ (cutoffFam d 1) (R⁻¹ • x)‖ *
          ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (FormDu d)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (cutoffFam d 1) (R⁻¹ • x)‖ * R⁻¹ := by rw [h2]
    _ ≤ A * R⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = A / R := by rw [div_eq_mul_inv]

/-! ## 2. Bounds for the cut-off error terms -/

/-- The `(0,2)`-form produced by the product rule for `∂̄₂`. -/
noncomputable def cutErr2 (d : ℕ) (R : ℝ) (X : FormDu d → FormSpace d) :
    FormDu d → (Fin d × Fin d → ℂ) :=
  fun w i => X w i.1 * partialZbar i.2 (toC (cutFn d R)) w
    - X w i.2 * partialZbar i.1 (toC (cutFn d R)) w

/-- The `(0,1)`-form produced by the product rule for `ϑ_φ`. -/
noncomputable def cutErr1 (d : ℕ) (R : ℝ) (X : FormDu d → FormSpace d) : FormDu d → ℂ :=
  fun w => ∑ j : Fin d, partialZ j (toC (cutFn d R)) w * X w j

/-- The derivative of the complexification of a real function has the same operator norm. -/
lemma norm_fderiv_toC_local {d : ℕ} {f : FormDu d → ℝ} {x : FormDu d}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun z => ((f z : ℝ) : ℂ)) x‖ = ‖fderiv ℝ f x‖ := by
  have hcomp : fderiv ℝ (fun z : FormDu d => ((f z : ℝ) : ℂ)) x
      = Complex.ofRealCLM.comp (fderiv ℝ f x) := by
    have h1 : (fun z : FormDu d => ((f z : ℝ) : ℂ)) = (⇑Complex.ofRealCLM) ∘ f := rfl
    rw [h1, fderiv_comp x Complex.ofRealCLM.differentiableAt hf,
      ContinuousLinearMap.fderiv]
  have hRe : ∀ r : ℝ, ‖Complex.ofRealCLM r‖ = ‖r‖ := fun r => by
    rw [Complex.ofRealCLM_apply, Complex.norm_def, Complex.normSq_ofReal]
    rw [Real.sqrt_mul_self_eq_abs, Real.norm_eq_abs]
  rw [hcomp]
  refine le_antisymm ?_ ?_
  · have hle : ‖Complex.ofRealCLM‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun r => by
        rw [hRe, one_mul])
    calc ‖Complex.ofRealCLM.comp (fderiv ℝ f x)‖
        ≤ ‖Complex.ofRealCLM‖ * ‖fderiv ℝ f x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖fderiv ℝ f x‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = ‖fderiv ℝ f x‖ := one_mul _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    calc ‖fderiv ℝ f x v‖ = ‖Complex.ofRealCLM (fderiv ℝ f x v)‖ := (hRe _).symm
      _ = ‖(Complex.ofRealCLM.comp (fderiv ℝ f x)) v‖ := rfl
      _ ≤ ‖Complex.ofRealCLM.comp (fderiv ℝ f x)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _

/-- The Wirtinger derivative `∂̄_j` of the complexification of a real function is bounded by the
operator norm of its derivative. -/
lemma norm_partialZbar_toC_le {χ : FormDu d → ℝ} {A R : ℝ}
    (hbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ A / R)
    (hχd : ∀ z, DifferentiableAt ℝ χ z) (j : Fin d) (z : FormDu d) :
    ‖partialZbar j (toC χ) z‖ ≤ A / R := by
  have hnorm : ‖fderiv ℝ (toC χ) z‖ ≤ A / R := by
    show ‖fderiv ℝ (fun y => ((χ y : ℝ) : ℂ)) z‖ ≤ A / R
    rw [norm_fderiv_toC_local (hχd z)]
    exact hbd z
  have h1 : ‖fderiv ℝ (toC χ) z (Pi.single j 1)‖ ≤ A / R := by
    have h := (fderiv ℝ (toC χ) z).le_opNorm (Pi.single j (1 : ℂ))
    rw [Pi.norm_single, norm_one, mul_one] at h
    exact h.trans hnorm
  have h2 : ‖fderiv ℝ (toC χ) z (Pi.single j Complex.I)‖ ≤ A / R := by
    have h := (fderiv ℝ (toC χ) z).le_opNorm (Pi.single j Complex.I)
    rw [Pi.norm_single, Complex.norm_I, mul_one] at h
    exact h.trans hnorm
  rw [partialZbar, norm_div]
  have h3 : ‖(fderiv ℝ (toC χ) z) (Pi.single j 1)
      + Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)‖
      ≤ (A / R) + (A / R) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    exact add_le_add h1 h2
  have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h4]
  linarith

/-- The Wirtinger derivative `∂_j` of the complexification of a real function is bounded by the
operator norm of its derivative. -/
lemma norm_partialZ_toC_le {χ : FormDu d → ℝ} {A R : ℝ}
    (hbd : ∀ z, ‖fderiv ℝ χ z‖ ≤ A / R)
    (hχd : ∀ z, DifferentiableAt ℝ χ z) (j : Fin d) (z : FormDu d) :
    ‖partialZ j (toC χ) z‖ ≤ A / R := by
  have hnorm : ‖fderiv ℝ (toC χ) z‖ ≤ A / R := by
    show ‖fderiv ℝ (fun y => ((χ y : ℝ) : ℂ)) z‖ ≤ A / R
    rw [norm_fderiv_toC_local (hχd z)]
    exact hbd z
  have h1 : ‖fderiv ℝ (toC χ) z (Pi.single j 1)‖ ≤ A / R := by
    have h := (fderiv ℝ (toC χ) z).le_opNorm (Pi.single j (1 : ℂ))
    rw [Pi.norm_single, norm_one, mul_one] at h
    exact h.trans hnorm
  have h2 : ‖fderiv ℝ (toC χ) z (Pi.single j Complex.I)‖ ≤ A / R := by
    have h := (fderiv ℝ (toC χ) z).le_opNorm (Pi.single j Complex.I)
    rw [Pi.norm_single, Complex.norm_I, mul_one] at h
    exact h.trans hnorm
  rw [partialZ, norm_div]
  have h3 : ‖(fderiv ℝ (toC χ) z) (Pi.single j 1)
      - Complex.I * (fderiv ℝ (toC χ) z) (Pi.single j Complex.I)‖
      ≤ (A / R) + (A / R) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    exact add_le_add h1 h2
  have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h4]
  linarith

lemma differentiableAt_cutFn {d : ℕ} {R : ℝ} (hR : 0 < R) (z : FormDu d) :
    DifferentiableAt ℝ (cutFn d R) z :=
  (contDiff_cutFn hR).differentiable (by simp) |>.differentiableAt

/-- Bound for the `(0,2)`-form of the `∂̄₂` product rule. -/
lemma exists_norm_liftForm2_cutErr2_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ (X : FormDu d → FormSpace d) (w : FormDu d),
      ‖liftForm2 (cutErr2 d R X) w‖ ≤ C / R * ‖X w‖ := by
  obtain ⟨A, hApos, hA⟩ := exists_norm_fderiv_cutFn_le d hd
  refine ⟨2 * (d : ℝ) ^ 2 * A, by positivity, fun R hR X w => ?_⟩
  have hb : ∀ j : Fin d, ‖partialZbar j (toC (cutFn d R)) w‖ ≤ A / R := fun j =>
    norm_partialZbar_toC_le (fun z => hA R hR z) (differentiableAt_cutFn hR) j w
  have hsum : ∑ l : Fin d, ‖X w l‖ ≤ (d : ℝ) * ‖X w‖ := sum_norm_apply_le d
  have hle_sum : ∀ j : Fin d, ‖X w j‖ ≤ (d : ℝ) * ‖X w‖ := fun j =>
    (Finset.single_le_sum (fun l _ => norm_nonneg _) (Finset.mem_univ j)).trans hsum
  have hterm : ∀ i : Fin d × Fin d, ‖cutErr2 d R X w i‖ ≤ 2 * (d : ℝ) * (A / R) * ‖X w‖ := by
    intro i
    have hstep : ∀ j : Fin d, ‖X w j‖ * (A / R) ≤ (A / R) * ((d : ℝ) * ‖X w‖) := by
      intro j
      calc ‖X w j‖ * (A / R) = (A / R) * ‖X w j‖ := by ring
        _ ≤ (A / R) * ((d : ℝ) * ‖X w‖) :=
            mul_le_mul_of_nonneg_left (hle_sum j) (by positivity)
    calc ‖cutErr2 d R X w i‖
        ≤ ‖X w i.1 * partialZbar i.2 (toC (cutFn d R)) w‖
            + ‖X w i.2 * partialZbar i.1 (toC (cutFn d R)) w‖ := by
          exact norm_sub_le _ _
      _ = ‖X w i.1‖ * ‖partialZbar i.2 (toC (cutFn d R)) w‖
            + ‖X w i.2‖ * ‖partialZbar i.1 (toC (cutFn d R)) w‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖X w i.1‖ * (A / R) + ‖X w i.2‖ * (A / R) :=
          add_le_add (mul_le_mul_of_nonneg_left (hb i.2) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hb i.1) (norm_nonneg _))
      _ ≤ (A / R) * ((d : ℝ) * ‖X w‖) + (A / R) * ((d : ℝ) * ‖X w‖) :=
          add_le_add (hstep i.1) (hstep i.2)
      _ = 2 * (d : ℝ) * (A / R) * ‖X w‖ := by ring
  have hcard : ∀ c : ℝ, (∑ _i : Fin d × Fin d, c ^ 2) = ((d : ℝ) * c) ^ 2 := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hkey : ‖liftForm2 (cutErr2 d R X) w‖ ^ 2
      ≤ (2 * (d : ℝ) ^ 2 * (A / R) * ‖X w‖) ^ 2 := by
    rw [norm_sq_liftForm2]
    calc ∑ i : Fin d × Fin d, ‖cutErr2 d R X w i‖ ^ 2
        ≤ ∑ i : Fin d × Fin d, (2 * (d : ℝ) * (A / R) * ‖X w‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hterm i) 2
      _ = ((d : ℝ) * (2 * (d : ℝ) * (A / R) * ‖X w‖)) ^ 2 := hcard _
      _ = (2 * (d : ℝ) ^ 2 * (A / R) * ‖X w‖) ^ 2 := by ring
  have hlhs : 0 ≤ ‖liftForm2 (cutErr2 d R X) w‖ := norm_nonneg _
  have hrhs : 0 ≤ 2 * (d : ℝ) ^ 2 * (A / R) * ‖X w‖ := by positivity
  calc ‖liftForm2 (cutErr2 d R X) w‖
      = Real.sqrt (‖liftForm2 (cutErr2 d R X) w‖ ^ 2) := (Real.sqrt_sq hlhs).symm
    _ ≤ Real.sqrt ((2 * (d : ℝ) ^ 2 * (A / R) * ‖X w‖) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = 2 * (d : ℝ) ^ 2 * (A / R) * ‖X w‖ := Real.sqrt_sq hrhs
    _ = (2 * (d : ℝ) ^ 2 * A) / R * ‖X w‖ := by ring

/-- Bound for the `(0,1)`-form of the `ϑ_φ` product rule. -/
lemma exists_norm_cutErr1_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ (X : FormDu d → FormSpace d) (w : FormDu d),
      ‖cutErr1 d R X w‖ ≤ C / R * ‖X w‖ := by
  obtain ⟨A, hApos, hA⟩ := exists_norm_fderiv_cutFn_le d hd
  refine ⟨(d : ℝ) * A, by positivity, fun R hR X w => ?_⟩
  have hb : ∀ j : Fin d, ‖partialZ j (toC (cutFn d R)) w‖ ≤ A / R := fun j =>
    norm_partialZ_toC_le (fun z => hA R hR z) (differentiableAt_cutFn hR) j w
  have h1 : ‖cutErr1 d R X w‖ ≤ ∑ j : Fin d, (A / R) * ‖X w j‖ := by
    simp only [cutErr1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb j) (norm_nonneg _)
  have h2 : ∑ j : Fin d, (A / R) * ‖X w j‖ = (A / R) * ∑ j : Fin d, ‖X w j‖ := by
    rw [Finset.mul_sum]
  have h3 : ∑ j : Fin d, ‖X w j‖ ≤ (d : ℝ) * ‖X w‖ := sum_norm_apply_le d
  rw [h2] at h1
  calc ‖cutErr1 d R X w‖ ≤ (A / R) * ∑ j : Fin d, ‖X w j‖ := h1
    _ ≤ (A / R) * ((d : ℝ) * ‖X w‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (d : ℝ) * A / R * ‖X w‖ := by ring

section LpBound

/-- A pointwise norm bound transfers to the `L²`-norms of the corresponding `Lp` elements. -/
lemma norm_toLp_le_of_pointwise {φ : FormDu d → ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : FormDu d → E} {g : FormDu d → F} {c : ℝ} (hc : 0 ≤ c)
    (hfg : ∀ z, ‖f z‖ ≤ c * ‖g z‖)
    (hf : MemLp f 2 (wtMeasure φ)) (hg : MemLp g 2 (wtMeasure φ)) :
    ‖hf.toLp f‖ ≤ c * ‖hg.toLp g‖ := by
  rw [Lp.norm_toLp f hf, Lp.norm_toLp g hg]
  have h1 : eLpNorm f 2 (wtMeasure φ) ≤ ENNReal.ofReal c * eLpNorm g 2 (wtMeasure φ) := by
    have h2 := eLpNorm_mono (p := 2) (μ := wtMeasure φ) (f := f) (g := c • g)
      (fun z => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc]
        exact hfg z)
    rwa [eLpNorm_const_smul, Real.enorm_of_nonneg hc] at h2
  calc (eLpNorm f 2 (wtMeasure φ)).toReal
      ≤ (ENNReal.ofReal c * eLpNorm g 2 (wtMeasure φ)).toReal :=
        ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          hg.eLpNorm_lt_top)) h1
    _ = c * (eLpNorm g 2 (wtMeasure φ)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

end LpBound

/-! ## 3. The cut-off family and the cut-off limits -/

section CutFamily

/-- The cut-off family indexed so that it is admissible for every `R` (the derivative bound is
`A / max R 1`, which tends to `0`). -/
noncomputable def cutFamily (d : ℕ) (R : ℝ) : FormDu d → ℝ := cutFn d (max R 1)

lemma one_le_max (R : ℝ) : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)

lemma cutFamily_nonneg (d : ℕ) (R : ℝ) (w : FormDu d) : 0 ≤ cutFamily d R w :=
  cutFn_nonneg (one_le_max R) w

lemma cutFamily_le_one (d : ℕ) (R : ℝ) (w : FormDu d) : cutFamily d R w ≤ 1 :=
  cutFn_le_one (one_le_max R) w

lemma contDiff_cutFamily (d : ℕ) (R : ℝ) : ContDiff ℝ ∞ (cutFamily d R) :=
  contDiff_cutFn (one_le_max R)

lemma hasCompactSupport_cutFamily (d : ℕ) (R : ℝ) : HasCompactSupport (cutFamily d R) :=
  hasCompactSupport_cutFn (one_le_max R)

lemma cutFamily_eq_one {d : ℕ} (hd : 1 ≤ d) {R : ℝ} {x : FormDu d} (hx : ‖x‖ ≤ R) :
    cutFamily d R x = 1 :=
  cutFn_eq_one hd (one_le_max R) (hx.trans (le_max_left R 1))

lemma cutFamily_eq_zero {d : ℕ} {R : ℝ} {x : FormDu d} (hx : 5 * max R 1 < ‖x‖) :
    cutFamily d R x = 0 :=
  cutFn_eq_zero (one_le_max R) hx

lemma exists_norm_fderiv_cutFamily_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, ∀ x : FormDu d,
      ‖fderiv ℝ (cutFamily d R) x‖ ≤ A / max R 1 := by
  obtain ⟨A, hApos, hA⟩ := exists_norm_fderiv_cutFn_le d hd
  exact ⟨A, hApos, fun R x => hA _ (one_le_max R) x⟩

lemma tendsto_cutFamily_one (d : ℕ) (hd : 1 ≤ d) (w : FormDu d) :
    Tendsto (fun R : ℝ => cutFamily d R w) atTop (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ‖w‖] with R hR
  exact (cutFamily_eq_one hd hR).symm

lemma tendsto_max_one : Tendsto (fun R : ℝ => max R 1) atTop atTop :=
  tendsto_atTop_mono (fun R => le_max_left R 1) tendsto_id

lemma tendsto_div_max_one (A : ℝ) : Tendsto (fun R : ℝ => A / max R 1) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp tendsto_max_one
  have h2 : Tendsto (fun R : ℝ => A * (max R 1)⁻¹) atTop (nhds (A * 0)) :=
    tendsto_const_nhds.mul h
  simpa [div_eq_mul_inv] using h2

/-- The norms of `toC χ w`. -/
lemma norm_toC (d : ℕ) (χ : FormDu d → ℝ) (w : FormDu d) : ‖toC χ w‖ = |χ w| := by
  rw [toC, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]

lemma norm_toC_smul (d : ℕ) (χ : FormDu d → ℝ) (w : FormDu d) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (v : E) :
    ‖toC χ w • v‖ = ‖χ w • v‖ := by
  rw [norm_smul, norm_smul, norm_toC, Real.norm_eq_abs]

/-- Subtracting the identity from the multiplication by `toC χ`. -/
lemma norm_toC_smul_sub (d : ℕ) (χ : FormDu d → ℝ) (w : FormDu d) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (v : E) :
    ‖toC χ w • v - v‖ = ‖(1 - χ w) • v‖ := by
  have h1 : toC χ w • v - v = (((χ w - 1 : ℝ)) : ℂ) • v := by
    have hx : toC χ w = (((χ w : ℝ)) : ℂ) := rfl
    calc toC χ w • v - v = (((χ w : ℝ)) : ℂ) • v - (1 : ℂ) • v := by rw [hx, one_smul]
      _ = ((((χ w : ℝ)) : ℂ) - 1) • v := (sub_smul _ _ _).symm
      _ = (((χ w - 1 : ℝ)) : ℂ) • v := by
          congr 1
          push_cast
          ring
  rw [h1, norm_smul, norm_smul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, Real.norm_eq_abs,
    abs_sub_comm]

end CutFamily

section CutErr

/-- Multiplication by `toC χ` preserves `L²(μ_φ)` when `0 ≤ χ ≤ 1`. -/
lemma memLp_smul_toC {d : ℕ} {φ : FormDu d → ℝ} {χ : FormDu d → ℝ} (hχc : Continuous χ)
    (hχnn : ∀ w, 0 ≤ χ w) (hχ1 : ∀ w, χ w ≤ 1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : FormDu d → E} (hX : MemLp X 2 (wtMeasure φ)) :
    MemLp (fun w => toC χ w • X w) 2 (wtMeasure φ) := by
  refine MemLp.mono hX ?_ ?_
  · exact AEStronglyMeasurable.smul
      ((Complex.continuous_ofReal.comp hχc).aestronglyMeasurable) hX.aestronglyMeasurable
  · filter_upwards with w
    rw [norm_toC_smul]
    have hb : ‖χ w‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχnn w)]
      exact hχ1 w
    calc ‖χ w • X w‖ = ‖χ w‖ * ‖X w‖ := norm_smul _ _
      _ ≤ 1 * ‖X w‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖X w‖ := one_mul _

/-- Multiplication by `toC χ` preserves compact support. -/
lemma hasCompactSupport_smul_toC {d : ℕ} {χ : FormDu d → ℝ} (hχs : HasCompactSupport χ)
    {E : Type*} [Zero E] [SMulWithZero ℂ E] (X : FormDu d → E) :
    HasCompactSupport (fun w => toC χ w • X w) := by
  refine hχs.mono ?_
  intro w hw
  simp only [Function.mem_support] at hw ⊢
  intro h
  exact hw (by simp only [toC, h, Complex.ofReal_zero, zero_smul])

/-- A `ℂ`-valued function on a finite index type is a.e. strongly measurable as soon as its
components are a.e. measurable. -/
lemma aestronglyMeasurable_pi_of_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι] {Ψ : α → (ι → ℂ)}
    (h : ∀ i, AEMeasurable (fun w => Ψ w i) μ) : AEStronglyMeasurable Ψ μ :=
  (aemeasurable_pi_iff.mpr h).aestronglyMeasurable

end CutErr

section CutErrLp

variable {d : ℕ}

/-- The constant in the `O(1/R)` bound for the `(0,2)`-error term. -/
noncomputable def cutErr2Const (d : ℕ) (hd : 1 ≤ d) : ℝ :=
  Classical.choose (exists_norm_liftForm2_cutErr2_le d hd)

lemma cutErr2Const_pos (d : ℕ) (hd : 1 ≤ d) : 0 < cutErr2Const d hd :=
  (Classical.choose_spec (exists_norm_liftForm2_cutErr2_le d hd)).1

lemma norm_liftForm2_cutErr2_le (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R)
    (X : FormDu d → FormSpace d) (w : FormDu d) :
    ‖liftForm2 (cutErr2 d R X) w‖ ≤ cutErr2Const d hd / R * ‖X w‖ :=
  (Classical.choose_spec (exists_norm_liftForm2_cutErr2_le d hd)).2 R hR X w

/-- The constant in the `O(1/R)` bound for the `(0,1)`-error term. -/
noncomputable def cutErr1Const (d : ℕ) (hd : 1 ≤ d) : ℝ :=
  Classical.choose (exists_norm_cutErr1_le d hd)

lemma cutErr1Const_pos (d : ℕ) (hd : 1 ≤ d) : 0 < cutErr1Const d hd :=
  (Classical.choose_spec (exists_norm_cutErr1_le d hd)).1

lemma norm_cutErr1_le (d : ℕ) (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R)
    (X : FormDu d → FormSpace d) (w : FormDu d) :
    ‖cutErr1 d R X w‖ ≤ cutErr1Const d hd / R * ‖X w‖ :=
  (Classical.choose_spec (exists_norm_cutErr1_le d hd)).2 R hR X w

lemma continuous_apply_formSpace {d : ℕ} (j : Fin d) :
    Continuous (fun v : FormSpace d => v j) :=
  PiLp.continuous_apply 2 (fun _ : Fin d => ℂ) j

/-- The `(0,2)`-error term of the `∂̄₂` product rule is in `L²(μ_φ)`. -/
lemma memLp_liftForm2_cutErr2 (hd : 1 ≤ d) {φ : FormDu d → ℝ} (R : ℝ)
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    MemLp (liftForm2 (cutErr2 d (max R 1) X)) 2 (wtMeasure φ) := by
  have hXj : ∀ j : Fin d, AEMeasurable (fun w => X w j) (wtMeasure φ) := fun j =>
    (Continuous.comp_aestronglyMeasurable (continuous_apply_formSpace j)
      hX.aestronglyMeasurable).aemeasurable
  have hχ : ContDiff ℝ 1 (toC (cutFn d (max R 1))) :=
    contDiff_toC ((contDiff_cutFn (one_le_max R)).of_le (by norm_num))
  have hχm : ∀ j : Fin d,
      AEMeasurable (fun w => partialZbar j (toC (cutFn d (max R 1))) w) (wtMeasure φ) :=
    fun j => (continuous_partialZbar hχ j).aemeasurable
  have hmeas : AEMeasurable (cutErr2 d (max R 1) X) (wtMeasure φ) := by
    rw [aemeasurable_pi_iff]
    intro i
    exact ((hXj i.1).mul (hχm i.2)).sub ((hXj i.2).mul (hχm i.1))
  have hstrong : AEStronglyMeasurable (liftForm2 (cutErr2 d (max R 1) X)) (wtMeasure φ) :=
    Continuous.comp_aestronglyMeasurable (f := cutErr2 d (max R 1) X)
      (PiLp.continuous_toLp 2 (fun _ : Fin d × Fin d => ℂ)) hmeas.aestronglyMeasurable
  refine MemLp.mono (hX.const_smul (cutErr2Const d hd / max R 1)) hstrong ?_
  filter_upwards with w
  have hc : 0 ≤ cutErr2Const d hd / max R 1 :=
    le_of_lt (div_pos (cutErr2Const_pos d hd) (one_le_max R))
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc]
  exact norm_liftForm2_cutErr2_le d hd (max R 1) (one_le_max R) X w

/-- The `(0,1)`-error term of the `ϑ_φ` product rule is in `L²(μ_φ)`. -/
lemma memLp_cutErr1 (hd : 1 ≤ d) {φ : FormDu d → ℝ} (R : ℝ)
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    MemLp (cutErr1 d (max R 1) X) 2 (wtMeasure φ) := by
  have hXj : ∀ j : Fin d, AEMeasurable (fun w => X w j) (wtMeasure φ) := fun j =>
    (Continuous.comp_aestronglyMeasurable (continuous_apply_formSpace j)
      hX.aestronglyMeasurable).aemeasurable
  have hχ : ContDiff ℝ 1 (toC (cutFn d (max R 1))) :=
    contDiff_toC ((contDiff_cutFn (one_le_max R)).of_le (by norm_num))
  have hχm : ∀ j : Fin d,
      AEMeasurable (fun w => partialZ j (toC (cutFn d (max R 1))) w) (wtMeasure φ) :=
    fun j => (continuous_partialZ hχ j).aemeasurable
  have hsum : AEMeasurable (fun w => ∑ j : Fin d,
      partialZ j (toC (cutFn d (max R 1))) w * X w j) (wtMeasure φ) := by
    have h := Finset.aemeasurable_sum (s := Finset.univ)
      (f := fun j w => partialZ j (toC (cutFn d (max R 1))) w * X w j)
      (fun j _ => (hχm j).mul (hXj j))
    convert h using 1
    funext w
    rw [Finset.sum_apply]
  have hmeas : AEMeasurable (cutErr1 d (max R 1) X) (wtMeasure φ) := hsum
  refine MemLp.mono (hX.const_smul (cutErr1Const d hd / max R 1))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with w
  have hc : 0 ≤ cutErr1Const d hd / max R 1 :=
    le_of_lt (div_pos (cutErr1Const_pos d hd) (one_le_max R))
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc]
  exact norm_cutErr1_le d hd (max R 1) (one_le_max R) X w

/-- The `L²`-norm of the `(0,2)`-error term is `O(1/R)`. -/
lemma norm_toLp_liftForm2_cutErr2_le (hd : 1 ≤ d) {φ : FormDu d → ℝ} (R : ℝ)
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    ‖(memLp_liftForm2_cutErr2 hd R hX).toLp (liftForm2 (cutErr2 d (max R 1) X))‖
      ≤ cutErr2Const d hd / max R 1 * ‖hX.toLp X‖ :=
  norm_toLp_le_of_pointwise (f := liftForm2 (cutErr2 d (max R 1) X)) (g := X)
    (c := cutErr2Const d hd / max R 1)
    (le_of_lt (div_pos (cutErr2Const_pos d hd) (one_le_max R)))
    (fun w => norm_liftForm2_cutErr2_le d hd (max R 1) (one_le_max R) X w)
    (memLp_liftForm2_cutErr2 hd R hX) hX

/-- The `L²`-norm of the `(0,1)`-error term is `O(1/R)`. -/
lemma norm_toLp_cutErr1_le (hd : 1 ≤ d) {φ : FormDu d → ℝ} (R : ℝ)
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    ‖(memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)‖
      ≤ cutErr1Const d hd / max R 1 * ‖hX.toLp X‖ :=
  norm_toLp_le_of_pointwise (f := cutErr1 d (max R 1) X) (g := X)
    (c := cutErr1Const d hd / max R 1)
    (le_of_lt (div_pos (cutErr1Const_pos d hd) (one_le_max R)))
    (fun w => norm_cutErr1_le d hd (max R 1) (one_le_max R) X w)
    (memLp_cutErr1 hd R hX) hX

/-- **Cut-off limit, `H₂`-part**: `χ_R • u → u`. -/
theorem tendsto_cutFamily_sub (hd : 1 ≤ d) {φ : FormDu d → ℝ} (hφc : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : FormDu d → E} (hu : MemLp u 2 (wtMeasure φ)) :
    Tendsto (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
        (cutFamily_nonneg d R) (cutFamily_le_one d R) hu).toLp
          (fun w => toC (cutFamily d R) w • u w) - hu.toLp u‖) atTop (nhds 0) := by
  have hFc : Continuous (fun z : FormDu d => Real.exp (-(φ z))) :=
    Real.continuous_exp.comp hφc.neg
  have hFnn : ∀ z : FormDu d, 0 ≤ Real.exp (-(φ z)) := fun z => Real.exp_nonneg _
  have hlim := Commons.MeasureTheory.tendsto_lintegral_ofReal_sq_one_sub_smul_cutoff
    hFc hFnn u hu (fun R => cutFamily d R) (fun R => (contDiff_cutFamily d R).continuous)
    (Filter.Eventually.of_forall fun R w =>
      ⟨cutFamily_nonneg d R w, cutFamily_le_one d R w⟩)
    (fun w => by
      filter_upwards [eventually_ge_atTop ‖w‖] with R hR
      exact cutFamily_eq_one hd hR)
  refine (Commons.MeasureTheory.Lp.tendsto_norm_toLp_sub_of_tendsto_lintegral_ofReal
    hFc hFnn
    (w := fun R w => toC (cutFamily d R) w • u w) (u := u)
    (fun R => memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
      (cutFamily_le_one d R) hu) hu ?_)
  refine hlim.congr' ?_
  filter_upwards with R
  refine lintegral_congr fun w => ?_
  rw [norm_toC_smul_sub]

/-- **Cut-off limit, `∂̄₂`-part**: `χ_R • ζ + e_R → ζ`. -/
theorem tendsto_cutFamily_S (hd : 1 ≤ d) {φ : FormDu d → ℝ} (hφc : Continuous φ)
    {ζ : FormDu d → FormSpace2 d} (hζ : MemLp ζ 2 (wtMeasure φ))
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    Tendsto (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
          (cutFamily_nonneg d R) (cutFamily_le_one d R) hζ).toLp
            (fun w => toC (cutFamily d R) w • ζ w)
        + (memLp_liftForm2_cutErr2 hd R hX).toLp (liftForm2 (cutErr2 d (max R 1) X))
        - hζ.toLp ζ‖) atTop (nhds 0) := by
  have h1 : Tendsto (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
      (cutFamily_nonneg d R) (cutFamily_le_one d R) hζ).toLp
        (fun w => toC (cutFamily d R) w • ζ w) - hζ.toLp ζ‖) atTop (nhds 0) :=
    tendsto_cutFamily_sub hd hφc hζ
  have h2 : Tendsto (fun R : ℝ => ‖(memLp_liftForm2_cutErr2 hd R hX).toLp
      (liftForm2 (cutErr2 d (max R 1) X))‖) atTop (nhds 0) := by
    have hmul : Tendsto (fun R : ℝ => cutErr2Const d hd / max R 1 * ‖hX.toLp X‖)
        atTop (nhds 0) := by
      have h := (tendsto_div_max_one (cutErr2Const d hd)).mul_const (‖hX.toLp X‖)
      simpa only [zero_mul] using h
    exact squeeze_zero_norm' (Filter.Eventually.of_forall fun R => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_toLp_liftForm2_cutErr2_le hd R hX) hmul
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun R => ?_)
    (by simpa only [add_zero] using h1.add h2)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hζ).toLp (fun w => toC (cutFamily d R) w • ζ w)
        + (memLp_liftForm2_cutErr2 hd R hX).toLp (liftForm2 (cutErr2 d (max R 1) X))
        - hζ.toLp ζ‖
      = ‖((memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hζ).toLp (fun w => toC (cutFamily d R) w • ζ w) - hζ.toLp ζ)
        + (memLp_liftForm2_cutErr2 hd R hX).toLp (liftForm2 (cutErr2 d (max R 1) X))‖ := by
        abel
    _ ≤ ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hζ).toLp (fun w => toC (cutFamily d R) w • ζ w)
          - hζ.toLp ζ‖
        + ‖(memLp_liftForm2_cutErr2 hd R hX).toLp (liftForm2 (cutErr2 d (max R 1) X))‖ :=
        norm_add_le _ _

/-- **Cut-off limit, `ϑ_φ`-part**: `χ_R • z - f_R → z`. -/
theorem tendsto_cutFamily_A (hd : 1 ≤ d) {φ : FormDu d → ℝ} (hφc : Continuous φ)
    {z : FormDu d → ℂ} (hz : MemLp z 2 (wtMeasure φ))
    {X : FormDu d → FormSpace d} (hX : MemLp X 2 (wtMeasure φ)) :
    Tendsto (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
          (cutFamily_nonneg d R) (cutFamily_le_one d R) hz).toLp
            (fun w => toC (cutFamily d R) w • z w)
        - (memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)
        - hz.toLp z‖) atTop (nhds 0) := by
  have h1 : Tendsto (fun R : ℝ => ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous
      (cutFamily_nonneg d R) (cutFamily_le_one d R) hz).toLp
        (fun w => toC (cutFamily d R) w • z w) - hz.toLp z‖) atTop (nhds 0) :=
    tendsto_cutFamily_sub hd hφc hz
  have h2 : Tendsto (fun R : ℝ => ‖(memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)‖)
      atTop (nhds 0) := by
    have hmul : Tendsto (fun R : ℝ => cutErr1Const d hd / max R 1 * ‖hX.toLp X‖)
        atTop (nhds 0) := by
      have h := (tendsto_div_max_one (cutErr1Const d hd)).mul_const (‖hX.toLp X‖)
      simpa only [zero_mul] using h
    exact squeeze_zero_norm' (Filter.Eventually.of_forall fun R => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_toLp_cutErr1_le hd R hX) hmul
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun R => ?_)
    (by simpa only [add_zero] using h1.add h2)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hz).toLp (fun w => toC (cutFamily d R) w • z w)
        - (memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)
        - hz.toLp z‖
      = ‖((memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hz).toLp (fun w => toC (cutFamily d R) w • z w) - hz.toLp z)
        - (memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)‖ := by
        abel
    _ ≤ ‖(memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
          (cutFamily_le_one d R) hz).toLp (fun w => toC (cutFamily d R) w • z w)
          - hz.toLp z‖
        + ‖(memLp_cutErr1 hd R hX).toLp (cutErr1 d (max R 1) X)‖ :=
        norm_sub_le _ _

end CutErrLp

section Friedrichs

variable {φ : FormDu d → ℝ}

/-- The cut-off `χ_R • x` of an `L²(μ_φ)` `(0,1)`-form. -/
noncomputable def cutX (R : ℝ) (x : H2 φ) : FormDu d → FormSpace d :=
  fun w => toC (cutFamily d R) w • (x : FormDu d → FormSpace d) w

lemma memLp_cutX (R : ℝ) (x : H2 φ) : MemLp (cutX (φ := φ) R x) 2 (wtMeasure φ) :=
  memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
    (cutFamily_le_one d R) (Lp.memLp x)

/-- The cut-off `χ_R • ζ` of an `L²(μ_φ)` `(0,2)`-form. -/
noncomputable def cutZeta (R : ℝ) (z : H3 φ) : FormDu d → FormSpace2 d :=
  fun w => toC (cutFamily d R) w • (z : FormDu d → FormSpace2 d) w

lemma memLp_cutZeta (R : ℝ) (z : H3 φ) : MemLp (cutZeta (φ := φ) R z) 2 (wtMeasure φ) :=
  memLp_smul_toC (contDiff_cutFamily d R).continuous (cutFamily_nonneg d R)
    (cutFamily_le_one d R) (Lp.memLp z)

/-- The cut-off `χ_R • z` of an `L²(μ_φ)` function. -/
noncomputable def cutZc (R : ℝ) (z : H1 φ) : FormDu d → ℂ :=
  fun w => toC (cutFamily d R) w * (z : FormDu d → ℂ) w

lemma memLp_cutZc (R : ℝ) (z : H1 φ) : MemLp (cutZc (φ := φ) R z) 2 (wtMeasure φ) := by
  refine MemLp.mono (Lp.memLp z) ?_ ?_
  · exact AEStronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp (contDiff_cutFamily d R).continuous).aestronglyMeasurable)
      (Lp.memLp z).aestronglyMeasurable
  · filter_upwards with w
    have hb : ‖toC (cutFamily d R) w‖ ≤ 1 := by
      rw [norm_toC, abs_of_nonneg (cutFamily_nonneg d R w)]
      exact cutFamily_le_one d R w
    calc ‖toC (cutFamily d R) w * (z : FormDu d → ℂ) w‖
        = ‖toC (cutFamily d R) w‖ * ‖(z : FormDu d → ℂ) w‖ := norm_mul _ _
      _ ≤ 1 * ‖(z : FormDu d → ℂ) w‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖(z : FormDu d → ℂ) w‖ := one_mul _

/-- The `(0,2)`-error term of the cut-off. -/
noncomputable def cutE2 (R : ℝ) (x : H2 φ) : FormDu d → (Fin d × Fin d → ℂ) :=
  cutErr2 d (max R 1) (x : FormDu d → FormSpace d)

lemma memLp_cutE2 (hd : 1 ≤ d) (R : ℝ) (x : H2 φ) :
    MemLp (liftForm2 (cutE2 (φ := φ) R x)) 2 (wtMeasure φ) :=
  memLp_liftForm2_cutErr2 hd R (Lp.memLp x)

/-- The `(0,1)`-error term of the cut-off. -/
noncomputable def cutE1 (R : ℝ) (x : H2 φ) : FormDu d → ℂ :=
  cutErr1 d (max R 1) (x : FormDu d → FormSpace d)

lemma memLp_cutE1 (hd : 1 ≤ d) (R : ℝ) (x : H2 φ) :
    MemLp (cutE1 (φ := φ) R x) 2 (wtMeasure φ) :=
  memLp_cutErr1 hd R (Lp.memLp x)

/-- The cut-off of a `∂̄₂`-closed form stays `∂̄₂`-closed, with the value given by the product
rule. -/
lemma dbarWeak2_cutX (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {x : H2 φ} (hxS : x ∈ (dbarOp2 φ).domain) (R : ℝ) :
    DbarWeak2 φ ((memLp_cutX (φ := φ) R x).toLp (cutX (φ := φ) R x))
      ((memLp_cutZeta (φ := φ) R ((dbarOp2 φ) ⟨x, hxS⟩)).toLp
          (cutZeta (φ := φ) R ((dbarOp2 φ) ⟨x, hxS⟩))
        + (memLp_cutE2 (d := d) hd R x).toLp (liftForm2 (cutE2 (φ := φ) R x))) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨ζ, hζ⟩ := mem_dbarOp2_domain.mp hxS
  have h0 : DbarWeak2 φ x ((dbarOp2 φ) ⟨x, hxS⟩) := by
    rw [dbarOp2_apply_eq (hφ := hφ1) hxS hζ]; exact hζ
  exact dbarWeak2_mul (φ := φ) hφ1 h0 (contDiff_cutFamily d R)
    (hasCompactSupport_cutFamily d R) (memLp_cutX (φ := φ) R x)
    (memLp_cutZeta (φ := φ) R ((dbarOp2 φ) ⟨x, hxS⟩)) (memLp_cutE2 (d := d) hd R x)

/-- The cut-off of a `ϑ_φ`-form stays in the domain of `ϑ_φ`. -/
lemma dbarAdjWeak_cutX (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {x : H2 φ} (hxA : x ∈ (dbarAdjOp φ).domain) (R : ℝ) :
    dbarAdjWeak φ ((memLp_cutX (φ := φ) R x).toLp (cutX (φ := φ) R x))
      ((memLp_cutZc (φ := φ) R ((dbarAdjOp φ) ⟨x, hxA⟩)).toLp
          (cutZc (φ := φ) R ((dbarAdjOp φ) ⟨x, hxA⟩))
        - (memLp_cutE1 (d := d) hd R x).toLp (cutE1 (φ := φ) R x)) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨z, hz⟩ := mem_dbarAdjOp_domain.mp hxA
  have h0 : dbarAdjWeak φ x ((dbarAdjOp φ) ⟨x, hxA⟩) := by
    rw [dbarAdjOp_apply_eq (hφ := hφ1) hxA hz]; exact hz
  exact dbarAdjWeak_mul (φ := φ) hφ1 h0 (contDiff_cutFamily d R)
    (hasCompactSupport_cutFamily d R) (memLp_cutX (φ := φ) R x)
    (memLp_cutZc (φ := φ) R ((dbarAdjOp φ) ⟨x, hxA⟩)) (memLp_cutE1 (d := d) hd R x)

end Friedrichs

section SmoothFormDef

variable {φ : FormDu d → ℝ}

/-- A smooth compactly supported `(0,1)`-form, packaged with the `L²(μ_φ)`-membership of itself
and of its two weak derivatives. -/
structure SmoothForm (φ : FormDu d → ℝ) where
  f : FormDu d → FormSpace d
  smooth : ContDiff ℝ ∞ f
  csupport : HasCompactSupport f
  memLp : MemLp f 2 (wtMeasure φ)
  memLpS : MemLp (liftForm2 (dbarFormFun2 (toFormFun f))) 2 (wtMeasure φ)
  memLpA : MemLp (dbarAdjoint φ (toFormFun f)) 2 (wtMeasure φ)

namespace SmoothForm

variable {φ : FormDu d → ℝ}

/-- The class of the form in `H₂`. -/
noncomputable def toH2 (y : SmoothForm φ) : H2 φ := y.memLp.toLp y.f

/-- The weak `∂̄₂` of the form. -/
noncomputable def Sval (y : SmoothForm φ) : H3 φ :=
  y.memLpS.toLp (liftForm2 (dbarFormFun2 (toFormFun y.f)))

/-- The weak `ϑ_φ` of the form. -/
noncomputable def Aval (y : SmoothForm φ) : H1 φ :=
  y.memLpA.toLp (dbarAdjoint φ (toFormFun y.f))

lemma liftForm_toFormFun (y : SmoothForm φ) : liftForm (toFormFun y.f) = y.f := by
  funext z
  simp only [liftForm, toFormFun, WithLp.equiv_apply, WithLp.toLp_ofLp]

lemma memLp_lift (y : SmoothForm φ) : MemLp (liftForm (toFormFun y.f)) 2 (wtMeasure φ) := by
  rw [liftForm_toFormFun]; exact y.memLp

lemma toLp_lift_eq_toH2 (y : SmoothForm φ) :
    (y.memLp_lift).toLp (liftForm (toFormFun y.f)) = y.toH2 :=
  MemLp.toLp_congr y.memLp_lift y.memLp (by rw [liftForm_toFormFun])

lemma contDiff_comp (y : SmoothForm φ) (j : Fin d) :
    ContDiff ℝ ∞ (fun z => toFormFun y.f z j) := by
  have h := (contDiff_piLp 2).mp y.smooth j
  simpa only [toFormFun, WithLp.equiv_apply] using h

lemma hasCompactSupport_apply (y : SmoothForm φ) (j : Fin d) :
    HasCompactSupport (fun z => toFormFun y.f z j) :=
  Submission.FUP.hasCompactSupport_comp j (hasCompactSupport_toFormFun y.csupport)

theorem dbarWeak2 (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    DbarWeak2 φ y.toH2 y.Sval := by
  have h := dbarWeak2_smooth hφ (fun j => y.contDiff_comp j) (fun j => y.hasCompactSupport_apply j)
    y.memLp_lift y.memLpS
  rwa [y.toLp_lift_eq_toH2] at h

theorem mem_domain_dbarOp2 (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    y.toH2 ∈ (dbarOp2 φ).domain :=
  mem_dbarOp2_domain.mpr ⟨y.Sval, y.dbarWeak2 hφ⟩

theorem dbarOp2_apply (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    (dbarOp2 φ) ⟨y.toH2, y.mem_domain_dbarOp2 hφ⟩ = y.Sval :=
  dbarOp2_apply_eq (hφ := hφ) _ (y.dbarWeak2 hφ)

theorem dbarAdjWeak (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    dbarAdjWeak φ y.toH2 y.Aval := by
  have h := dbarAdjWeak_smooth hφ (fun j => y.contDiff_comp j)
    (fun j => Submission.FUP.hasCompactSupport_comp j (hasCompactSupport_toFormFun y.csupport))
    y.memLp_lift y.memLpA
  rwa [y.toLp_lift_eq_toH2] at h

theorem mem_domain_dbarAdjOp (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    y.toH2 ∈ (dbarAdjOp φ).domain :=
  mem_dbarAdjOp_domain.mpr ⟨y.Aval, y.dbarAdjWeak hφ⟩

theorem dbarAdjOp_apply (hφ : ContDiff ℝ 1 φ) (y : SmoothForm φ) :
    (dbarAdjOp φ) ⟨y.toH2, y.mem_domain_dbarAdjOp hφ⟩ = y.Aval :=
  dbarAdjOp_apply_eq (hφ := hφ) _ (y.dbarAdjWeak hφ)

end SmoothForm

end SmoothFormDef

section Defect

variable {φ : FormDu d → ℝ}

/-- The adjoint-side defect of the mollification is a.e. strongly measurable. -/
lemma aestronglyMeasurable_dbarAdjDefect {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ)
    {ρ : FormDu d → ℝ} (hρc : Continuous ρ) {X : FormDu d → FormSpace d}
    (hX : AEStronglyMeasurable X (volume : Measure (FormDu d))) :
    AEStronglyMeasurable (dbarAdjDefect φ ρ X) (volume : Measure (FormDu d)) := by
  set X' := hX.mk X with hX'def
  have hX'm : StronglyMeasurable X' := hX.stronglyMeasurable_mk
  have hX'ae : X =ᵐ[(volume : Measure (FormDu d))] X' := hX.ae_eq_mk
  have hXj : ∀ j : Fin d, StronglyMeasurable
      (fun p : FormDu d × FormDu d => (X' (p.1 - p.2)).ofLp j) := by
    intro j
    have h1 : StronglyMeasurable (fun p : FormDu d × FormDu d => X' (p.1 - p.2)) :=
      hX'm.comp_measurable (measurable_fst.sub measurable_snd)
    have h2 : StronglyMeasurable (fun v : FormSpace d => v.ofLp j) :=
      ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin d → ℂ))).stronglyMeasurable
    exact h2.comp_measurable h1.measurable
  have huncurry : AEStronglyMeasurable (fun p : FormDu d × FormDu d =>
      ρ p.2 • (∑ j ∈ (Finset.univ : Finset (Fin d)),
        (partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1) * X' (p.1 - p.2) j))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
    refine AEStronglyMeasurable.smul (𝕜 := ℝ) ?_ ?_
    · exact (hρc.comp continuous_snd).aestronglyMeasurable
    · have hsum : AEStronglyMeasurable (fun p : FormDu d × FormDu d =>
          ∑ j : Fin d, (partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1)
            * X' (p.1 - p.2) j)
          ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
        refine (Finset.aemeasurable_sum (M := ℂ) (s := Finset.univ)
          (μ := (volume : Measure (FormDu d)).prod (volume : Measure (FormDu d)))
          (f := fun j (p : FormDu d × FormDu d) =>
            (partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1) * X' (p.1 - p.2) j)
          (fun j _ => ((((continuous_partialZ (contDiff_toC hφ) j).comp
                (continuous_fst.sub continuous_snd)).sub
              ((continuous_partialZ (contDiff_toC hφ) j).comp continuous_fst)).aemeasurable).mul
            ((hXj j).aemeasurable))).aestronglyMeasurable.congr ?_
        filter_upwards with p
        rw [Finset.sum_apply]
      exact hsum
  have hstep : AEStronglyMeasurable (dbarAdjDefect φ ρ X') (volume : Measure (FormDu d)) :=
    huncurry.integral_prod_right'
  refine hstep.congr ?_
  filter_upwards with u
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_sub_left u).quasiMeasurePreserving.ae_eq_comp hX'ae]
    with y hy
  simp only [Function.comp_apply] at hy
  simp only [dbarAdjDefectFun, hy]

/-- `dbarAdjDefect` only depends on the a.e.-class of `X`. -/
lemma dbarAdjDefect_congr_ae {φ : FormDu d → ℝ} {ρ : FormDu d → ℝ}
    {V W : FormDu d → FormSpace d} (h : V =ᵐ[(volume : Measure (FormDu d))] W) :
    dbarAdjDefect φ ρ V = dbarAdjDefect φ ρ W := by
  funext u
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_sub_left u).quasiMeasurePreserving.ae_eq_comp h]
    with y hy
  simp only [Function.comp_apply] at hy
  simp only [dbarAdjDefectFun, hy]

end Defect

end Submission.FUP
