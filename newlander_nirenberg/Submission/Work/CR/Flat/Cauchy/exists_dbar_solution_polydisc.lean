import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.dbarCoord_setIntegral_shift
import Submission.Work.CR.Flat.Cauchy.exists_norm_fderiv_le_of_halfPolydisc_support
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin
import Submission.Work.CR.Flat.Cauchy.integral_dbarC_translate
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-! ### Elementary glue

These lemmas move between the `n`-variable `∂̄`-operator `dbarCoord` of
`Submission/Work/CR/Flat/Polydisc.lean` and the one-variable `dbarC` of
`Submission/Work/CR/Flat/Cauchy.lean` applied to a slice, and record how `dbarCoord`
behaves under multiplication by a constant and under translations.
-/

/-- `∂̄` commutes with multiplication by a constant, for a differentiable function. -/
lemma dbarSolution_dbarCoord_const_mul {n : ℕ} (k : Fin n) (c : ℂ) {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hφ : DifferentiableAt ℝ φ z) :
    dbarCoord k (fun y => c * φ y) z = c * dbarCoord k φ z := by
  have h : fderiv ℝ (fun y => c * φ y) z = c • fderiv ℝ φ z := fderiv_const_mul hφ c
  rw [dbarCoord, dbarCoord, h]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The `(0,1)`-derivative on `ℂ` of the slice `w ↦ g (z with z_j = w)` is the `j`-th
`(0,1)`-derivative of `g` at the corresponding point. -/
lemma dbarSolution_dbarC_update_eq_dbarCoord {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    {u : ℂ} (hg : DifferentiableAt ℝ g (Function.update z j u)) :
    dbarC (fun w : ℂ => g (Function.update z j w)) u = dbarCoord j g (Function.update z j u) := by
  -- the affine map `w ↦ Function.update z j w` has derivative `Pi.single j`
  have hL : HasFDerivAt (fun w : ℂ => Function.update z j w)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) u := by
    have hfun : (fun w : ℂ => Function.update z j w)
        = fun w : ℂ => Function.update z j 0 +
            (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
      funext w
      rw [ContinuousLinearMap.single_apply]
      ext i
      by_cases h : i = j <;> simp [h]
    rw [hfun]
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
      (x := u)).const_add (Function.update z j 0)
  have hcomp := (hg.hasFDerivAt).comp u hL
  simp only [Function.comp_def] at hcomp
  rw [dbarC, dbarCoord, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]

/-- Slices of `C¹` functions are `C¹`. -/
lemma dbarSolution_contDiff_update {n : ℕ} (j : Fin n) (z : Fin n → ℂ) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (fun w : ℂ => g (Function.update z j w)) := by
  have hS : ContDiff ℝ 1 (fun w : ℂ => Function.update z j w) := by
    have hfun : (fun w : ℂ => Function.update z j w)
        = fun w : ℂ => Function.update z j 0 +
            (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
      funext w
      rw [ContinuousLinearMap.single_apply]
      ext i
      by_cases h : i = j <;> simp [h]
    rw [hfun]
    simpa only [Pi.add_apply] using
      contDiff_const.add (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j))
  simpa only [Function.comp_def] using hg.comp hS

/-- `Function.update z j (z j + w) = z + Function.update 0 j w`: shifting the `j`-th
coordinate of `z` by `w` is adding the vector `w e_j`. -/
lemma dbarSolution_update_self_add {n : ℕ} (j : Fin n) (z : Fin n → ℂ) (w : ℂ) :
    Function.update z j (z j + w) = z + Function.update (0 : Fin n → ℂ) j w := by
  ext i
  by_cases h : i = j <;> simp [h]

/-- The `j`-th slice of a form whose components vanish off the open half-size polydisc
vanishes off the disc of radius `r j / 2` about `c j`. -/
lemma dbarSolution_slice_zero {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hsupp : ∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0) (k j : Fin n) (z : Fin n → ℂ) :
    ∀ w : ℂ, r j / 2 ≤ ‖w - c j‖ → f k (Function.update z j w) = 0 := by
  intro w hw
  exact hsupp k _ ⟨j, by simpa [Function.update_self] using hw⟩


/-! ### The one-variable input

Pompeiu's formula: the Cauchy transform of `∂̄g` inverts `∂̄`.  On the disc of radius `ρ`, the
integral of `∂̄g` against the Cauchy kernel `1/w` equals `-π g`.  The case of the pole at the
origin (`cauchyGreen_origin`) is available in the workspace; here it is translated to a general
pole (`dbarSolution_cauchyGreen_at`) and then combined with the change of variables
`integral_dbarC_translate` and the mean-zero property `∫_{‖w‖<ρ} 1/w = 0` of the Cauchy kernel
(`integral_inv_ball`) to get the shifted form (`dbarSolution_dbarC_shift_pompeiu_self`) used by the slice
argument for polydiscs.
-/

/-- If `D` is continuous then subtracting its value at `z` does not change the Cauchy-kernel
integral over a disc: the subtracted constant `D z` has mean zero against `1/w`. -/
lemma dbarSolution_setIntegral_sub_sub_div {ρ : ℝ} (hρ : 0 < ρ) {D : ℂ → ℂ} (hD : Continuous D) (z : ℂ) :
    ∫ w in Metric.ball (0 : ℂ) ρ, (D (z + w) - D z) / w
      = ∫ w in Metric.ball (0 : ℂ) ρ, D (z + w) / w := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn
    ((hD.comp (continuous_const.add continuous_id)).continuousOn)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (Metric.mem_closedBall_self hρ.le))
  have hmaj : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (-1 : ℝ)) (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul C
  have hmeas : AEStronglyMeasurable (fun w : ℂ => D (z + w) / w)
      (volume.restrict (Metric.ball (0 : ℂ) ρ)) :=
    ((hD.measurable.comp (continuous_const.add continuous_id).measurable).div
      measurable_id).aestronglyMeasurable
  have hint : IntegrableOn (fun w : ℂ => D (z + w) / w) (Metric.ball (0 : ℂ) ρ) := by
    refine hmaj.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
    have hb : ‖D (z + w)‖ ≤ C := hC w (by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hw))
    rw [norm_div]
    calc ‖D (z + w)‖ / ‖w‖ ≤ C / ‖w‖ := by gcongr
      _ = C * ‖w‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hc : IntegrableOn (fun w : ℂ => D z / w) (Metric.ball (0 : ℂ) ρ) := by
    have h : (fun w : ℂ => D z / w) = fun w : ℂ => D z * w⁻¹ := by funext w; rw [div_eq_mul_inv]
    rw [h]; exact (integrableOn_inv_ball ρ).const_mul (D z)
  have hzero : (∫ w in Metric.ball (0 : ℂ) ρ, D z / w) = 0 := by
    have h : (fun w : ℂ => D z / w) = fun w : ℂ => D z * w⁻¹ := by funext w; rw [div_eq_mul_inv]
    rw [h, integral_const_mul, integral_inv_ball ρ, mul_zero]
  have hsplit : (∫ w in Metric.ball (0 : ℂ) ρ, (D (z + w) - D z) / w)
      = (∫ w in Metric.ball (0 : ℂ) ρ, D (z + w) / w)
        - ∫ w in Metric.ball (0 : ℂ) ρ, D z / w := by
    have h : (fun w : ℂ => (D (z + w) - D z) / w)
        = fun w : ℂ => D (z + w) / w - D z / w := by funext w; rw [sub_div]
    rw [h]
    exact integral_sub hint hc
  rw [hsplit, hzero, sub_zero]

/-- `∂̄` of a function vanishing off the disc of radius `R` vanishes off that disc. -/
lemma dbarSolution_dbarC_eq_zero_of_supportedInBall {R : ℝ} {f : ℂ → ℂ} (hfsupp : SupportedInBall R f)
    {ζ : ℂ} (hζ : R < ‖ζ‖) : dbarC f ζ = 0 := by
  have hopen : IsOpen {x : ℂ | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hf0 : f =ᶠ[nhds ζ] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hζ] with x hx
    exact hfsupp x (le_of_lt hx)
  have hderiv : fderiv ℝ f ζ = 0 := by
    have h1 : HasFDerivAt f (0 : ℂ →L[ℝ] ℂ) ζ :=
      (hasFDerivAt_const (0 : ℂ) ζ).congr_of_eventuallyEq hf0
    simpa using h1.fderiv
  simp [dbarC, hderiv]

/-- `fderiv` is invariant under translation of the argument. -/
lemma dbarSolution_fderiv_add_const {g : ℂ → ℂ} {c u : ℂ} (hg : DifferentiableAt ℝ g (c + u)) :
    fderiv ℝ (fun w : ℂ => g (c + w)) u = fderiv ℝ g (c + u) := by
  have hshift : HasFDerivAt (fun w : ℂ => c + w) (ContinuousLinearMap.id ℝ ℂ) u :=
    (hasFDerivAt_id (𝕜 := ℝ) u).const_add c
  have h := (hg.hasFDerivAt).comp u hshift
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h.fderiv

/-- `dbarC` is invariant under translation of the argument. -/
lemma dbarSolution_dbarC_add_const {g : ℂ → ℂ} {c u : ℂ} (hg : DifferentiableAt ℝ g (c + u)) :
    dbarC (fun w : ℂ => g (c + w)) u = dbarC g (c + u) := by
  unfold dbarC
  rw [dbarSolution_fderiv_add_const hg]

/-- **Pompeiu's formula with the pole at an arbitrary point**, deduced from the case of the pole
at the origin (`cauchyGreen_origin`) by translating the function: if `f` is `C¹` and supported in
the disc of radius `R/2` and `‖z‖ < R/2`, then `-(1/π) ∫_{‖ζ‖<R} (∂̄f)(ζ)/(ζ - z) = f z`. -/
lemma dbarSolution_cauchyGreen_at {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfsupp : SupportedInBall (R / 2) f) {z : ℂ} (hz : ‖z‖ < R / 2) :
    -((Real.pi : ℂ))⁻¹ * ∫ ζ in Metric.ball (0 : ℂ) R, (dbarC f ζ) / (ζ - z) = f z := by
  -- shift the pole to the origin
  let F : ℂ → ℂ := fun η => f (z + η)
  have hFcd : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1 fun η : ℂ => f (z + η)
    exact hf.comp ((contDiff_const (c := z)).add contDiff_id)
  have hFsupp : SupportedInBall R F := by
    intro η hη
    change f (z + η) = 0
    refine hfsupp (z + η) ?_
    have h1 : ‖η‖ ≤ ‖z + η‖ + ‖z‖ := by
      calc ‖η‖ = ‖(z + η) - z‖ := by congr 1; ring
        _ ≤ ‖z + η‖ + ‖z‖ := norm_sub_le _ _
    linarith [hz, h1, norm_nonneg (z + η)]
  have hgreen := cauchyGreen_origin hR hFcd hFsupp
  -- `∂̄F η = ∂̄f (z + η)`
  have hdbarF : ∀ η : ℂ, dbarC F η = dbarC f (z + η) := by
    intro η
    change dbarC (fun x : ℂ => f (z + x)) η = dbarC f (z + η)
    exact dbarSolution_dbarC_add_const ((hf.differentiable one_ne_zero).differentiableAt)
  -- the two integrals agree: both extend to the whole plane, where `η = ζ - z`
  have hkey : (∫ η in Metric.ball (0 : ℂ) R, (dbarC F η) / η)
      = ∫ ζ in Metric.ball (0 : ℂ) R, (dbarC f ζ) / (ζ - z) := by
    have h1 : ∀ η : ℂ, η ∉ Metric.ball (0 : ℂ) R → (dbarC f (z + η)) / η = 0 := by
      intro η hη
      rw [Metric.mem_ball, not_lt, dist_zero_right] at hη
      have h2 : R / 2 < ‖z + η‖ := by
        have h3 : ‖η‖ ≤ ‖z + η‖ + ‖z‖ := by
          calc ‖η‖ = ‖(z + η) - z‖ := by congr 1; ring
            _ ≤ ‖z + η‖ + ‖z‖ := norm_sub_le _ _
        linarith [hz, h3, norm_nonneg (z + η)]
      rw [dbarSolution_dbarC_eq_zero_of_supportedInBall hfsupp h2, zero_div]
    have h2 : ∀ ζ : ℂ, ζ ∉ Metric.ball (0 : ℂ) R → (dbarC f ζ) / (ζ - z) = 0 := by
      intro ζ hζ
      rw [Metric.mem_ball, not_lt, dist_zero_right] at hζ
      rw [dbarSolution_dbarC_eq_zero_of_supportedInBall hfsupp (by linarith), zero_div]
    calc (∫ η in Metric.ball (0 : ℂ) R, (dbarC F η) / η)
        = ∫ η in Metric.ball (0 : ℂ) R, (dbarC f (z + η)) / η := by
          refine setIntegral_congr_fun measurableSet_ball (fun η _ => ?_)
          rw [hdbarF η]
      _ = ∫ η : ℂ, (dbarC f (z + η)) / η :=
          setIntegral_eq_integral_of_forall_compl_eq_zero h1
      _ = ∫ η : ℂ, (fun ζ : ℂ => (dbarC f ζ) / (ζ - z)) (z + η) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
          show dbarC f (z + η) / η = dbarC f (z + η) / ((z + η) - z)
          rw [add_sub_cancel_left]
      _ = ∫ ζ : ℂ, (dbarC f ζ) / (ζ - z) :=
          integral_add_left_eq_self (fun ζ : ℂ => (dbarC f ζ) / (ζ - z)) z
      _ = ∫ ζ in Metric.ball (0 : ℂ) R, (dbarC f ζ) / (ζ - z) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h2).symm
  have hF0 : F 0 = f z := by simp [F]
  rw [hF0, hkey] at hgreen
  exact hgreen

/-- **Pompeiu's formula in the shifted form needed by the polydisc `∂̄`-equation.**  Let
`g : ℂ → ℂ` be `C¹` and supported in the closed disc of radius `ρ/2` about `c`, and let
`‖a - c‖ < ρ/2`.  Then `-(1/π) ∫_{‖w‖<ρ} (∂̄g)(a + w)/w = g a`. -/
lemma dbarSolution_dbarC_shift_pompeiu_self {ρ : ℝ} (hρ : 0 < ρ) {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    {c a : ℂ} (hsupp : ∀ w : ℂ, ρ / 2 ≤ ‖w - c‖ → g w = 0) (ha : ‖a - c‖ < ρ / 2) :
    -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ, (dbarC g (a + w)) / w = g a := by
  -- translate so that the support is centred at the origin
  let G : ℂ → ℂ := fun w => g (c + w)
  have hGdiff : ∀ y : ℂ, DifferentiableAt ℝ g (c + y) := fun y =>
    (hg.differentiable one_ne_zero).differentiableAt
  have hGcd : ContDiff ℝ 1 G := by
    change ContDiff ℝ 1 fun w : ℂ => g (c + w)
    exact hg.comp ((contDiff_const (c := c)).add contDiff_id)
  have hGsupp : SupportedInBall (ρ / 2) G := by
    intro w hw
    change g (c + w) = 0
    exact hsupp (c + w) (by simpa using hw)
  -- the integrand is the one for the centred function at the shifted pole
  have hint_eq : (∫ w in Metric.ball (0 : ℂ) ρ, (dbarC g (a + w)) / w)
      = ∫ w in Metric.ball (0 : ℂ) ρ, (dbarC G ((a - c) + w)) / w := by
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    congr 1
    change dbarC g (a + w) = dbarC (fun x : ℂ => g (c + x)) ((a - c) + w)
    rw [show a + w = c + ((a - c) + w) by ring]
    exact (dbarSolution_dbarC_add_const (hGdiff ((a - c) + w))).symm
  rw [hint_eq]
  have hDcont : Continuous (dbarC G) := by
    have h1 : Continuous (fderiv ℝ G) := hGcd.continuous_fderiv one_ne_zero
    have h2 : Continuous fun z : ℂ => fderiv ℝ G z 1 := h1.clm_apply continuous_const
    have h3 : Continuous fun z : ℂ => fderiv ℝ G z Complex.I := h1.clm_apply continuous_const
    unfold dbarC
    exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hA : ‖a - c‖ < ρ / 2 := ha
  -- subtract the value at the pole; the subtracted constant has mean zero against `1/w`
  rw [← dbarSolution_setIntegral_sub_sub_div hρ hDcont (a - c)]
  -- change of variables: `w ↦ ζ = (a - c) + w`
  rw [integral_dbarC_translate hρ hGcd hGsupp hA]
  -- Pompeiu's formula with the pole at `a - c`
  have hval : G (a - c) = g a := by
    change g (c + (a - c)) = g a
    rw [show c + (a - c) = a by ring]
  have hgreen := dbarSolution_cauchyGreen_at hρ hGcd hGsupp hA
  rwa [hval] at hgreen

/-- **Existence part of the flat `∂̄`-Poincaré result on a polydisc `P = polydisc c r
⊆ ℂⁿ`.**  Let `f = Σ_j f_j dz̄_j` be a `(0,1)`-form whose components are `C¹`, are
supported in the *open* half-size polydisc (`hsupp`), and which is *closed*
(`hclosed : IsClosedForm f`, i.e. `∂̄_k f_j = ∂̄_j f_k`).  Then on the half-size
polydisc there is a function `u` with `∂̄_j u = f_j` for all `j` (the constructed
`u` is `C¹`, indeed `u(z) = cauchyTransform (r j) (slice j (f j) z) (z j)` for any
fixed coordinate `j`).

How the construction works for `k ≠ j`: differentiating under the integral in the
parameter `z_k` gives `∂̄_k u z = T_j (∂̄_k f_j)`, the closedness rewrites this as
`T_j (∂̄_j f_k)`, and Pompeiu's formula in the `j`-th variable (valid because
`w ↦ f_k (z with z_j := w)` is compactly supported in the disc of radius `r_j/2`)
turns this into `f_k z`.  So no telescoping over coordinates is needed: the
compact support makes the one-variable Cauchy transform invert `∂̄_j` on the nose. -/
theorem exists_dbar_solution_polydisc {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hsupp : ∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0)
    (hclosed : IsClosedForm f) :
    ∃ u : (Fin n → ℂ) → ℂ,
      ∀ j, ∀ z : Fin n → ℂ, (∀ k, ‖z k - c k‖ < r k / 2) → dbarCoord j u z = f j z := by
  -- It suffices to construct the potential from a single chosen coordinate `j0`: the
  -- `j0`-th Cauchy transform inverts `∂̄` in every direction, because the data are closed and
  -- compactly supported, so no telescoping over the coordinates is needed.
  -- It suffices to construct the potential from a single chosen coordinate `j0`.
  suffices key : ∀ j0 : Fin n, ∃ u : (Fin n → ℂ) → ℂ,
      ∀ j, ∀ z : Fin n → ℂ, (∀ k, ‖z k - c k‖ < r k / 2) → dbarCoord j u z = f j z by
    exact key ⟨0, hn⟩
  intro j0
  -- The Cauchy transform of `∂̄` inverts `∂̄`, so the potential is the `j0`-th Cauchy
  -- transform of `G := -(1/π) f_{j0}` (the constant is absorbed so that no separate
  -- differentiability of the integral is needed).
  let G : (Fin n → ℂ) → ℂ := fun y => -((Real.pi : ℂ))⁻¹ * f j0 y
  have hGcd : ContDiff ℝ 1 G := by
    change ContDiff ℝ 1 fun y : Fin n → ℂ => -((Real.pi : ℂ))⁻¹ * f j0 y
    exact ContDiff.const_smul (-((Real.pi : ℂ))⁻¹) (hf j0)
  -- uniform bound for the differential of `G`
  obtain ⟨M, hM⟩ := exists_norm_fderiv_le_of_halfPolydisc_support (c := c) (r := r) hr
    (hf j0) (hsupp j0)
  have hpi : ‖-((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hMG : ∀ y : Fin n → ℂ, ‖fderiv ℝ G y‖ ≤ Real.pi⁻¹ * M := by
    intro y
    have h1 : fderiv ℝ G y = -((Real.pi : ℂ))⁻¹ • fderiv ℝ (f j0) y := by
      change fderiv ℝ (fun y : Fin n → ℂ => -((Real.pi : ℂ))⁻¹ * f j0 y) y = _
      exact fderiv_const_mul ((hf j0).differentiable one_ne_zero).differentiableAt _
    rw [h1, norm_smul, hpi]
    exact mul_le_mul_of_nonneg_left (hM y) (by positivity)
  refine ⟨fun z => ∫ w in Metric.ball (0 : ℂ) (r j0),
      G (z + Function.update (0 : Fin n → ℂ) j0 w) / w, ?_⟩
  intro k z hz
  have hρ : 0 < r j0 := hr j0
  -- differentiate the Cauchy integral in the `∂̄_k` direction
  have hdiff := dbarCoord_setIntegral_shift (ρ := r j0) hρ (j := j0) hGcd hMG k z
  rw [hdiff]
  -- the constant `-(1/π)` comes out of the integral
  have step1 : (∫ w in Metric.ball (0 : ℂ) (r j0),
        dbarCoord k G (z + Function.update (0 : Fin n → ℂ) j0 w) / w)
      = ∫ w in Metric.ball (0 : ℂ) (r j0),
          (-((Real.pi : ℂ))⁻¹ * dbarCoord k (f j0)
            (z + Function.update (0 : Fin n → ℂ) j0 w)) / w := by
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    congr 1
    change dbarCoord k (fun y : Fin n → ℂ => -((Real.pi : ℂ))⁻¹ * f j0 y)
        (z + Function.update (0 : Fin n → ℂ) j0 w)
      = -((Real.pi : ℂ))⁻¹ * dbarCoord k (f j0) (z + Function.update (0 : Fin n → ℂ) j0 w)
    exact dbarSolution_dbarCoord_const_mul k _ ((hf j0).differentiable one_ne_zero).differentiableAt
  have step2 : (∫ w in Metric.ball (0 : ℂ) (r j0),
          (-((Real.pi : ℂ))⁻¹ * dbarCoord k (f j0)
            (z + Function.update (0 : Fin n → ℂ) j0 w)) / w)
      = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) (r j0),
          dbarCoord k (f j0) (z + Function.update (0 : Fin n → ℂ) j0 w) / w := by
    rw [show (fun w : ℂ => (-((Real.pi : ℂ))⁻¹ * dbarCoord k (f j0)
            (z + Function.update (0 : Fin n → ℂ) j0 w)) / w)
        = fun w : ℂ => -((Real.pi : ℂ))⁻¹ *
            (dbarCoord k (f j0) (z + Function.update (0 : Fin n → ℂ) j0 w) / w) by
      funext w; ring]
    exact integral_const_mul _ _
  -- closedness of the form
  have step3 : (∫ w in Metric.ball (0 : ℂ) (r j0),
          dbarCoord k (f j0) (z + Function.update (0 : Fin n → ℂ) j0 w) / w)
      = ∫ w in Metric.ball (0 : ℂ) (r j0),
          dbarCoord j0 (f k) (z + Function.update (0 : Fin n → ℂ) j0 w) / w := by
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    rw [hclosed j0 k]
  -- identify the `j0`-derivative of the slice of `f k`
  have step4 : (∫ w in Metric.ball (0 : ℂ) (r j0),
          dbarCoord j0 (f k) (z + Function.update (0 : Fin n → ℂ) j0 w) / w)
      = ∫ w in Metric.ball (0 : ℂ) (r j0),
          dbarC (fun u : ℂ => f k (Function.update z j0 u)) (z j0 + w) / w := by
    refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    congr 1
    rw [← dbarSolution_update_self_add j0 z w]
    exact (dbarSolution_dbarC_update_eq_dbarCoord j0
      (hg := (hf k).differentiable one_ne_zero |>.differentiableAt)).symm
  -- Pompeiu's formula in the `j0`-th variable
  have hchild := dbarSolution_dbarC_shift_pompeiu_self (ρ := r j0) hρ
    (g := fun u : ℂ => f k (Function.update z j0 u)) (dbarSolution_contDiff_update j0 z (hf k))
    (dbarSolution_slice_zero hsupp k j0 z) (by simpa using hz j0)
  rw [show Function.update z j0 (z j0) = z from Function.update_eq_self j0 z] at hchild
  exact step1.trans (step2.trans ((congrArg (fun t => -((Real.pi : ℂ))⁻¹ * t) step3).trans
    ((congrArg (fun t => -((Real.pi : ℂ))⁻¹ * t) step4).trans hchild)))

end Work.CR.Flat.Cauchy
