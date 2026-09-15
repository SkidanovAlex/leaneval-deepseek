import Submission.FUP.HormanderExist
import Submission.FUP.DbarClosed
import Submission.FUP.Weyl
import Submission.FUP.LpNorms
import Submission.Commons.MeasureTheory.volume_absolutelyContinuous_withDensity_ofReal_pos
import Submission.Commons.MeasureTheory.integrableOn_volume_of_memLp_withDensity_exp_neg
import Submission.Commons.MeasureTheory.LocallyIntegrable.of_memLp_withDensity_exp_neg

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Hörmander's `∂̄` theorem for smooth weights and exact data

This module closes gap (G) of the Hörmander project: for a **smooth** (`C^∞`) weight `φ` whose
Hermitian Hessian dominates `κ` pointwise (`HessBound φ κ`), and for data of the special form
`η = ∂̄h` with `h` smooth and compactly supported, Hörmander's equation `∂̄g = η` has a solution `g`
which is `C^∞`, solves the equation *pointwise*, and satisfies the weighted `L²` estimate
`∫|g|²e^{-φ} ≤ ∫|η|²e^{-φ}/κ`.

The proof is

* the `L²` existence theorem `Submission.FUP.exists_L2_solution_of_dbar` (Friedrichs), giving
  `u ∈ L²(μ_φ)` with `DbarWeak φ u (∂̄h)` and `‖u‖² ≤ etaKapNorm (∂̄h) φ κ`;
* subtract the smooth function `h`: `DbarWeak φ (u - h) 0`;
* **Weyl's lemma** (`Submission.FUP.weyl_dbar_wt`): `u - h` agrees `μ_φ`-a.e. with a holomorphic
  `H`;
* then `g := H + h` is smooth, `∂̄g = ∂̄h` pointwise, and `g = u` a.e., so the estimate transfers.

The remaining gap for the full distributional statement `HormanderStatement` is the passage from a
merely plurisubharmonic weight to the smooth one (gap (H)); see `Submission/FUP/ROADMAP.md`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- `volume` is absolutely continuous with respect to `μ_φ = e^{-φ}dvol`. -/
lemma volume_absolutelyContinuous_wtMeasure {φ : FormDu d → ℝ} (hφ : Continuous φ) :
    (volume : Measure (FormDu d)) ≪ wtMeasure φ := by
  change (volume : Measure (FormDu d)) ≪
    (volume : Measure (FormDu d)).withDensity (fun z => ENNReal.ofReal (Real.exp (-(φ z))))
  exact Commons.MeasureTheory.volume_absolutelyContinuous_withDensity_ofReal_pos
    (Real.continuous_exp.comp hφ.neg) (fun z => Real.exp_pos _)

/-- A function in `L²(μ_φ)` (with `φ` continuous) is a.e. strongly measurable for `volume`. -/
lemma aestronglyMeasurable_volume_of_memLp {φ : FormDu d → ℝ} (hφ : Continuous φ)
    {E : Type*} [NormedAddCommGroup E] {F : FormDu d → E} (hF : MemLp F 2 (wtMeasure φ)) :
    AEStronglyMeasurable F (volume : Measure (FormDu d)) :=
  hF.aestronglyMeasurable.mono_ac (volume_absolutelyContinuous_wtMeasure hφ)

/-- **Local integrability of an `L²(μ_φ)`-element.**  A function in `L²(μ_φ)`, `φ` continuous, is
locally integrable for `volume`, and so is the square of its norm. -/
theorem locallyIntegrable_of_memLp_wtMeasure {φ : FormDu d → ℝ} (hφ : Continuous φ)
    {F : FormDu d → ℂ} (hF : MemLp F 2 (wtMeasure φ)) :
    LocallyIntegrable F (volume : Measure (FormDu d)) ∧
      LocallyIntegrable (fun z => ‖F z‖ ^ 2) (volume : Measure (FormDu d)) := by
  have hF' : MemLp F 2 ((volume : Measure (FormDu d)).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-(φ z))))) := hF
  have haesm : AEStronglyMeasurable F (volume : Measure (FormDu d)) :=
    aestronglyMeasurable_volume_of_memLp hφ hF
  constructor
  · rw [locallyIntegrable_iff]
    exact fun K hK =>
      Commons.MeasureTheory.integrableOn_volume_of_memLp_withDensity_exp_neg hφ hF' hK
  · rw [locallyIntegrable_iff]
    intro K hK
    have hmem := Commons.MeasureTheory.LocallyIntegrable.memLp_restrict_of_memLp_withDensity_exp_neg
      hφ hF' hK
    exact (memLp_two_iff_integrable_sq_norm (haesm.mono_measure Measure.restrict_le_self)).mp hmem

/-- A holomorphic function on `ℂᵈ` is `C^∞` over `ℝ`. -/
theorem contDiff_of_differentiable_complex {H : FormDu d → ℂ} (hH : Differentiable ℂ H) :
    ContDiff ℝ ∞ H := by
  have h1 : AnalyticOnNhd ℂ H Set.univ :=
    Commons.Analysis.Complex.analyticOnNhd_of_dbar_eq_zero (d := d) isOpen_univ
      (hH.restrictScalars ℝ).differentiableOn
      (fun j z _ => by
        have hz := congrFun (partialZbar_eq_zero_of_differentiable_complex hH j) z
        rw [partialZbar] at hz
        rcases div_eq_zero_iff.mp hz with h | h
        · exact h
        · exact absurd h (by norm_num))
  exact (h1.contDiff).restrict_scalars ℝ

/-- **The `L²(μ_φ)`-norm as a weighted `lintegral` of `ofReal`s.** -/
theorem lintegral_norm_sq_wtMeasure {φ : FormDu d → ℝ} (hφ : Continuous φ)
    {F : FormDu d → ℂ} (hF : MemLp F 2 (wtMeasure φ)) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(φ z)))
      = ENNReal.ofReal (‖hF.toLp F‖ ^ 2) := by
  have hFnn : ∀ z, 0 ≤ ‖F z‖ ^ 2 * Real.exp (-(φ z)) := fun z => by positivity
  have hmeas : AEStronglyMeasurable (fun z => ‖F z‖ ^ 2 * Real.exp (-(φ z)))
      (volume : Measure (FormDu d)) :=
    ((aestronglyMeasurable_volume_of_memLp hφ hF).norm.pow 2).mul
      (Real.continuous_exp.comp hφ.neg).aestronglyMeasurable
  -- finiteness of the `μ_φ`-integral of `‖F‖²`
  have hIntμ : Integrable (fun z => ‖F z‖ ^ 2) (wtMeasure φ) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have h3 : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂(wtMeasure φ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)).mp
      hIntμ.hasFiniteIntegral
  -- the same, against `volume`
  have h5 : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(φ z)))
      ∂(volume : Measure (FormDu d)) < ⊤ := by
    have h := h3
    rw [lintegral_wtMeasure hφ (fun z => ENNReal.ofReal (‖F z‖ ^ 2))] at h
    refine lt_of_eq_of_lt ?_ h
    refine lintegral_congr fun z => ?_
    rw [wtDensity_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]
  have hInt : Integrable (fun z => ‖F z‖ ^ 2 * Real.exp (-(φ z)))
      (volume : Measure (FormDu d)) :=
    integrable_of_lintegral_ofReal_lt_top hmeas hFnn h5
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hFnn)]
  congr 1
  rw [norm_sq_toLp F hF, integral_wtMeasure hφ]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show ‖F z‖ ^ 2 * Real.exp (-(φ z)) = Real.exp (-(φ z)) • ‖F z‖ ^ 2
  rw [smul_eq_mul]
  ring

/-- `formNormSq η` is nonnegative. -/
lemma formNormSq_nonneg (η : FormDu d → (Fin d → ℂ)) (z : FormDu d) :
    0 ≤ formNormSq η z := by
  rw [formNormSq]
  exact Finset.sum_nonneg fun j _ => by positivity

/-- **Hörmander's `∂̄`-theorem for smooth weights and exact data.**

If `φ` is `C^∞` with `HessBound φ κ` (`κ` continuous and positive), and `h` is smooth and compactly
supported, then `∂̄g = ∂̄h` has a `C^∞` solution satisfying the equation *pointwise* and the
weighted `L²` estimate with the sharp constant. -/
theorem exists_smooth_solution_of_dbar_exact {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hd : 1 ≤ d)
    {κ : FormDu d → ℝ} (hκc : Continuous κ) (hκpos : ∀ z, 0 < κ z) (hhess : HessBound φ κ)
    {h : FormDu d → ℂ} (hh : ContDiff ℝ ∞ h) (hhs : HasCompactSupport h)
    (hint : ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z) < ⊤) :
    ∃ g : FormDu d → ℂ, ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun h z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(φ z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z)) := by
  have hφc : Continuous φ := hφ.continuous
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the smoothness and support of the data `η = ∂̄h`
  have hη1 : ∀ j, ContDiff ℝ ∞ (fun z => dbarFun h z j) := fun j =>
    (contDiff_pi.mp (contDiff_dbarFun hh)) j
  have hηc : ∀ j, Continuous (fun z => dbarFun h z j) := fun j => (hη1 j).continuous
  have hηs : ∀ j, HasCompactSupport (fun z => dbarFun h z j) := fun j =>
    hhs.mono' (fun z hz => by
      by_contra hzc
      have hd0 : fderiv ℝ h z = 0 := (HasFDerivAt.of_notMem_tsupport ℝ hzc).fderiv
      exact hz (by simp [dbarFun, partialZbar, hd0]))
  have hηm : MemLp (liftForm (dbarFun h)) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc (contDiff_liftForm hη1)
      (hasCompactSupport_liftForm (hasCompactSupport_pi hηs))
  have hηclosed : DbarClosed (dbarFun h) :=
    dbarClosed_dbarFun (hh.of_le (WithTop.coe_le_coe.mpr le_top))
  have hv0 : DbarWeak2 φ (hηm.toLp (liftForm (dbarFun h))) 0 :=
    dbarWeak2_of_dbarClosed hφ1 hη1 hηm hηclosed
  -- the `L²` existence theorem
  obtain ⟨u, hu, hub⟩ :=
    exists_L2_solution_of_dbar hφ hd hκc hκpos hηc hint hηm hhess hv0
  -- the smooth relation for `h`
  have hhm : MemLp h 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc hh hhs
  have hwm : MemLp (dbarFormFun h) 2 (wtMeasure φ) := hηm
  have huh : DbarWeak φ (hhm.toLp h) (hηm.toLp (liftForm (dbarFun h))) := by
    have h' := dbarWeak_smooth (φ := φ) hφ1 hh hhs hhm hwm
    rwa [show hwm.toLp (dbarFormFun h) = hηm.toLp (liftForm (dbarFun h)) from
      MemLp.toLp_congr hwm hηm (Eventually.of_forall fun z => rfl)] at h'
  have hsub : DbarWeak φ (u - hhm.toLp h) 0 := by
    have h' := DbarWeak.sub hu huh
    simpa using h'
  -- Weyl's lemma
  set uLp : Lp ℂ 2 (wtMeasure φ) := u - hhm.toLp h with huLp
  have hsub' : DbarWeak φ uLp 0 := by rw [huLp]; exact hsub
  have hFm : MemLp (↑↑uLp : FormDu d → ℂ) 2 (wtMeasure φ) := Lp.memLp uLp
  have hFweak : DbarWeak φ (hFm.toLp (↑↑uLp)) 0 := by
    rw [Lp.toLp_coeFn uLp hFm]; exact hsub'
  obtain ⟨hF1, hF2⟩ := locallyIntegrable_of_memLp_wtMeasure hφc hFm
  obtain ⟨H, hHd, hHeq⟩ := weyl_dbar_wt hφ hFm hF1 hF2 hFweak
  -- the solution `g = H + h`
  refine ⟨fun z => H z + h z, ?_, ?_, ?_⟩
  · exact (contDiff_of_differentiable_complex hHd).add hh
  · intro j
    funext z
    have h1 : partialZbar j (fun z => H z + h z) z
        = partialZbar j H z + partialZbar j h z :=
      partialZbar_add j (hHd.differentiableAt.restrictScalars ℝ)
        (hh.differentiable (by simp)).differentiableAt
    rw [h1, congrFun (partialZbar_eq_zero_of_differentiable_complex hHd j) z]
    simp only [Pi.zero_apply, zero_add]
    rfl
  · -- the estimate: `g = u` a.e.
    have hcoe : (↑↑uLp : FormDu d → ℂ) =ᵐ[wtMeasure φ] fun z => (↑↑u : FormDu d → ℂ) z - h z := by
      have h1 : (↑↑uLp : FormDu d → ℂ) =ᵐ[wtMeasure φ]
          (↑↑(u - hhm.toLp h) : FormDu d → ℂ) := by
        rw [huLp]
      filter_upwards [h1, Lp.coeFn_sub u (hhm.toLp h), hhm.coeFn_toLp] with z h1z h2z h3z
      rw [← h1z, h2z]
      simp only [Pi.sub_apply]
      rw [h3z]
    have hae : (fun z => H z + h z) =ᵐ[wtMeasure φ] (↑↑u : FormDu d → ℂ) := by
      filter_upwards [hHeq, hcoe] with z hz1 hz2
      rw [← hz1, hz2]; ring
    have hLHS : ∫⁻ z, ENNReal.ofReal (‖H z + h z‖ ^ 2 * Real.exp (-(φ z)))
        = ENNReal.ofReal (‖u‖ ^ 2) := by
      have hae' : (fun z => H z + h z) =ᵐ[(volume : Measure (FormDu d))]
          (↑↑u : FormDu d → ℂ) := ae_volume_of_ae_wtMeasure hφc hae
      have hcongr : (fun z => ENNReal.ofReal (‖H z + h z‖ ^ 2 * Real.exp (-(φ z))))
          =ᵐ[(volume : Measure (FormDu d))]
          (fun z => ENNReal.ofReal (‖(↑↑u : FormDu d → ℂ) z‖ ^ 2 * Real.exp (-(φ z)))) := by
        filter_upwards [hae'] with z hz
        rw [show H z + h z = (↑↑u : FormDu d → ℂ) z from hz]
      rw [lintegral_congr_ae hcongr, lintegral_norm_sq_wtMeasure hφc (Lp.memLp u), Lp.toLp_coeFn]
    have hRHS : ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z)
        = ENNReal.ofReal (etaKapNorm (dbarFun h) φ κ) := by
      have hcont : Continuous
          (fun z => formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z) :=
        (continuous_formNormSq (continuous_pi hηc)).mul
          (Real.continuous_exp.comp hφc.neg) |>.div hκc (fun z => (hκpos z).ne')
      have hnn : ∀ z, 0 ≤ formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z := fun z =>
        div_nonneg (mul_nonneg (formNormSq_nonneg _ z) (Real.exp_nonneg _)) (hκpos z).le
      have hInt : Integrable (fun z => formNormSq (dbarFun h) z * Real.exp (-(φ z)) / κ z)
          (volume : Measure (FormDu d)) :=
        integrable_of_lintegral_ofReal_lt_top hcont.aestronglyMeasurable hnn hint
      rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hnn), etaKapNorm]
    rw [hLHS, hRHS]
    exact ENNReal.ofReal_le_ofReal hub

end Submission.FUP
