import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.EL12z_Kd
import Submission.Work.Coercivity.EL12z_weight
import Submission.Work.Coercivity.C0_sq_le4
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Integrals over `Iz = [0,∞)` and `(0,∞)` agree (the two sets differ by `{0}`). -/
theorem setIntegral_Iz_eq_Ioi (g : ℝ → ℝ) :
    ∫ z in Work.Spaces.Iz, g z = ∫ z in Set.Ioi (0 : ℝ), g z := by
  show (∫ z in Set.Ici (0 : ℝ), g z) = ∫ z in Set.Ioi (0 : ℝ), g z
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm

/-- Integrability over `Iz = [0,∞)` and over `(0,∞)` agree. -/
theorem integrableOn_Iz_iff_Ioi (g : ℝ → ℝ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iz
      ↔ MeasureTheory.IntegrableOn g (Set.Ioi (0 : ℝ)) := by
  have h : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    show MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)) = _
    exact (Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  rw [MeasureTheory.IntegrableOn, MeasureTheory.IntegrableOn, h]


/-- The angular slice of a `SmoothQuad` function is a.e. strongly measurable (it is continuous
on the open interval, which is connull in `Iθ`). -/
theorem aesm_slice_theta_Q {g : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad g) {s : ℝ}
    (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hz : s ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hcont : ContinuousOn (fun θ => g s θ) (Set.Ioo 0 (π / 2)) :=
    (hsq.curry_θ hz).continuousOn
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have h2 : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))
  rwa [h2] at h1

/-- The angular slice of `D_θ` of a `SmoothQuad` function is a.e. strongly measurable. -/
theorem aesm_slice_Dth_Q {g : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad g) {s : ℝ}
    (hs : 0 < s) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hz : s ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hIoo : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth g)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_pth hIoo hsq
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.pth g s θ)
      (Set.Ioo 0 (π / 2)) := Work.FTS.LocData.contDiffOn_slice_θ hpth hz
  have hcont : ContinuousOn (fun θ => Work.Spaces.Dth g s θ) (Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    exact h1.mul hslice.continuousOn
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth g s θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have h2 : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))
  rwa [h2] at h1

/-- A.e. in `z`, the angular slice `θ ↦ f z θ` of a function of the interior class is
integrable. -/
theorem ae_integrableOn_slice_f (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ := by
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  have hP0 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hp.sqDzEta 0 (by norm_num)
  filter_upwards [hP0.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_theta_Q hsq hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
      Work.FTS.CoercivityFix.Coer1.one_le_sig_eta hθ
    nlinarith [sq_nonneg (f s θ)]
  have h4 : MeasureTheory.Integrable (fun θ => (1 : ℝ) / 2 + (1 / 2) * f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_theta_Q hsq hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]

/-- A.e. in `z`, the angular slice `θ ↦ D_θ f z θ` of a function of the interior class is
integrable. -/
theorem ae_integrableOn_slice_Dth (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ := by
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  have hP2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dth f p.1 p.2 ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        (Work.Spaces.gam α) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    refine (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ici.prod measurableSet_Icc)] with p hp'
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  filter_upwards [hP2.prod_right_ae, Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos]
    with s hs hspos
  have hRho : (fun θ => Work.Spaces.Dth f s θ ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) s θ)
      = fun θ => Work.Spaces.w s ^ 2
          * (Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
              (Work.Spaces.gam α) θ) := by
    funext θ
    simp only [Work.FTS.CoercivityFix.Coer1.Rho]
    ring
  rw [hRho] at hs
  have hwpos : (0 : ℝ) < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hwne : Work.Spaces.w s ^ 2 ≠ 0 := by positivity
  have hs2 : MeasureTheory.Integrable
      (fun θ => Work.Spaces.Dth f s θ ^ 2 * Work.FTS.CoercivityFix.Coer1.sig
        (Work.Spaces.gam α) θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hwne) _).mp hs
  have hs3 : MeasureTheory.Integrable (fun θ => Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hs2
      ((aesm_slice_Dth_Q hsq hspos).pow 2) ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hγ : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsin0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hs1 : 1 ≤ Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ := by
      have h1 := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
        (show -(Work.Spaces.gam α) ≤ -(0 : ℝ) by linarith [hγ])
      rw [neg_zero, Real.rpow_zero] at h1
      simpa only [Work.FTS.CoercivityFix.Coer1.sig] using h1
    nlinarith [sq_nonneg (Work.Spaces.Dth f s θ)]
  have h4 : MeasureTheory.Integrable
      (fun θ => (1 : ℝ) / 2 + (1 / 2) * Work.Spaces.Dth f s θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_const _).add (hs3.const_mul (1 / 2))
  refine h4.mono' (aesm_slice_Dth_Q hsq hspos) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|Work.Spaces.Dth f s θ| - 1), sq_abs (Work.Spaces.Dth f s θ)]

/-! ## The endpoint vanishing of the profile and the angular integration by parts -/

/-- **`f` vanishes at the two angular endpoints**, for every `z > 0`, as a consequence of
`BdryTraces` (the `a + b = 0` slot: `sin(2θ)^{1-γ}f(z,θ)² → 0`). -/
theorem tendsto_slice_zero_bdry (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hbd : Work.FTS.Nonlin.BdryTraces α 5 f) {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun θ => f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Filter.Tendsto (fun θ => f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hbd' := (hbd 0 0 (by norm_num)).2 s hs
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  constructor
  · -- `θ → 0⁺`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := hbd'.1
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[>] (0 : ℝ), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpi2)]
        with θ hθ hθ2
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero
  · -- `θ → (π/2)⁻`
    have hsq : Filter.Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * f s θ ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := hbd'.2
    have hg : Filter.Tendsto (fun θ =>
        Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
        (𝓝[<] (π / 2)) (𝓝 0) := by
      have hcomp : Filter.Tendsto (fun θ =>
          Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2))
          (𝓝[<] (π / 2)) (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp hsq
      rw [Real.sqrt_zero] at hcomp
      exact hcomp
    have hle : ∀ᶠ θ in 𝓝[<] (π / 2), |f s θ|
        ≤ Real.sqrt (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * f s θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hpi2)]
        with θ hθ2 hθ
      have hθ' : (0 : ℝ) < θ := hθ
      have hθ2' : θ < π / 2 := hθ2
      have hsin0 : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; positivity
      have h1 : (1 : ℝ) ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hsin0 hsin1
          (show (1 : ℝ) - Work.Spaces.gam α ≤ (0 : ℝ) by
            rw [Work.Spaces.gam]; linarith)
        rw [Real.rpow_zero] at h
        exact h
      rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
      rw [sq_abs]
      nlinarith [sq_nonneg (f s θ)]
    have hzero : Filter.Tendsto (fun θ => |f s θ|) (𝓝[<] (π / 2)) (𝓝 0) :=
      squeeze_zero' (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hle hg
    exact (tendsto_zero_iff_abs_tendsto_zero (fun θ => f s θ)).mpr hzero

/-- **The angular integration by parts in the interior class**:
`∫_{Iθ} C0h(θ)∂_θf(z,θ) = -∫_{Iθ} C0g(θ)f(z,θ)` for `z > 0`, where `C0h = 3K sin(2θ)` is the
angular factor of the density of `L₁₂(Transport f)` and `C0g = C0h'`.  The boundary terms
`C0h(0) = C0h(π/2) = 0` vanish, and the two limits of `C0h·f` at the endpoints are `0` by
`BdryTraces`. -/
theorem C0thetaIBP_Q (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hbd : Work.FTS.Nonlin.BdryTraces α 5 f)
    {s : ℝ} (hs : 0 < s)
    (hfI : MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ)
    (hDI : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ) :
    ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ
      = -∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ := by
  have hpi2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hpi2pos : (0 : ℝ) < π / 2 := by positivity
  -- the endpoint limits of `f`
  obtain ⟨hf0, hf2⟩ := tendsto_slice_zero_bdry α hα hbd hs
  -- the primitive and its derivative on the open interval
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun θ' => Work.Coercivity.C0h θ' * f s θ')
        (Work.Coercivity.C0g θ * f s θ
          + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun θ' => f s θ') (Work.Spaces.pth f s θ) θ :=
      (Work.FTS.CoercivityFix.Coer1.differentiableAt_slice_theta_Q hsq hs hθ).hasDerivAt
    exact (Work.Coercivity.C0h_hasDerivAt θ).mul h1
  -- integrability of the two summands of the derivative
  have hC0h_cont : Continuous Work.Coercivity.C0h := by
    unfold Work.Coercivity.C0h Work.Spaces.K
    fun_prop
  have hC0g_cont : Continuous Work.Coercivity.C0g := by
    unfold Work.Coercivity.C0g
    fun_prop
  have hK_cont : Continuous (fun θ : ℝ => 3 * Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  have hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0g θ * f s θ)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.continuousOn_mul hC0g_cont.continuousOn hfI isCompact_Icc
  have hI2 : MeasureTheory.IntegrableOn (fun θ => Work.Coercivity.C0h θ * Work.Spaces.pth f s θ)
      Work.Spaces.Iθ := by
    refine (MeasureTheory.IntegrableOn.continuousOn_mul hK_cont.continuousOn hDI
      isCompact_Icc).congr_fun ?_ measurableSet_Icc
    intro θ _
    simp only [Work.Coercivity.C0h, Work.Spaces.Dth, Work.Spaces.K]
    ring
  have hderiv_int : IntervalIntegrable (fun θ => Work.Coercivity.C0g θ * f s θ
      + Work.Coercivity.C0h θ * Work.Spaces.pth f s θ) MeasureTheory.volume 0 (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
      ((hI1.mono_set Set.Ioc_subset_Icc_self).add (hI2.mono_set Set.Ioc_subset_Icc_self))
  -- the limits of the primitive
  have hlim0 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[>] (0 : ℝ)) (𝓝 (Work.Coercivity.C0h 0)) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.1] at h1
    simpa using h1.mul hf0
  have hlim2 : Filter.Tendsto (fun θ => Work.Coercivity.C0h θ * f s θ) (𝓝[<] (π / 2)) (𝓝 0) := by
    have h1 : Filter.Tendsto Work.Coercivity.C0h (𝓝[<] (π / 2))
        (𝓝 (Work.Coercivity.C0h (π / 2))) :=
      hC0h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [Work.Coercivity.C0h_zero.2] at h1
    simpa using h1.mul hf2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := 0) (b := π / 2)
    hpi2pos hderiv hderiv_int hlim0 hlim2
  -- split and convert to set integrals over `Iθ`
  have hsplit : (∫ y in (0 : ℝ)..(π / 2), (Work.Coercivity.C0g y * f s y
        + Work.Coercivity.C0h y * Work.Spaces.pth f s y))
      = (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
        + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) :=
    intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI1.mono_set Set.Ioc_subset_Icc_self))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpi2).mpr
        (hI2.mono_set Set.Ioc_subset_Icc_self))
  have hzero : (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y)
      + (∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y) = 0 := by
    rw [← hsplit]
    simpa using hFTC
  have hg_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0g y * f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0g y * f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  have hh_eq : (∫ y in Work.Spaces.Iθ, Work.Coercivity.C0h y * Work.Spaces.pth f s y)
      = ∫ y in (0 : ℝ)..(π / 2), Work.Coercivity.C0h y * Work.Spaces.pth f s y := by
    rw [Work.Spaces.Iθ]
    exact ((intervalIntegral.integral_of_le hpi2).trans
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume)))).symm
  rw [hg_eq, hh_eq]
  linarith [hzero]


/-! ## The bound `(C₀ f)² ≤ 64 Ef f` in the interior class -/

/-- `(L₁₂(Transport f)(0))² ≤ 64 |f w|²_{L²}` in the interior class `CoerAdm`.

The paper's proof of `(C₀f)² ≤ Ef·(C0Ih·C0D)`: `C₀ f = ∫_0^∞ L₁₂dens(Transport f)(s)ds`, the
density factors as `(1/(s(1+s)))∫_θ C0h(θ)∂_θf(s,θ)dθ`, the angular integration by parts
`∫_θ C0h·∂_θf = -∫_θ C0g·f` (`C0thetaIBP_Q`) turns this into the double integral
`C₀ f = -∫∫ C0g(θ)f(s,θ)/(s(1+s))`, and Cauchy–Schwarz for the two `L²`-functions
`A = f·w` and `B = C0g(θ)/(s(1+s)w(s))` gives the bound, with
`∫B² = C0Ih·C0D ≤ 729/16 = 45.57`. -/
theorem C0_sq_le_Ef_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Coercivity.Ef f := by
  have hα1' : α ≤ 1 := by linarith
  have hreg : Work.FTS.Nonlin.RegQ α 5 f := hf.reg
  have hsq : Work.FTS.LocData.SmoothQuad f := hreg.1
  have hbd : Work.FTS.Nonlin.BdryTraces α 5 f := hreg.2.2
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hreg (by norm_num)
  -- ## the measure, the two test functions and the auxiliary `H`
  set μ : Measure (ℝ × ℝ) := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hμdef
  set J : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ with hJdef
  set A : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1 with hAdef
  set B : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.C0g p.2 * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) with hBdef
  set H : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.C0g p.2 * f p.1 p.2 / (p.1 * (1 + p.1)) with hHdef
  have hJmeas : MeasurableSet J := by
    rw [hJdef]; exact measurableSet_Ioi.prod measurableSet_Icc
  have hμJ : μ = (MeasureTheory.volume.prod MeasureTheory.volume).restrict J := by
    rw [hμdef, hJdef]
    have h1 : MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
      (Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [h1, Measure.prod_restrict]
  have hmemJ : ∀ᵐ p ∂μ, p ∈ J := by
    rw [hμJ]; exact MeasureTheory.ae_restrict_mem hJmeas
  -- ## a.e. strong measurability
  have hC0g_cont : Continuous Work.Coercivity.C0g := by
    unfold Work.Coercivity.C0g
    fun_prop
  have hf_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2) μ :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.CoercivityFix.Coer1.continuousOn_f_Q hsq)
  have hw_aesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) μ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ Work.Coercivity.continuousOn_w_quad
  have hA_aesm : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hAdef]; exact hf_aesm.mul hw_aesm
  have hrat_meas : Measurable (fun p : ℝ × ℝ => 1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) := by
    unfold Work.Spaces.w
    fun_prop
  have hB_aesm : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hBdef]
    exact ((hC0g_cont.measurable.comp measurable_snd).mul hrat_meas).aestronglyMeasurable
  have hH_aesm : MeasureTheory.AEStronglyMeasurable H μ := by
    rw [hHdef]
    have h1 : AEMeasurable (fun p : ℝ × ℝ => Work.Coercivity.C0g p.2 * f p.1 p.2) μ :=
      ((hC0g_cont.measurable.comp measurable_snd).aestronglyMeasurable.mul hf_aesm).aemeasurable
    have h2 : AEMeasurable (fun p : ℝ × ℝ => p.1 * (1 + p.1)) μ :=
      (measurable_fst.mul (measurable_const.add measurable_fst)).aemeasurable
    exact (h1.div h2).aestronglyMeasurable
  -- ## integrability of `A²`, `B²` and `H`
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf2
    refine (hp.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  have hA2int : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p ^ 2) μ := by
    rw [hAdef, hμdef, Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hfw
  have hInvSq : MeasureTheory.IntegrableOn
      (fun s : ℝ => (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2) Work.Spaces.Iz := by
    refine (Work.Coercivity.integrable_Iz_zsq_div_six).congr
      (Filter.Eventually.of_forall (fun s => ?_))
    rcases eq_or_ne s 0 with rfl | hs
    · norm_num [Work.Spaces.w]
    · unfold Work.Spaces.w
      field_simp
  have hC0g2_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Coercivity.C0g θ) ^ 2) Work.Spaces.Iθ :=
    (hC0g_cont.pow 2).continuousOn.integrableOn_Icc
  have hB2int : MeasureTheory.Integrable (fun p : ℝ × ℝ => B p ^ 2) μ := by
    rw [hBdef, hμdef]
    have h1 : (fun p : ℝ × ℝ => (Work.Coercivity.C0g p.2
          * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) ^ 2)
        = fun p : ℝ × ℝ =>
          (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) ^ 2 * (Work.Coercivity.C0g p.2) ^ 2 := by
      funext p; rw [mul_pow]; ring
    rw [h1]
    exact hInvSq.mul_prod hC0g2_int
  have hHdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (1 / 2) * (A p ^ 2 + B p ^ 2)) μ :=
    (hA2int.add hB2int).const_mul (1 / 2)
  have hHint : MeasureTheory.Integrable H μ := by
    refine MeasureTheory.Integrable.mono' hHdom hH_aesm ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwpos : 0 < Work.Spaces.w p.1 := by rw [Work.Spaces.w]; positivity
    have hden : 0 < p.1 * (1 + p.1) := by positivity
    have hAeq : A p ^ 2 = (|f p.1 p.2| * Work.Spaces.w p.1) ^ 2 := by
      rw [hAdef, mul_pow, mul_pow, sq_abs]
    have hBeq : B p ^ 2
        = (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) ^ 2 := by
      rw [hBdef, mul_pow, mul_pow, sq_abs]
    have hHeq : ‖H p‖ = (|f p.1 p.2| * Work.Spaces.w p.1)
        * (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1))) := by
      simp only [hHdef]
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden]
      have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
      have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
      have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
      have hwne : Work.Spaces.w p.1 ≠ 0 := ne_of_gt hwpos
      field_simp
    rw [hHeq, hAeq, hBeq]
    nlinarith [two_mul_le_add_sq (|f p.1 p.2| * Work.Spaces.w p.1)
      (|Work.Coercivity.C0g p.2| * (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)))]
  -- ## Fubini and the identification with the double integral
  have hH_fub : (∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H (s, θ)) = ∫ p, H p ∂μ := by
    have hint := hHint
    rw [hμdef] at hint ⊢
    exact (MeasureTheory.integral_prod H hint).symm
  have hX : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Coercivity.C0g θ * f s θ / (s * (1 + s)))
      = ∫ p, A p * B p ∂μ := by
    have hfill : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Coercivity.C0g θ * f s θ / (s * (1 + s)))
        = ∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, H (s, θ) := by
      rw [hHdef]
      exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
    rw [hfill, hH_fub]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hmemJ] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hwne : Work.Spaces.w p.1 ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hp1ne : p.1 ≠ 0 := ne_of_gt hp1
    have h1p1 : (0 : ℝ) < 1 + p.1 := by linarith
    have h1p1ne : (1 : ℝ) + p.1 ≠ 0 := ne_of_gt h1p1
    rw [hHdef, hAdef, hBdef]
    field_simp
  -- ## the two `L²` norms
  have hA2eq : ∫ p, A p ^ 2 ∂μ = Work.Coercivity.Ef f := by
    have hint := hA2int
    rw [hAdef] at hint ⊢
    rw [hμdef] at hint ⊢
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) hint]
    rfl
  have hB2eq : ∫ p, B p ^ 2 ∂μ = Work.Coercivity.C0Ih * Work.Coercivity.C0D := by
    have h1 : (fun p : ℝ × ℝ => B p ^ 2)
        = fun p : ℝ × ℝ =>
          (1 / (p.1 * (1 + p.1) * Work.Spaces.w p.1)) ^ 2 * (Work.Coercivity.C0g p.2) ^ 2 := by
      funext p; rw [hBdef, mul_pow]; ring
    rw [h1, hμdef]
    rw [MeasureTheory.integral_prod_mul
      (f := fun s : ℝ => (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2)
      (g := fun θ : ℝ => (Work.Coercivity.C0g θ) ^ 2)]
    have hC0D' : (∫ s in Work.Spaces.Iz, (1 / (s * (1 + s) * Work.Spaces.w s)) ^ 2)
        = Work.Coercivity.C0D :=
      (MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))).symm
    rw [show Work.Coercivity.C0Ih = ∫ θ in Work.Spaces.Iθ, (Work.Coercivity.C0g θ) ^ 2 from rfl,
      hC0D']
    ring
  have hnum : Work.Coercivity.C0Ih * Work.Coercivity.C0D ≤ 64 := by
    have h1 : Work.Coercivity.C0Ih ≤ 729 := Work.Coercivity.C0Ih_le
    have h2 : Work.Coercivity.C0D ≤ 1 / 16 := Work.Coercivity.C0D_le
    have h3 : 0 ≤ Work.Coercivity.C0Ih := by
      rw [Work.Coercivity.C0Ih]; exact integral_nonneg (fun θ => sq_nonneg _)
    have h4 : 0 ≤ Work.Coercivity.C0D := by
      rw [Work.Coercivity.C0D]; exact integral_nonneg (fun s => sq_nonneg _)
    nlinarith [h1, h2, h3, h4]
  have hEf : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## the identity `C₀ f = -∫∫ C0g(θ)f/(s(1+s))`
  have hC0 : Work.Coercivity.C0 f
      = -∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Coercivity.C0g θ * f s θ / (s * (1 + s)) := by
    have step1 : Work.Coercivity.C0 f
        = ∫ s in Set.Ioi (0 : ℝ),
            Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) s := by
      rw [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12]
    rw [step1]
    have step2 : (∫ s in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) s)
        = ∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
            * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      have hs'0 : (0 : ℝ) < s := hs'
      have hs0 : s ≠ 0 := ne_of_gt hs'0
      have hs1 : (1 : ℝ) + s ≠ 0 := ne_of_gt (by linarith)
      rw [Work.FM.L12dens]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Work.Coercivity.Transport, Work.Spaces.Dth, Work.Coercivity.C0h, Work.Spaces.K]
      field_simp
    rw [step2]
    have step3 : (∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
          * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0h θ * Work.Spaces.pth f s θ)
        = -∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
            * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      have hsf : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ :=
        ae_integrableOn_slice_f α hα hsq hf2
      have hsD : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ :=
        ae_integrableOn_slice_Dth α hα hsq hf2
      have hsf' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          MeasureTheory.IntegrableOn (fun θ => f s θ) Work.Spaces.Iθ := by
        rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
        exact hsf
      have hsD' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dth f s θ) Work.Spaces.Iθ := by
        rw [Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
        exact hsD
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hsf' hsD'
      filter_upwards [hsf', hsD'] with s hfs hDs hs'
      rw [C0thetaIBP_Q α hα hsq hbd hs' (hfs hs') (hDs hs')]
      ring
    rw [step3]
    have step4 : (∫ s in Set.Ioi (0 : ℝ), (1 / (s * (1 + s)))
          * ∫ θ in Work.Spaces.Iθ, Work.Coercivity.C0g θ * f s θ)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.C0g θ * f s θ / (s * (1 + s)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs' => ?_)
      rw [MeasureTheory.integral_div]
      ring
    rw [step4]
  -- ## Cauchy–Schwarz and the numerical bound
  calc (Work.Coercivity.C0 f) ^ 2
      = (∫ p, A p * B p ∂μ) ^ 2 := by rw [hC0, hX]; ring
    _ ≤ (∫ p, A p ^ 2 ∂μ) * (∫ p, B p ^ 2 ∂μ) :=
        Work.Coercivity.cs_integral_mul
          ((MeasureTheory.memLp_two_iff_integrable_sq hA_aesm).mpr hA2int)
          ((MeasureTheory.memLp_two_iff_integrable_sq hB_aesm).mpr hB2int)
    _ = Work.Coercivity.Ef f
          * (Work.Coercivity.C0Ih * Work.Coercivity.C0D) := by rw [hA2eq, hB2eq]
    _ ≤ Work.Coercivity.Ef f * 64 := by nlinarith [hnum, hEf]
    _ = 64 * Work.Coercivity.Ef f := by ring



/-- **The pointwise decomposition of `D_z𝓛_Γ^T` in the interior class.**  With
`𝓛_Γ^T = 𝓛̂ + Corr` (`LGammaT_eq_Lhat_add_Corr`), the `z`-derivative splits as

  `D_z(𝓛_Γ^T f) = D_z(𝓛̂ f) + Z₃ + Z₄ + Z₇`,

where `Z₃, Z₄, Z₇` are the three nonlocal/projector terms of `Work.Coercivity.SumI`. -/
theorem Dz_LGammaT_eq_Lhat_add_Zrest (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hfH : Work.Coercivity.HardyHyp f) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ := by
  intro z θ hz hθ
  have hz1 : (-1 : ℝ) < z := by linarith
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα (by linarith)
  have hIoo : IsOpen (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hcdPz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_pz hIoo hsq
  have hcdPth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_pth hIoo hsq
  have hdiffF : DifferentiableAt ℝ (fun t : ℝ => f t θ) z :=
    (((hsq.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz1))
  have hdiffPz : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPz hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz1))
  have hdiffPth : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pth f t θ) z :=
    (((Work.FTS.LocData.contDiffOn_slice_z hcdPth hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz1))
  have hF : HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f z θ) z := hdiffF.hasDerivAt
  have hPz : HasDerivAt (fun t : ℝ => Work.Spaces.pz f t θ)
      (Work.Spaces.pz (Work.Spaces.pz f) z θ) z := hdiffPz.hasDerivAt
  have hPth : HasDerivAt (fun t : ℝ => Work.Spaces.pth f t θ)
      (Work.Spaces.pz (Work.Spaces.pth f) z θ) z := hdiffPth.hasDerivAt
  have hden1 : HasDerivAt (fun t : ℝ => 1 + t) (1 : ℝ) z := (hasDerivAt_id z).const_add 1
  -- ## the derivative of the `𝓛̂`-slice
  have hDz : HasDerivAt (fun t : ℝ => t * Work.Spaces.pz f t θ)
      (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) z :=
    (hasDerivAt_id z).mul hPz
  have hq3 : HasDerivAt (fun t : ℝ => 2 * f t θ / (1 + t))
      ((2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2) z :=
    (hF.const_mul 2).div hden1 h1z
  have hq4 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * θ) * Work.Spaces.pth f t θ / (1 + t))
      ((3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
        - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z :=
    ((hPth.const_mul (3 * Real.sin (2 * θ))).div hden1 h1z)
  have hLhatSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
      (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2) z := by
    have hmain := ((hF.add hDz).sub hq3).sub hq4
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Work.FTS.CoercivityFix.Lhat_eq]
    simp only [Work.Spaces.Dz, Work.Spaces.Dth]
    ring
  -- ## the derivative of the `Corr`-slice
  have hL12 : HasDerivAt (fun t : ℝ => Work.Coercivity.L12f f t)
      (-(Work.Coercivity.Kavg f z / z)) z := Work.Coercivity.L12f_zDeriv f hfH hz
  have hsq : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
    have hraw := hden1.pow 2
    have hfun : ((fun t : ℝ => 1 + t) ^ 2) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv : HasDerivAt (fun t : ℝ => ((1 + t) ^ 2)⁻¹)
      (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2) z := hsq.inv (by positivity)
  have hprod : HasDerivAt (fun t : ℝ => t * ((1 + t) ^ 2)⁻¹)
      (1 * ((1 + z) ^ 2)⁻¹ + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) z :=
    (hasDerivAt_id z).mul hinv
  have hg1 : HasDerivAt
      (fun t : ℝ => (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (t * ((1 + t) ^ 2)⁻¹)
        * Work.Coercivity.L12f f t)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))) z :=
    (hprod.const_mul (-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹))).mul hL12
  have hsq2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * z) z := by
    have hraw := ((hasDerivAt_id z).pow 2).const_mul 2
    have hfun : (fun y : ℝ => 2 * (id ^ 2) y) =ᶠ[𝓝 z] (fun t : ℝ => 2 * t ^ 2) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp; ring)
  have hcube : HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + z) ^ 2) z := by
    have hraw := hden1.pow 3
    have hfun : ((fun t : ℝ => 1 + t) ^ 3) =ᶠ[𝓝 z] (fun t : ℝ => (1 + t) ^ 3) :=
      Filter.Eventually.of_forall (fun t => by simp)
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by simp)
  have hinv3 : HasDerivAt (fun t : ℝ => ((1 + t) ^ 3)⁻¹)
      (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2) z := hcube.inv (by positivity)
  have hinner : HasDerivAt (fun t : ℝ => 2 * t ^ 2 * ((1 + t) ^ 3)⁻¹)
      (4 * z * ((1 + z) ^ 3)⁻¹
        + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)) z :=
    hsq2.mul hinv3
  have hg2 : HasDerivAt
      (fun t : ℝ => (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (2 * t ^ 2 * ((1 + t) ^ 3)⁻¹))
      ((Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
        * (4 * z * ((1 + z) ^ 3)⁻¹
          + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z :=
    hinner.const_mul _
  have hCorrSlice : HasDerivAt (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ)
      ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2))) z := by
    have hmain := hg1.add hg2
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz1] with t ht
    have ht' : (-1 : ℝ) < t := ht
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith
    simp only [Pi.add_apply]
    rw [Work.FTS.CoercivityFix.Corr_eq, Work.Coercivity.C0]
    field_simp
  -- ## the sum
  have hsum : HasDerivAt (fun t : ℝ => Work.Coercivity.LGammaT α f t θ)
      ((Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (1 * ((1 + z) ^ 2)⁻¹
          + z * (-(2 * (1 + z)) / ((1 + z) ^ 2) ^ 2)) * Work.Coercivity.L12f f z
        + ((-(2 * Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹)) * (z * ((1 + z) ^ 2)⁻¹))
          * (-(Work.Coercivity.Kavg f z / z))
        + (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ * Work.Coercivity.C0 f)
          * (4 * z * ((1 + z) ^ 3)⁻¹
            + 2 * z ^ 2 * (-(3 * (1 + z) ^ 2) / ((1 + z) ^ 3) ^ 2)))) z := by
    have hmain := hLhatSlice.add hCorrSlice
    refine hmain.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr]
    rfl
  have hderiv := hsum.deriv
  -- ## conclusion
  show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ = _
  rw [show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = z * deriv (fun t : ℝ => Work.Coercivity.LGammaT α f t θ) z from rfl, hderiv,
    show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz f z θ
        + (1 * Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - (2 * Work.Spaces.pz f z θ * (1 + z) - 2 * f z θ * 1) / (1 + z) ^ 2
        - (3 * Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ * (1 + z)
            - 3 * Real.sin (2 * θ) * Work.Spaces.pth f z θ * 1) / (1 + z) ^ 2)
      from by
        rw [show Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
            = z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z from rfl,
          hLhatSlice.deriv]]
  simp only [Work.Coercivity.Z3, Work.Coercivity.Z4, Work.Coercivity.Z7]
  field_simp
  ring

/-- The radial majorant `4(L₁₂dens)² + 4(L₁₂f/z)² + 16C₀²/(1+z)²` of the nonlocal deflection
`Z₃ + Z₄ + Z₇` of `D_z𝓛_Γ^T`. -/
noncomputable def ZrestBracket (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
    + 4 * (Work.Coercivity.L12f f z / z) ^ 2
    + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2

/-- The full majorant of the squared nonlocal deflection: `ZrestBracket f z` times the `θ`-weight
`300 sin(2θ)^{-η}`. -/
noncomputable def ZrestMaj (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ * ZrestBracket f z


/-- `z ↦ Kavg f z` is continuous on `z > 0` (it is `z · L₁₂dens`). -/
theorem continuousOn_Kavg_Ioi (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) :
    ContinuousOn (fun z : ℝ => Work.Coercivity.Kavg f z) (Set.Ioi 0) := by
  have hL : ContinuousOn (fun z : ℝ => Work.FM.L12dens Work.Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hfH.hcont z hz).continuousWithinAt
  refine (continuousOn_id.mul hL).congr (fun z hz => ?_)
  have hz0 : z ≠ 0 := ne_of_gt hz
  show Work.Coercivity.Kavg f z = z * Work.FM.L12dens Work.Spaces.K f z
  rw [Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (s := z) hz0]
  simp only [Work.Coercivity.Kavg, Work.Spaces.Iθ]
  field_simp

/-- The sum `Z₃ + Z₄ + Z₇` of the three nonlocal deflections of `D_z𝓛_Γ^T` is continuous on the
open quadrant. -/
theorem continuousOn_Zrest_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hfH : Work.Coercivity.HardyHyp f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z3 α f p.1 p.2
      + Work.Coercivity.Z4 α f p.1 p.2 + Work.Coercivity.Z7 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  have hKavg : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Kavg f p.1)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (continuousOn_Kavg_Ioi f hfH).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hL12f : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (Work.Coercivity.L12f_continuousOn f hfH).comp continuous_fst.continuousOn
      (fun p hp => hp.1)
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (Work.Coercivity.continuousOn_Gam α hα).comp continuous_snd.continuousOn
      (fun p hp => ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)
  have hden2 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd,
      Work.Spaces.c α * (1 + p.1) ^ 2 ≠ 0 := fun p hp =>
    mul_ne_zero hc (ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity))
  have hden3 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd,
      Work.Spaces.c α * (1 + p.1) ^ 3 ≠ 0 := fun p hp =>
    mul_ne_zero hc (ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity))
  have hden4 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd, (1 + p.1) ^ 4 ≠ 0 := fun p hp =>
    ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity)
  have hZ3 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z3 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hA : ContinuousOn (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        Work.FTS.CoercivityFix.Coer1.Qd :=
      (((continuous_const.mul continuous_fst).continuousOn).mul hGam).div
        ((continuous_const.mul ((continuous_const.add continuous_fst).pow 2)).continuousOn)
        hden2
    refine (hA.mul hKavg).congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z3, Pi.mul_apply]
  have hZ4 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z4 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hB : ContinuousOn (fun p : ℝ × ℝ => -(2 * p.1 * (1 - p.1) * Work.Spaces.Gam α p.2
        / (Work.Spaces.c α * (1 + p.1) ^ 3))) Work.FTS.CoercivityFix.Coer1.Qd :=
      ((((continuous_const.mul continuous_fst).continuousOn).mul
        (continuous_const.sub continuous_fst).continuousOn).mul hGam).div
        ((continuous_const.mul ((continuous_const.add continuous_fst).pow 3)).continuousOn)
        hden3 |>.neg
    refine (hB.mul hL12f).congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z4, Pi.mul_apply]
  have hZ7 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z7 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hC : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 * (2 - p.1) / (1 + p.1) ^ 4)) Work.FTS.CoercivityFix.Coer1.Qd :=
      (hGam.div_const (Work.Spaces.c α)).mul
        ((((continuous_const.mul (continuous_fst.pow 2)).continuousOn).mul
          (continuous_const.sub continuous_fst).continuousOn).div
          (((continuous_const.add continuous_fst).pow 4).continuousOn) hden4)
    have h := hC.mul (continuousOn_const (c := Work.Coercivity.C0 f))
    refine h.congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z7, Pi.mul_apply]
    ring
  exact (hZ3.add hZ4).add hZ7

/-- **Pointwise bound for the nonlocal deflection `Z₃ + Z₄ + Z₇`.**  With `D = L₁₂dens(f)`,
`L = L₁₂(f)` and `C = L₁₂(Transport f)(0)`, the three summands factor as
`Z₃ = (Γ/c)(2z/(1+z)²)(zD)`, `Z₄ = (Γ/c)(-(2z(1-z)/(1+z)³))L` and
`Z₇ = (Γ/c)C·(2z²(2-z)/(1+z)⁴)`, so that `(Z₃+Z₄+Z₇)²w²sin^{-η}` is controlled by
`3(a²+b²+c²)` with `a = 2D`, `b = -2(1-z)L/(z(1+z))`, `c = 2(2-z)C/(1+z)²`, and
`|b| ≤ 2|L|/z`, `|c| ≤ 4|C|/(1+z)`; with `(Γ/c)² ≤ 100` this gives the stated constant. -/
theorem Zrest_sq_pt (α : ℝ) (hα : 0 < α) (hα1' : α ≤ 1) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
          * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2
            + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1'
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hG : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
      Work.Coercivity.Gam_div_c_bound hα hα1' hθ
    have h2 := abs_le.mp h1
    nlinarith [abs_nonneg (Work.Spaces.Gam α θ / Work.Spaces.c α), h2.1, h2.2]
  have hsin_nn : 0 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ := by
    rw [Work.FTS.CoercivityFix.Coer1.sig]
    exact Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hKavg : Work.Coercivity.Kavg f z = z * Work.FM.L12dens Work.Spaces.K f z := by
    rw [Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (s := z) hz0]
    simp only [Work.Coercivity.Kavg, Work.Spaces.Iθ]
    field_simp
  have hZ3 : Work.Coercivity.Z3 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
          * Work.Coercivity.Kavg f z := by
    simp only [Work.Coercivity.Z3]
    field_simp
  have hZ4 : Work.Coercivity.Z4 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (-(2 * z * (1 - z) / (1 + z) ^ 3))
          * Work.Coercivity.L12f f z := by
    simp only [Work.Coercivity.Z4]
    field_simp
  have hZ7 : Work.Coercivity.Z7 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Coercivity.C0 f
          * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) := by
    simp only [Work.Coercivity.Z7]
  rw [hZ3, hZ4, hZ7, hKavg]
  simp only [Work.FTS.CoercivityFix.Coer1.Rho]
  have hcs : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro a b c
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hstep1 : ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)
        + (-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z
        + Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
      ≤ 3 * (((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
        + ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
        + (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2) :=
    hcs _ _ _
  have hstep2 : (Work.Spaces.w z) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
      = 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  have hstep3 : (Work.Spaces.w z) ^ 2
        * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
      ≤ 4 * (Work.Coercivity.L12f f z / z) ^ 2 := by
    have hL2 : 0 ≤ (Work.Coercivity.L12f f z) ^ 2 := sq_nonneg _
    have h1 : (1 - z) ^ 2 ≤ (1 + z) ^ 2 := by
      nlinarith [sq_nonneg ((1 : ℝ) + z - (1 - z)), hz.le, sq_nonneg (1 + z), sq_nonneg (1 - z)]
    have hnum : 4 * ((1 - z) * Work.Coercivity.L12f f z) ^ 2
        ≤ 4 * ((Work.Coercivity.L12f f z) ^ 2 * (1 + z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right h1 hL2
      nlinarith [h]
    have heq1 : (Work.Spaces.w z) ^ 2
          * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
        = 4 * ((1 - z) * Work.Coercivity.L12f f z) ^ 2 / (z ^ 2 * (1 + z) ^ 2) := by
      rw [Work.Spaces.w]
      field_simp
      ring
    have heq2 : 4 * (Work.Coercivity.L12f f z / z) ^ 2
        = 4 * ((Work.Coercivity.L12f f z) ^ 2 * (1 + z) ^ 2) / (z ^ 2 * (1 + z) ^ 2) := by
      field_simp
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hstep4 : (Work.Spaces.w z) ^ 2
        * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
      ≤ 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2 := by
    have hC2 : 0 ≤ (Work.Coercivity.C0 f) ^ 2 := sq_nonneg _
    have h1 : (2 - z) ^ 2 ≤ 4 * (1 + z) ^ 2 := by
      nlinarith [hz.le, sq_nonneg (1 + z), sq_nonneg (2 - z), sq_nonneg z]
    have hnum : 4 * ((2 - z) * Work.Coercivity.C0 f) ^ 2
        ≤ 4 * (4 * (Work.Coercivity.C0 f) ^ 2 * (1 + z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right h1 hC2
      nlinarith [h]
    have heq1 : (Work.Spaces.w z) ^ 2
          * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        = 4 * ((2 - z) * Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
      ring
    have heq2 : 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2
        = 4 * (4 * (Work.Coercivity.C0 f) ^ 2 * (1 + z) ^ 2) / (1 + z) ^ 4 := by
      field_simp
      ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hmid : 3 * ((Work.Spaces.w z) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
      + (Work.Spaces.w z) ^ 2
        * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
      + (Work.Spaces.w z) ^ 2
        * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2)
      ≤ 3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
        + 4 * (Work.Coercivity.L12f f z / z) ^ 2
        + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
    linarith [hstep2, hstep3, hstep4]
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  calc ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
          * (z * Work.FM.L12dens Work.Spaces.K f z)
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (-(2 * z * (1 - z) / (1 + z) ^ 3))
          * Work.Coercivity.L12f f z
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Coercivity.C0 f
          * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)
          + (-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z
          + Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
        ring
    _ ≤ (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (3 * (((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
          + ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
          + (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2))
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep1 (sq_nonneg _)) ?_
        exact mul_nonneg hWnn hsin_nn
    _ = (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * ((Work.Spaces.w z) ^ 2
            * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
          + (Work.Spaces.w z) ^ 2
            * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
          + (Work.Spaces.w z) ^ 2
            * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2)) := by
        ring
    _ ≤ (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hmid ?_
        exact mul_nonneg (sq_nonneg _) hsin_nn
    _ ≤ 100 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)) := by
        have h1 : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
            ≤ 100 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
          mul_le_mul_of_nonneg_right hG hsin_nn
        have h2 : 0 ≤ 3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2
            + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
          have h1z' : (0 : ℝ) < 1 + z := by linarith
          positivity
        exact mul_le_mul_of_nonneg_right h1 h2
    _ = 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
        ring

/-- **The two bounds on the nonlocal deflection `Z₃ + Z₄ + Z₇` of `D_z𝓛_Γ^T`.**

Both are the crude Cauchy–Schwarz/AM–GM bounds that suffice for the slot estimate: the
squared weighted `L²`-norm of `Z₃+Z₄+Z₇` is at most `10⁹ Ef` (the three summands contribute
`(L₁₂dens)²`, `(L₁₂f/z)²` — the two Hardy quantities — and `C₀²`), and the pairing with
`D_zf` is therefore bounded below by `-(1/40)EDz - 10¹⁰Ef`. -/
theorem Zrest_pairing_ge_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hfH : Work.Coercivity.HardyHyp f)
    (hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ 64 * Work.Coercivity.Ef f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ) ≤ 10 ^ 9 * Work.Coercivity.Ef f
    ∧ MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ -((1 / 40) * Work.Coercivity.EDz f + 10 ^ 10 * Work.Coercivity.Ef f)
        ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := by
  have hα1' : α ≤ 1 := by linarith
  have hreg : Work.FTS.Nonlin.RegQ α 5 f := hf.reg
  have hsq : Work.FTS.LocData.SmoothQuad f := hreg.1
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hreg (by norm_num)
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf2
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ :=
    fun z θ hθ => Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta z θ hθ
  have hEf0 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  -- ## integral data for the `θ`-factor
  have hsig_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) Work.Spaces.Iθ :=
    (Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
  have hsig_le : ∫ θ in Work.Spaces.Iθ,
      Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 400 := by
    have h := (Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).2
    rw [show (4 : ℝ) / (1 - Work.Spaces.eta) = 400 by rw [Work.Spaces.eta]; norm_num] at h
    exact h
  -- ## integral data for the three `z`-factors
  have hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  have hsl := Work.Coercivity.EL12z_ae_slice f hfw
  have hDens := Work.Coercivity.EL12z_Kd f hfH hsl
  have hDens_le : ∫ z in Set.Ioi (0 : ℝ),
      (Work.FM.L12dens Work.Spaces.K f z) ^ 2 ≤ 3 * Work.Coercivity.Ef f := by
    have h2 := Work.Coercivity.EL12z_weight f hfw hsl
    linarith [hDens.2, h2]
  have hLz_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) := by
    refine (hfH.intA 1 (by norm_num)).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Nat.cast_one, mul_one, Real.rpow_two, div_pow]
  have hLz_le : ∫ z in Set.Ioi (0 : ℝ), (Work.Coercivity.L12f f z / z) ^ 2
      ≤ 16 * Work.Coercivity.Ef f := by
    have h := Work.Coercivity.EL12z_le f hfH hfw
    rw [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz] at h
    rwa [setIntegral_Iz_eq_Ioi] at h
  have hInv_int : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ioi 0) := by
    refine (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num)).congr (Filter.Eventually.of_forall (fun z => ?_))
    show (z + 1) ^ (-2 : ℝ) = (1 + z) ^ (-2 : ℝ)
    rw [show z + 1 = 1 + z by ring]
  have hInv_val : ∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-2 : ℝ) = 1 := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) ((1 + x) ^ (-2 : ℝ)) x := by
      intro x hx
      have hx0 : (0 : ℝ) < 1 + x := by
        have hx' : (0 : ℝ) < x := hx
        linarith
      have h1 : HasDerivAt (fun z : ℝ => 1 + z) (1 : ℝ) x := (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-((1 + x) ^ 2)⁻¹) x := by
        have h := h1.inv (ne_of_gt hx0)
        convert h using 1
        ring
      have h3 : HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (-(-((1 + x) ^ 2)⁻¹)) x := h2.neg
      refine h3.congr_deriv ?_
      rw [neg_neg, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (x := 1 + x) (le_of_lt hx0) 2, Real.rpow_two]
    have hcont : ContinuousWithinAt (fun z : ℝ => -((1 + z)⁻¹)) (Set.Ici 0) 0 := by
      refine ContinuousAt.neg ?_ |>.continuousWithinAt
      exact ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id) (by norm_num)
    have htend : Filter.Tendsto (fun z : ℝ => -((1 + z)⁻¹)) Filter.atTop (𝓝 (0 : ℝ)) := by
      have h : Filter.Tendsto (fun z : ℝ => (1 + z)⁻¹) Filter.atTop (𝓝 0) :=
        Filter.Tendsto.comp tendsto_inv_atTop_zero
          (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      simpa using h.neg
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (m := 0)
      hcont hderiv hInv_int htend
    simpa using h
  -- ## the three summands of the bracket, over `(0,∞)` and over `Iz`
  have hb1 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2) (Set.Ioi 0) :=
    (hDens.1.const_mul 4).congr (Filter.Eventually.of_forall (fun z => by ring))
  have hb2 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      4 * (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) :=
    (hLz_int.const_mul 4).congr (Filter.Eventually.of_forall (fun z => by ring))
  have hb3 : MeasureTheory.IntegrableOn (fun z : ℝ =>
      16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine ((hInv_int.const_mul (16 * (Work.Coercivity.C0 f) ^ 2))).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : (0 : ℝ) < 1 + z := by
      have hz' : (0 : ℝ) < z := hz
      linarith
    rw [Real.rpow_neg (x := 1 + z) (le_of_lt hz0) 2, Real.rpow_two]
    field_simp
  have hb3val : ∫ z in Set.Ioi (0 : ℝ),
      16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2 = 16 * (Work.Coercivity.C0 f) ^ 2 := by
    rw [show (∫ z in Set.Ioi (0 : ℝ), 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ),
            (16 * (Work.Coercivity.C0 f) ^ 2) * ((1 + z) ^ (-2 : ℝ)) from by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards with z hz
      have hz' : (0 : ℝ) < z := hz
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      rw [Real.rpow_neg (x := 1 + z) (le_of_lt hz0) 2, Real.rpow_two]
      field_simp]
    rw [MeasureTheory.integral_const_mul, hInv_val, mul_one]
  -- ## the bracket: integrability and integral bound
  have hbr_int : MeasureTheory.IntegrableOn (ZrestBracket f) Work.Spaces.Iz :=
    (integrableOn_Iz_iff_Ioi _).mpr (by
      refine ((hb1.add hb2).add hb3).congr (Filter.Eventually.of_forall (fun z => ?_))
      simp only [ZrestBracket, Pi.add_apply])
  have hbr_le : ∫ z in Work.Spaces.Iz, ZrestBracket f z ≤ 1100 * Work.Coercivity.Ef f := by
    have hIz : ∫ z in Work.Spaces.Iz, ZrestBracket f z
        = ∫ z in Set.Ioi (0 : ℝ), ZrestBracket f z := setIntegral_Iz_eq_Ioi _
    rw [hIz]
    have hsplit : ∫ z in Set.Ioi (0 : ℝ), ZrestBracket f z
        = (∫ z in Set.Ioi (0 : ℝ), 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2)
          + (∫ z in Set.Ioi (0 : ℝ), 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          + (∫ z in Set.Ioi (0 : ℝ), 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
      simp only [ZrestBracket]
      have hAB : MeasureTheory.IntegrableOn (fun z : ℝ =>
          4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2) (Set.Ioi 0) :=
        (hb1.add hb2).congr (Filter.Eventually.of_forall (fun z => by
          simp only [Pi.add_apply]))
      rw [MeasureTheory.integral_add
          (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun z : ℝ => 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          (g := fun z : ℝ => 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)
          hAB hb3,
        MeasureTheory.integral_add
          (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (f := fun z : ℝ => 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2)
          (g := fun z : ℝ => 4 * (Work.Coercivity.L12f f z / z) ^ 2)
          hb1 hb2]
    rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hb3val]
    nlinarith [hDens_le, hLz_le, hC0, hEf0]
  -- ## integrability of the majorant and domination of `S²ρ`
  have hmaj_int : MeasureTheory.IntegrableOn (Function.uncurry (ZrestMaj f))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hθ : MeasureTheory.Integrable
        (fun θ : ℝ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hsig_int.const_mul 300
    have hz : MeasureTheory.Integrable (ZrestBracket f)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hbr_int
    have h := hz.mul_prod hθ
    rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, ZrestMaj]
    ring
  have hS2_cont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    ((continuousOn_Zrest_Q α hα hα1' hfH).pow 2).mul
      (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
  have hS2_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q hS2_cont hmaj_int ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    have hθmem : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have h := Zrest_sq_pt (f := f) α hα hα1' hp1 hθmem
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρnn p.1 p.2 hθmem))]
    simp only [ZrestMaj, ZrestBracket]
    exact h
  -- ## the product-measure forms and the bound on `wip ρ S S`
  have hS2_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hS2_int
  have hmaj_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ => ZrestMaj f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hmaj_int
  have hS2_wip : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip]
    rw [MeasureTheory.integral_prod]
    · refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Work.FTS.CoercivityFix.Coer1.Rho]
      ring
    · exact hS2_prod
  have hS_bound : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) ≤ 10 ^ 9 * Work.Coercivity.Ef f := by
    have hprod : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ)
        = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hS2_wip
    rw [hprod]
    have hmono : (∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2
            + Work.Coercivity.Z4 α f p.1 p.2 + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ ∫ p : ℝ × ℝ, ZrestMaj f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine MeasureTheory.integral_mono_ae hS2_prod hmaj_prod ?_
      filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
        Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
      have hθmem : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
      have h := Zrest_sq_pt (f := f) α hα hα1' hp1 hθmem
      simp only [ZrestMaj, ZrestBracket]
      exact h
    have hmaj_val : (∫ p : ℝ × ℝ, ZrestMaj f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≤ 10 ^ 9 * Work.Coercivity.Ef f := by
      rw [show (fun p : ℝ × ℝ => ZrestMaj f p.1 p.2)
          = fun p : ℝ × ℝ => ZrestBracket f p.1
              * (300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta p.2) from by
        funext p
        simp only [ZrestMaj]
        ring]
      rw [MeasureTheory.integral_prod_mul (f := ZrestBracket f)
        (g := fun θ : ℝ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)]
      have h1 : ∫ θ in Work.Spaces.Iθ,
          300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 120000 := by
        rw [MeasureTheory.integral_const_mul]
        have h2 : (300 : ℝ) * ∫ θ in Work.Spaces.Iθ,
            Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ ≤ 120000 := by
          have h2' := mul_le_mul_of_nonneg_left hsig_le (show (0 : ℝ) ≤ 300 by norm_num)
          norm_num at h2'
          exact h2'
        exact h2
      have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ := by
        rw [MeasureTheory.integral_const_mul]
        refine mul_nonneg (by norm_num) ?_
        refine integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
      have h4 : (0 : ℝ) ≤ 1100 * Work.Coercivity.Ef f := mul_nonneg (by norm_num) hEf0
      exact le_trans (mul_le_mul hbr_le h1 h3 h4) (by nlinarith [hEf0])
    linarith [hmono, hmaj_val]
  -- ## the pairing with `D_z f`
  have hDz2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzEta 1 (by norm_num)).congr_fun ?_
      (measurableSet_Ici.prod measurableSet_Icc)
    rintro ⟨z, θ⟩ _
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hDz2_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Dz f p.1 p.2) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hDz2
  have hpair_cont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    ((continuousOn_Zrest_Q α hα hα1' hfH).mul
      (Work.FTS.CoercivityFix.Coer1.continuousOn_DzIter_Q hsq 1)).mul
      (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
  have hpair_maj : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (1 / 40) * ((Work.Spaces.Dz f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
        + 10 * ((Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (hDz2.const_mul (1 / 40)).add (hS2_int.const_mul 10)
  have hpair_pt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
          + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ|
        ≤ (1 / 40) * ((Work.Spaces.Dz f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
          + 10 * ((Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) ^ 2
            * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ) := by
    intro z hz θ hθ
    have hρp : 0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ := hρnn z θ hθ
    have hkey : 0 ≤ Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
        * (|Work.Spaces.Dz f z θ| - 20 * |(Work.Coercivity.Z3 α f z θ
            + Work.Coercivity.Z4 α f z θ + Work.Coercivity.Z7 α f z θ)|) ^ 2 :=
      mul_nonneg hρp (sq_nonneg _)
    have hDzsq : |Work.Spaces.Dz f z θ| ^ 2 = (Work.Spaces.Dz f z θ) ^ 2 := sq_abs _
    have hSsq : |(Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ)| ^ 2
        = (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) ^ 2 := sq_abs _
    rw [abs_mul, abs_mul, abs_of_nonneg hρp]
    nlinarith [hkey, hDzsq, hSsq]
  have hpair_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q hpair_cont hpair_maj ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    exact hpair_pt p.1 (le_of_lt hp1) p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
  refine ⟨hS2_int, hS_bound, hpair_int, ?_⟩
  -- ## the lower bound for the pairing
  have hprod' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
        + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f)
      = ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Coercivity.wip_eq_integral_prod _ _ _ hpair_int
  rw [hprod']
  have hpair_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
        + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hpair_int
  have hpair_maj_prod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hpair_maj
  have hmono2 : (∫ p : ℝ × ℝ, -((1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p : ℝ × ℝ, ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
          + Work.Coercivity.Z7 α f p.1 p.2) * Work.Spaces.Dz f p.1 p.2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.integral_mono_ae hpair_maj_prod.neg hpair_prod ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    have h := hpair_pt p.1 (le_of_lt hp1) p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    linarith [neg_le_of_abs_le h]
  have hval : (∫ p : ℝ × ℝ, -((1 / 40) * ((Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2)
        + 10 * ((Work.Coercivity.Z3 α f p.1 p.2 + Work.Coercivity.Z4 α f p.1 p.2
            + Work.Coercivity.Z7 α f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = -((1 / 40) * Work.Coercivity.EDz f + 10 * Work.Coercivity.wip
          (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ)
          (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ)) := by
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_add
      (hDz2_prod.const_mul (1 / 40)) (hS2_prod.const_mul 10),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hA : (∫ p : ℝ × ℝ, (Work.Spaces.Dz f p.1 p.2) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = Work.Coercivity.EDz f := by
      rw [Work.Coercivity.EDz_eq_wip]
      rw [Work.Coercivity.wip_eq_integral_prod
        (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        (Work.Spaces.Dz f) (Work.Spaces.Dz f) ?_]
      · refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        rcases p with ⟨z, θ⟩
        simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
        rw [show (2 : ℝ) * θ = θ * 2 by ring]
        ring
      · refine hDz2.congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
        rintro ⟨z, θ⟩ _
        simp only [Function.uncurry_apply_pair, Work.FTS.CoercivityFix.Coer1.Rho,
          Work.FTS.CoercivityFix.Coer1.sig]
        rw [show (2 : ℝ) * θ = θ * 2 by ring]
        ring
    rw [hA, ← hS2_wip]
  linarith [hmono2, hval, hS_bound]


theorem slotDz_LGammaT (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hHH : Work.Coercivity.HardyHyp f) :
    (1 / 5) * Work.Coercivity.EDz f - 100 * Work.Coercivity.EfEta f
        - 100 * Work.Coercivity.EDth α f - 10 ^ 12 * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f) := by
  have hα1' : α ≤ 1 := by linarith
  have hα4 : α ≤ 1 / 4 := by linarith
  have hreg : Work.FTS.Nonlin.RegQ α 5 f := hf.reg
  have hsq : Work.FTS.LocData.SmoothQuad f := hreg.1
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hreg (by norm_num)
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf2
  -- ## the two estimates
  have hC0 := C0_sq_le_Ef_Q α hα hα1 hf
  obtain ⟨hS2_int, hS_bound, hpair_int, hpair_lb⟩ :=
    Zrest_pairing_ge_Q α hα hα1 hf hHH hC0
  have hA' : (47 / 100) * Work.Coercivity.EDz f
      - (Work.Coercivity.EfEta f + 4 * Work.Coercivity.EDth α f
        + (1 / 8) * Work.Coercivity.EDz f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
    have h := Work.FTS.CoercivityFix.Coer1.est_A α hα hα4 hf2
    rwa [← Work.FTS.CoercivityFix.Coer1.EDz_eq_En f,
      ← Work.FTS.CoercivityFix.Coer1.EfEta_eq_En f,
      ← Work.FTS.CoercivityFix.Coer1.EDth_eq_En α f] at h
  -- ## integrability of the `𝓛̂`-pairing
  have hDzLhat_int : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hsum := hp.intLhat_Dz_eta.add hp.intE2hat_Dz_eta
    refine hsum.congr ?_
    have hμ : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.iz_prod_restrict.symm
    rw [hμ]
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
      Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
    obtain ⟨z, θ⟩ := p
    have hkey := Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat hsq hp1 hp2.1 hp2.2
    simp only [Pi.add_apply, Function.uncurry_apply_pair]
    rw [hkey]
    ring
  -- ## the a.e. pointwise decomposition and the splitting of the pairing
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
          + (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
            + Work.Coercivity.Z7 α f z θ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    have h := Dz_LGammaT_eq_Lhat_add_Zrest α hα hα1 hsq hHH z θ hz hθ
    rw [h]
    ring
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      hDzLhat_int hpair_int
  -- ## nonnegativity of the energies
  have e1 : 0 ≤ Work.Coercivity.EDz f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDz_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e2 : 0 ≤ Work.Coercivity.EfEta f := by
    rw [Work.FTS.CoercivityFix.Coer1.EfEta_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e3 : 0 ≤ Work.Coercivity.EDth α f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    exact Work.FTS.CoercivityFix.Coer1.En_nonneg _ _
  have e4 : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
  have hsplit' : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (Work.Spaces.Dz (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (fun z θ => Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ
              + Work.Coercivity.Z7 α f z θ) (Work.Spaces.Dz f) := hsplit
  rw [hsplit']
  nlinarith [hA', hpair_lb, e1, e2, e3, e4]

end Work.FTS.CoercivityFix.Coer1T
