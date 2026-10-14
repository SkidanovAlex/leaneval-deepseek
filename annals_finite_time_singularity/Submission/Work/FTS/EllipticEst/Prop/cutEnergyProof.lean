import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.Honest.Step1G.EnergyG
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.final
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeUHk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `AngAWeak/aeUHk` — the level-`0` `ρ`-mass of `u` in the a.e. class of `prop:H2`

Target: `HkMem α 0 u` together with `nrm α u ≤ C * nrm α G` for data `AeData α u G`
(`ρ = w² σ`, `σ = sin(2θ)^{-η}`, `nrm α f = √(HkSq α 0 f)`): the `u`-half of Step 1 of
Elgindi's `prop:H2` in the almost-everywhere class.

## Route

* `HkMem α 0 u` is `Cores.AeStep2Aux.aeUHk_mem` (the a.e. slicewise second-order weighted
  Poincaré inequality `∫_θ u²σ ≤ C ∫_θ (∂_θθu)²σ`, integrated against `w²`);
* the norm bound comes from the **truncated `w²`-energy inequality** in its `∫⁻` form
  (`H2W.AeProof.AeEnergyExpl`)

  `α²·A + B ≤ K·M + ½·HkSq α 0 G`,  `K = 13/2 + 3α² + (3/2)α(5+α) ≤ 8.657 < 9`,

  where `A = ∫⁻_z w²∫⁻_θ (z∂_zu)²`, `B = ∫⁻_z w²∫⁻_θ (∂_θu)²`, `M = ∫⁻_z w²∫⁻_θ u²`,
  combined with
* the **constrained slice gap** `9∫_θ u² ≤ ∫_θ (∂_θu)²` a.e. in `z`
  (`H2W.AeProof.AeGapSlices`, fed by the a.e. `0⁺`-limits `AngAWeak.aeLeftTendsto`),
  which absorbs the `K·M` term because `K/9 < 1`; this gives `B ≤ 15·HkSq α 0 G`;
* the **`σ`-Poincaré upgrade** `HkSq α 0 u ≤ C_σ · B` (`H2W.AeProof.AeSigmaUpgradeU_all`,
  via the `∫⁻`-form `H2W.AeProof.ae.ofReal_HkSq_eq` of `HkSq`),
  so that `HkSq α 0 u ≤ 15 C_σ · HkSq α 0 G`, and the norm bound follows by `Real.sqrt`.
-/

/-! ## Auxiliary slice facts -/

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square `g² w² σ`. -/
theorem aeUHk_HkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ

/-- **The `θ`-derivative of a slice is square-integrable for every `z > 0`.**  From
`HkMem α 0 (∂_θθu)` the slice lemma `slice_bdd_of_sq_mul_sEta` bounds `u z θ` and
`∂_θu z θ` on the open interval, whence `(∂_θu z ·)²` is integrable on `Iθ`. -/
theorem aeUHk_pth_sq_integrable (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact ((h.smooth 2).comp (by fun_prop) hmap)
  have hint : IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have h1 := h.memAng2.1 z hzI
    have h2 : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      h1.congr_fun (fun θ hθ => aeUHk_HkIntegrand_zero α (Work.Spaces.pthIter 2 u) z hθ)
        measurableSet_Icc
    have hw' : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
    have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
    refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
    have hpth2 : Work.Spaces.pthIter 2 u z θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hpth2]
    field_simp
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hslice hint
  have hpair : volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set hst
  rw [IntegrableOn, hms]
  refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    ((measurable_deriv (fun θ' : ℝ => u z θ')).pow_const 2).aestronglyMeasurable
    (C ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hb := (hC θ hθ).2
  rw [Real.norm_of_nonneg (sq_nonneg _), show Work.Spaces.pth u z θ
    = deriv (fun θ' : ℝ => u z θ') θ from rfl, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2

/-! ## The constrained slice gap in `∫⁻` form -/


/-- **The constrained slice gap in `∫⁻` form**:
`9 · ∫⁻_z w² ∫⁻_θ u² ≤ ∫⁻_z w² ∫⁻_θ (∂_θu)²`. -/
theorem aeUHk_ofReal_nine_mul_le {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
  have hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    aeLeftTendsto α u G h
  have hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  have hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact aeUHk_pth_sq_integrable α u G h z hz
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC hint
  have htransport : ∀ ⦃P : ℝ → Prop⦄,
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), P z) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), P z) := by
    intro P hP
    rw [Work.Spaces.Iz]
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hP
  have hgapIz := htransport hgap
  have hCIz := htransport hC
  have hintIz := htransport hint
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal 9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) := by
    filter_upwards [hgapIz, hCIz, hintIz] with z hgz hCz hintz
    have hI1 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
      hCz.pow 2 |>.integrableOn_compact isCompact_Icc
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI1
        (Filter.Eventually.of_forall (fun θ => sq_nonneg _)),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintz
        (Filter.Eventually.of_forall (fun θ => sq_nonneg _)),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
    exact ENNReal.ofReal_le_ofReal hgz
  calc ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal 9
          * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 9) _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal 9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        refine MeasureTheory.lintegral_congr fun z => ?_
        ring
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hkey] with z hz
        exact mul_le_mul_of_nonneg_left hz zero_le

/-! ## The coefficient of the energy inequality and its arithmetic -/

/-- The coefficient `K` of the truncated energy inequality. -/
def aeUHk_K (α : ℝ) : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))

theorem aeUHk_K_pos (α : ℝ) : 0 < aeUHk_K α := by
  rw [aeUHk_K]; nlinarith [sq_nonneg α]

theorem aeUHk_K_lt_nine {α : ℝ} (hα0 : 0 ≤ α) (hα4 : α ≤ 1 / 4) :
    aeUHk_K α < 9 := by
  rw [aeUHk_K]; nlinarith

theorem aeUHk_K_le {α : ℝ} (hα0 : 0 ≤ α) (hα4 : α ≤ 1 / 4) :
    aeUHk_K α ≤ 87 / 10 := by
  rw [aeUHk_K]; nlinarith

/-! ## The target -/

theorem aeUHk : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨Cσ, hCσpos, hσ⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  refine ⟨Real.sqrt (Cσ * 15), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α u G h
  have hα0 : 0 ≤ α := h.hα.le
  have hα4 : α ≤ 1 / 4 := h.hα4
  refine ⟨Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem α u G h, ?_⟩
  -- ## the three a.e. hypotheses of the energy inequality
  have hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    aeLeftTendsto α u G h
  have hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  have hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
  -- ## the abbreviations
  set M : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hM
  set B : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hB
  -- ## the energy inequality
  have hσeq : ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
    Work.FTS.EllipticEst.H2W.AeProof.ae.ofReal_HkSq_eq α u
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem α u G h)
  have hMle : M ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 u) := by
    rw [hM, hσeq]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    refine MeasureTheory.lintegral_mono_ae ?_
    have hmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Work.Spaces.Iθ, MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
          (b := Real.pi / 2)).symm]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with θ hθ
    refine ENNReal.ofReal_le_ofReal ?_
    simpa using mul_le_mul_of_nonneg_left
      (Work.FTS.EllipticEst.H2W.one_le_sEta hθ) (sq_nonneg (u z θ))
  have hMlt : M < ⊤ := lt_of_le_of_lt hMle ENNReal.ofReal_lt_top
  have hEin : ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
      + B ≤ ENNReal.ofReal (aeUHk_K α) * M
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    rw [hB, hM, aeUHk_K]
    exact Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl α u G h hC hL0 hLπ
  have hBle : B ≤ ENNReal.ofReal (aeUHk_K α) * M
      + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    have h0 : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2))) :=
      bot_le
    exact le_trans (le_add_of_nonneg_left h0) hEin
  have hRHSlt : ENNReal.ofReal (aeUHk_K α) * M
      + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) < ⊤ :=
    ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMlt,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  have hBlt : B < ⊤ := lt_of_le_of_lt hBle hRHSlt
  -- ## the gap
  have hgap := aeUHk_ofReal_nine_mul_le (u := u) (G := G) h
  rw [← hM, ← hB] at hgap
  have hB1 : B.toReal ≤ aeUHk_K α * M.toReal + (1 / 2) * Work.Spaces.HkSq α 0 G := by
    have h := ENNReal.toReal_mono hRHSlt.ne hBle
    rw [ENNReal.toReal_add (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMlt).ne
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (aeUHk_K_pos α).le,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α 0 G)] at h
    linarith
  have hB2 : 9 * M.toReal ≤ B.toReal := by
    have h := ENNReal.toReal_mono hBlt.ne hgap
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9)] at h
  have hK9 : aeUHk_K α < 9 := aeUHk_K_lt_nine hα0 hα4
  have hden : 0 < 1 - aeUHk_K α / 9 := by nlinarith
  have hBfin : B.toReal ≤ ((1 / 2) / (1 - aeUHk_K α / 9)) * Work.Spaces.HkSq α 0 G := by
    have hM9 : M.toReal ≤ B.toReal / 9 := by linarith [hB2]
    have h1 : B.toReal ≤ aeUHk_K α * (B.toReal / 9) + (1 / 2) * Work.Spaces.HkSq α 0 G := by
      have h2 : aeUHk_K α * M.toReal ≤ aeUHk_K α * (B.toReal / 9) :=
        mul_le_mul_of_nonneg_left hM9 (aeUHk_K_pos α).le
      linarith [hB1, h2]
    have h2 : B.toReal * (1 - aeUHk_K α / 9) ≤ (1 / 2) * Work.Spaces.HkSq α 0 G := by
      nlinarith [h1]
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    linarith [h2]
  have hmul : (1 / 2) / (1 - aeUHk_K α / 9) ≤ 15 := by
    have hK : aeUHk_K α ≤ 87 / 10 := aeUHk_K_le hα0 hα4
    have hden' : 0 < 1 - aeUHk_K α / 9 := hden
    rw [div_le_iff₀ hden']
    nlinarith
  -- ## the `HkSq` bound
  have hUσ := hσ α u G h
  rw [← hB] at hUσ
  have hHk : Work.Spaces.HkSq α 0 u ≤ (Cσ * 15) * Work.Spaces.HkSq α 0 G := by
    have h1 : Work.Spaces.HkSq α 0 u = (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))).toReal := by
      rw [← hσeq, ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α 0 u)]
    rw [h1]
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))).toReal
        ≤ (ENNReal.ofReal Cσ * B).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBlt).ne hUσ
      _ = Cσ * B.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCσpos.le]
      _ ≤ Cσ * (((1 / 2) / (1 - aeUHk_K α / 9)) * Work.Spaces.HkSq α 0 G) :=
          mul_le_mul_of_nonneg_left hBfin hCσpos.le
      _ ≤ Cσ * (15 * Work.Spaces.HkSq α 0 G) := by
          refine mul_le_mul_of_nonneg_left ?_ hCσpos.le
          exact mul_le_mul_of_nonneg_right hmul (Work.Spaces.HkSq_nonneg α 0 G)
      _ = (Cσ * 15) * Work.Spaces.HkSq α 0 G := by ring
  -- ## the `nrm` bound
  calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
      = Real.sqrt (Work.Spaces.HkSq α 0 u) := rfl
    _ ≤ Real.sqrt ((Cσ * 15) * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hHk
    _ = Real.sqrt (Cσ * 15) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Cσ * 15)]
        rfl

end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.cutEnergyProof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

theorem cutEnergyProof : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp α u G :=
  Work.FTS.EllipticEst.Prop.CutEnergyAux.aeCutEnergyProp_holds

end Work.FTS.EllipticEst.Prop
end
