import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AeU2.aeU2_bound
import Submission.Work.FTS.EllipticEst.H2W.ESV.aeUHkAux
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSliceBdd
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Two elementary facts -/

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` is that to `(0,∞)`: the two sets differ
by the null singleton `{0}`. -/
private lemma restrict_Iz_eq_restrict_Ioi :
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

/-- The angular weight `σ = sin(2θ)^{-η}` dominates `1` off the two endpoints. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `ofReal` of a nonnegative Bochner integral is dominated by the `lintegral` of its `ofReal`,
for any function (no measurability needed: a non-strongly-measurable function has integral `0`). -/
private lemma ofReal_integral_le_lintegral' {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    (hnn : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ, f θ ∂μ) ≤ ∫⁻ θ, ENNReal.ofReal (f θ) ∂μ := by
  by_cases h : MeasureTheory.AEStronglyMeasurable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) h]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef (fun hi => h hi.aestronglyMeasurable)]
    simp

/-! ## The `HkSq α 0`-mass of `u` against the `σ`-mass -/

/-- For `u` whatsoever, `ofReal (HkSq α 0 u)` is dominated by the `σ`-weighted angular mass
of `u`. -/
private theorem ofReal_HkSq_le_sigmaMass (α : ℝ) {u : ℝ → ℝ → ℝ} :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 u) ≤
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have step1 : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) :=
    ofReal_integral_le_lintegral'
      (fun z => integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ) :=
    MeasureTheory.lintegral_mono
      (fun z => ofReal_integral_le_lintegral'
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α u hθ,
          ENNReal.ofReal_mul (sq_nonneg _)])
    rw [MeasureTheory.lintegral_congr_ae hae,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [Work.Spaces.HkSq]
    _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

end

/-- **The `u`-mass bound of Step 1 of `prop:H2` in the `AeData` class**, from the paper's
`w²`-weighted radial energy inequality (★) — the statement of
`Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl` / `Cores.Pieces.AeGradRho.ae_w2_energy` — taken
here as the hypothesis `hW2`.

Chain: (★) plus the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` (a.e. in `z`) gives
`9 Mc ≤ Bc ≤ K Mc + ½ HkSq α 0 G` with `K = 13/2 + 3α² + (3/2)α(5+α) ≤ 8.7 < 9`, hence
`Bc ≤ 30·(½ HkSq α 0 G)` and `Mc` is finite; the `σ`-upgrade
`AeSigmaUpgradeU_all` bounds the `σ`-mass `Sc` by `Cσ·Bc`, and the bridge
`ofReal_HkSq_le_sigmaMass` identifies `ofReal (HkSq α 0 u)` with at most `Sc`. -/
theorem ae_mass_bound_of
    (hW2 : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨Cσ, hCσpos, hσup⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FTS.EllipticEst.H2W.AeU2.aeU2_bound
  refine ⟨Real.sqrt (Cσ * 30 * (1 / 2)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α u G h
  -- ## the a.e. fibre data
  have hL0 := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  have hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
  have hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact Work.FTS.EllipticEst.AngAWeak.integrableOn_pth_sq_of_AeData_esv α u G h z hz
  -- ## the constrained slice gap, a.e. in `z`
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC hint
  -- ## the radial energy inequality
  have hEn := hW2 α u G h
  -- ## the three masses
  set Mc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMc
  set Bc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBc
  set Sc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) with hSc
  -- ## the `σ`-mass is finite, and dominates `Mc`
  have hSc_fin : Sc ≤ ENNReal.ofReal C₂
      * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
    rw [hSc, restrict_Iz_eq_restrict_Ioi]
    exact hC₂ α u G h hL0
  have hSc_ne_top : Sc ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hSc_fin
  have hMc_le_Sc : Mc ≤ Sc := by
    rw [hMc, hSc]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine mul_le_mul_of_nonneg_left ?_
      (bot_le : (⊥ : ℝ≥0∞) ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (sq_nonneg _) (one_le_sEta hθ))
  have hMc_ne_top : Mc ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hMc_le_Sc.trans hSc_fin)
  -- ## the slice gap in `lintegral` form
  have hgapI : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) := by
    rw [restrict_Iz_eq_restrict_Ioi]
    filter_upwards [hgap, hC, hint] with z hzgap hzC hzint
    have hLI : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
      (hzC.pow 2).integrableOn_compact isCompact_Icc
    have hL : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLI
        (Eventually.of_forall (fun θ => sq_nonneg _))).symm
    have hR : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzint
        (Eventually.of_forall (fun θ => sq_nonneg _))).symm
    rw [hL, hR]
    calc 9 * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
        = ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
            show ENNReal.ofReal (9 : ℝ) = (9 : ℝ≥0∞) from by norm_num]
      _ ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
          ENNReal.ofReal_le_ofReal hzgap
  have h9 : (9 : ℝ≥0∞) * Mc ≤ Bc := by
    rw [hMc, hBc]
    calc (9 : ℝ≥0∞) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        = ∫⁻ z in Work.Spaces.Iz, (9 : ℝ≥0∞)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) :=
          (MeasureTheory.lintegral_const_mul' 9 _ (by norm_num)).symm
      _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
          refine MeasureTheory.lintegral_congr (fun z => ?_)
          ring
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) :=
          MeasureTheory.lintegral_mono_ae
            (hgapI.mono (fun z hz => mul_le_mul_of_nonneg_left hz bot_le))
  -- ## the arithmetic in `ℝ`
  obtain ⟨hα0, hα4⟩ := h.hα, h.hα4
  have hKn_nonneg : (0 : ℝ) ≤ 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) := by
    nlinarith [hα0]
  have hKn87 : 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) ≤ 87 / 10 := by
    nlinarith [hα0, hα4]
  have hKn_lt9 : 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) < 9 := by linarith
  have hSG : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hhalf : (0 : ℝ) ≤ 1 / 2 * Work.Spaces.HkSq α 0 G := by linarith
  have hRHS_ne_top : ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mc
      + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) ≠ ⊤ :=
    (ENNReal.add_ne_top).mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hBc_ne_top : Bc ≠ ⊤ := ne_top_of_le_ne_top hRHS_ne_top (le_trans le_add_self hEn)
  have hBcreal : Bc.toReal ≤ (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mc.toReal
      + 1 / 2 * Work.Spaces.HkSq α 0 G := by
    have h := ENNReal.toReal_mono hRHS_ne_top (le_trans le_add_self hEn)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKn_nonneg, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal hSG] at h
    exact h
  have h9real : 9 * Mc.toReal ≤ Bc.toReal := by
    have h := ENNReal.toReal_mono hBc_ne_top h9
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
    exact h
  have hhalfmul : 29 * (1 / 2 * Work.Spaces.HkSq α 0 G) * (9 - (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))))
      ≥ (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (1 / 2 * Work.Spaces.HkSq α 0 G) := by
    nlinarith [hKn87, hKn_nonneg, hhalf]
  have hBc_le : Bc.toReal ≤ 30 * (1 / 2 * Work.Spaces.HkSq α 0 G) := by
    have hMr : (0 : ℝ) ≤ Mc.toReal := ENNReal.toReal_nonneg
    nlinarith [hBcreal, h9real, hKn87, hKn_nonneg, hhalf, hhalfmul, hMr]
  -- ## back to the `σ`-mass
  have hSc_real : Sc.toReal ≤ Cσ * Bc.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBc_ne_top)
      (hσup α u G h)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hCσpos)] at h
    exact h
  have hSc_le : Sc ≤ ENNReal.ofReal (Cσ * 30 * (1 / 2)) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    rw [← ENNReal.ofReal_toReal hSc_ne_top, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hSc_real, hBc_le, hCσpos]
  -- ## the final comparison
  have hmain : ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      ≤ ENNReal.ofReal (Cσ * 30 * (1 / 2)) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) :=
    (ofReal_HkSq_le_sigmaMass α).trans hSc_le
  have hreal : Work.Spaces.HkSq α 0 u ≤ Cσ * 30 * (1 / 2) * Work.Spaces.HkSq α 0 G := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hmain
    rw [ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α 0 u), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hSG] at h
    exact h
  calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
      = Real.sqrt (Work.Spaces.HkSq α 0 u) := rfl
    _ ≤ Real.sqrt (Cσ * 30 * (1 / 2) * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (Cσ * 30 * (1 / 2)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
        rw [Real.sqrt_mul (by positivity)]
        rfl

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
