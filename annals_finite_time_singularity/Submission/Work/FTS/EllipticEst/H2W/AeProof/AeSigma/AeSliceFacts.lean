import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeGSlice
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceSigmaLower
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeSigma/AeSliceFacts` — the slice-level data of the `σ`-weighted first-order estimate

For data `AeData α u G` and a.e. `z > 0`:

* `aeSliceBound`: `|u z θ| ≤ C·min(θ, π/2-θ)` and `|∂_θu z θ| ≤ C` on `(0,π/2)` — the
  endpoint rates that make the `σ`-weighted primitive of the `L₀`-self-form vanish;
* `aeSliceSigmaInt`: the `σ`-weighted slice integrability of the five pairings occurring in
  the equation and in the self-form.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.AeSigma

set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev sEtaR (θ : ℝ) : ℝ := Work.FTS.EllipticEst.sEta θ

theorem sEtaR_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sEtaR θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _

theorem measurable_sEtaR : Measurable sEtaR := by
  have h1 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    have h2 : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.measurable_sin.comp (measurable_const.mul measurable_id)
    exact h2.pow measurable_const
  have h3 : sEtaR = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    funext θ
    simp only [sEtaR, Work.FTS.EllipticEst.sEta]
  rw [h3]
  exact h1

theorem integrableOn_sEtaR : IntegrableOn sEtaR Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.integrableOn_thEta.1

/-- A function continuous on the open angular interval is a.e. strongly measurable for the
restricted measure on `Iθ`. -/
theorem aesm_of_contOn_Ioo {f : ℝ → ℝ} (h : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [Work.Spaces.Iθ]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-- The a.e. points of `Iθ` are interior points. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The slice `θ ↦ u z θ` of an `AeData` datum is continuous on the open interval. -/
theorem contOn_slice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  (Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 1).continuousOn

/-- The slice `θ ↦ ∂_θu z θ`. -/
theorem contOn_slice_pth {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pth u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz 2
  have := hsm.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  simpa [Work.Spaces.pth] using this

/-- The slice `θ ↦ ∂_zu z θ` (the angular restriction of `pz u`). -/
theorem contOn_slice_pz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz u) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).pz
  have hc := hS.continuousOn
  rw [Work.FTS.EllipticEst.Q0] at hc
  refine hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ?_)
  exact ⟨hz, hθ⟩

/-- The slice `θ ↦ ∂_z²u z θ`. -/
theorem contOn_slice_pzIter2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.pzIter 2 u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter 2 u) :=
    (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth).pzIter 2
  have hc := hS.continuousOn
  rw [Work.FTS.EllipticEst.Q0] at hc
  refine hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ?_)
  exact ⟨hz, hθ⟩

/-- The slice `θ ↦ G z θ` is a.e. strongly measurable: on the open interval `G` agrees with the
`C^∞` function `bslOp α u`, by the equation. -/
theorem aesm_slice_G {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  have hcont : ContinuousOn (fun θ => Work.Elliptic.bslOp α u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hc := hbsl.continuousOn
    rw [Work.FTS.EllipticEst.Q0] at hc
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hz, hθ⟩)
  refine (aesm_of_contOn_Ioo hcont).congr ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact h.eq z hz θ hθ.1 hθ.2

/-! ## Two integrability helpers -/

/-- Integrability of `f · σ` on `Iθ` from a uniform bound on `f`. -/
theorem integrableOn_mul_sEtaR_of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) :
    IntegrableOn (fun θ => f θ * sEtaR θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (integrableOn_sEtaR.const_mul C)
    (hmeas.mul measurable_sEtaR.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sEtaR_nonneg hθ)]
  exact mul_le_mul_of_nonneg_right (hb θ hθ) (sEtaR_nonneg hθ)

/-- Integrability of `f · g · σ` on `Iθ` by AM–GM, from the `σ`-square integrability of `f`
and of `g`. -/
theorem integrableOn_mul_mul_sEtaR {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hgm : AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hf : IntegrableOn (fun θ => (f θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ)
    (hg : IntegrableOn (fun θ => (g θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => f θ * g θ * sEtaR θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2))
    ((hfm.mul hgm).mul measurable_sEtaR.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσ0 : 0 ≤ sEtaR θ := sEtaR_nonneg hθ
  have hAM : |f θ| * |g θ| ≤ (1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2) := by
    nlinarith [sq_nonneg (|f θ| - |g θ|), abs_nonneg (f θ), abs_nonneg (g θ),
      sq_abs (f θ), sq_abs (g θ)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hσ0]
  calc |f θ| * |g θ| * sEtaR θ
      ≤ ((1 / 2) * ((f θ) ^ 2 + (g θ) ^ 2)) * sEtaR θ :=
        mul_le_mul_of_nonneg_right hAM hσ0
    _ = (1 / 2) * ((f θ) ^ 2 * sEtaR θ + (g θ) ^ 2 * sEtaR θ) := by ring

/-- `σ`-square integrability of a slice from the level-`0` honesty of the datum. -/
theorem integrableOn_sq_mul_sEtaR_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (g z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ := by
  have h1 := hm.1 z (le_of_lt hz)
  have h2 : IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * sEtaR θ)) Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => hkIntegrand_w α g hθ) measurableSet_Icc
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
  refine (h2.const_mul ((Work.Spaces.w z) ^ 2)⁻¹).congr ?_
  filter_upwards with θ
  show ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (g z θ ^ 2 * sEtaR θ))
    = g z θ ^ 2 * sEtaR θ
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw), one_mul]

/-- The `z²`-scaled version: honesty of `z² g` gives the `σ`-square integrability of `g`. -/
theorem integrableOn_sq_mul_sEtaR_of_HkMem_zsq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * g z θ)) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (g z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ := by
  have h := integrableOn_sq_mul_sEtaR_of_HkMem hm hz
  refine (h.const_mul (((z ^ 2) ^ 2))⁻¹).congr ?_
  filter_upwards with θ
  have hz0 : z ≠ 0 := ne_of_gt hz
  show ((z ^ 2) ^ 2)⁻¹ * ((z ^ 2 * g z θ) ^ 2 * sEtaR θ) = g z θ ^ 2 * sEtaR θ
  field_simp
  try ring

/-! ## The endpoint rates of an `AeData` slice -/

/-- **The endpoint rates of a slice.**  For a.e. `z`, an `AeData` slice has both endpoint
limits `0` (the left one by hypothesis, the right one by `AeSliceRightTendsto`) and bounded
derivative, hence `|u z θ| ≤ C min(θ, π/2-θ)` and `|∂_θu z θ| ≤ C`. -/
theorem aeSliceBound (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hl : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |u z θ| ≤ C * θ ∧ |u z θ| ≤ C * (Real.pi / 2 - θ)
          ∧ |Work.Spaces.pth u z θ| ≤ C := by
  filter_upwards [hl, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hlz hz0
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz0
  have hsmAll : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip h.smooth hz0 n
  have hrl := Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto α u G h z hz0
  have hmvt : ∀ {θ θ₀ : ℝ}, θ ∈ Set.Ioo 0 (Real.pi / 2) → θ₀ ∈ Set.Ioo 0 (Real.pi / 2) →
      |u z θ - u z θ₀| ≤ C * |θ - θ₀| := fun {θ θ₀} hθ hθ₀ =>
    Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound hsmAll hθ hθ₀
      (fun ξ hξ => (hC ξ hξ).2)
  refine ⟨C, hCpos, fun θ hθ => ⟨?_, ?_, (hC θ hθ).2⟩⟩
  · -- the rate at `θ = 0`, from `u → 0`
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hb : ∀ᶠ θ' in 𝓝[>] (0 : ℝ), |u z θ'| < ε := by
      have h1 := hlz (Metric.ball_mem_nhds (0 : ℝ) hε)
      filter_upwards [h1] with θ' hθ'
      simpa [Real.dist_eq] using hθ'
    have hlt : ∀ᶠ θ' in 𝓝[>] (0 : ℝ), θ' < θ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hθ.1] with θ' hθ'
      exact fun _ => hθ'
    have hcomb : ∀ᶠ θ' in 𝓝[>] (0 : ℝ), (0 < θ' ∧ θ' < θ) ∧ |u z θ'| < ε := by
      filter_upwards [hb, hlt, self_mem_nhdsWithin] with θ' h1 h2 h3
      exact ⟨⟨h3, h2⟩, h1⟩
    obtain ⟨θ', ⟨hθ'pos, hθ'lt⟩, hθ'ltε⟩ := hcomb.exists
    have hm := hmvt hθ ⟨hθ'pos, lt_trans hθ'lt hθ.2⟩
    have hdiff : |u z θ - u z θ'| ≤ C * θ := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < θ - θ')] at hm
      nlinarith [hm, hθ'pos, hCpos]
    calc |u z θ| = |(u z θ - u z θ') + u z θ'| := by ring_nf
      _ ≤ |u z θ - u z θ'| + |u z θ'| := abs_add_le _ _
      _ ≤ C * θ + ε := by linarith
  · -- the rate at `θ = π/2`, from the right limit
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hb : ∀ᶠ θ' in 𝓝[<] (Real.pi / 2), |u z θ'| < ε := by
      have h1 := hrl (Metric.ball_mem_nhds (0 : ℝ) hε)
      filter_upwards [h1] with θ' hθ'
      simpa [Real.dist_eq] using hθ'
    have hgt : ∀ᶠ θ' in 𝓝[<] (Real.pi / 2), θ < θ' := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds hθ.2] with θ' hθ'
      exact fun _ => hθ'
    have hcomb : ∀ᶠ θ' in 𝓝[<] (Real.pi / 2), (θ < θ' ∧ θ' < Real.pi / 2) ∧ |u z θ'| < ε := by
      filter_upwards [hb, hgt, self_mem_nhdsWithin] with θ' h1 h2 h3
      exact ⟨⟨h2, h3⟩, h1⟩
    obtain ⟨θ', ⟨hθ'gt, hθ'lt⟩, hθ'ltε⟩ := hcomb.exists
    have hθ'pos : 0 < θ' := lt_trans hθ.1 hθ'gt
    have hm := hmvt ⟨hθ'pos, hθ'lt⟩ hθ
    rw [abs_sub_comm (u z θ') (u z θ), abs_sub_comm θ' θ] at hm
    have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
    have hdiff : |u z θ - u z θ'| ≤ C * (Real.pi / 2 - θ) := by
      rw [abs_of_neg (by linarith : θ - θ' < 0)] at hm
      nlinarith [hm, hθ'gt, hCpos, hπ2]
    calc |u z θ| = |(u z θ - u z θ') + u z θ'| := by ring_nf
      _ ≤ |u z θ - u z θ'| + |u z θ'| := abs_add_le _ _
      _ ≤ C * (Real.pi / 2 - θ) + ε := by linarith

/-! ## The `σ`-weighted slice integrability -/

/-- **The `σ`-weighted integrability of the slice pairings.**  For every `z > 0` the five
integrands appearing in the equation and in the `L₀`-self-form are `θ`-integrable against
`sEta`. -/
theorem aeSliceSigmaInt (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2 * sEtaR θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.pz u z θ * sEtaR θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.pzIter 2 u z θ * sEtaR θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * sEtaR θ)
        Work.Spaces.Iθ := by
  intro z hz
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  have hsmu : AEStronglyMeasurable (fun θ => (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aesm_of_contOn_Ioo (contOn_slice h hz)).pow 2
  have hsmd : AEStronglyMeasurable (fun θ => (Work.Spaces.pth u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aesm_of_contOn_Ioo (contOn_slice_pth h hz)).pow 2
  have hsmu' : AEStronglyMeasurable (fun θ => u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_of_contOn_Ioo (contOn_slice h hz)
  have hsmz : AEStronglyMeasurable (fun θ => Work.Spaces.pz u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_of_contOn_Ioo (contOn_slice_pz h hz)
  have hsmz2 : AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_of_contOn_Ioo (contOn_slice_pzIter2 h hz)
  -- (1) `u²σ`
  have h1 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (integrableOn_sEtaR.const_mul (C ^ 2))
      (hsmu.mul measurable_sEtaR.aestronglyMeasurable) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : (u z θ) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).1 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEtaR_nonneg hθI))]
    exact mul_le_mul_of_nonneg_right h2 (sEtaR_nonneg hθI)
  -- (2) `(∂_θu)²σ`
  have h2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2 * sEtaR θ)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (integrableOn_sEtaR.const_mul (C ^ 2))
      (hsmd.mul measurable_sEtaR.aestronglyMeasurable) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hb : (Work.Spaces.pth u z θ) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).2 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEtaR_nonneg hθI))]
    exact mul_le_mul_of_nonneg_right hb (sEtaR_nonneg hθI)
  -- (3) `u · ∂_zu · σ`
  have hg : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2 * sEtaR θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.H2W.Ae.AeGSlice α u G h z hz
  have h3 : MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.pz u z θ * sEtaR θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_mul_sEtaR hsmu' hsmz h1 hg
  -- (4) `u · ∂_z²u · σ`
  have hg2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ :=
    integrableOn_sq_mul_sEtaR_of_HkMem_zsq h.memRad2 hz
  have h4 : MeasureTheory.IntegrableOn (fun θ => u z θ * Work.Spaces.pzIter 2 u z θ * sEtaR θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_mul_sEtaR hsmu' hsmz2 h1 hg2
  -- (5) `(L₀u) · u · σ`
  have hG : MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * sEtaR θ) Work.Spaces.Iθ :=
    integrableOn_sq_mul_sEtaR_of_HkMem h.memG hz
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ * sEtaR θ) Work.Spaces.Iθ :=
    integrableOn_mul_mul_sEtaR (aesm_slice_G h hz) hsmu' hG h1
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
        = G z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
    intro θ hθ
    have hb := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    have hL : Work.Elliptic.Lzero u z θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ := by
      rw [Work.Elliptic.Lzero_eq_deriv, Work.FTS.EllipticEst.Lzero1]
    rw [hL] at hb
    linear_combination hb
  have h5 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * sEtaR θ)
      Work.Spaces.Iθ := by
    have hsum : MeasureTheory.IntegrableOn
        (fun θ => (G z θ * u z θ * sEtaR θ)
          + ((α ^ 2 * z ^ 2) * (u z θ * Work.Spaces.pzIter 2 u z θ * sEtaR θ))
          + ((α * (5 + α) * z) * (u z θ * Work.Spaces.pz u z θ * sEtaR θ)))
        Work.Spaces.Iθ :=
      (hGu.add (h4.const_mul (α ^ 2 * z ^ 2))).add (h3.const_mul (α * (5 + α) * z))
    refine hsum.congr ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    rw [hpt θ hθ]
    ring
  exact ⟨h1, h2, h3, h4, h5⟩

end Work.FTS.EllipticEst.H2W.AeProof.AeSigma
