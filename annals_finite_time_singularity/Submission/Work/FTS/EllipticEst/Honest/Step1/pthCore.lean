/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.EllipticEst.Honest.Step1.pthCore`

For every honest pair `(F,Ψ)` (`Hon α F Ψ`, `0 < α ≤ 1/4`) the first angular derivative
`∂_θΨ` is honest and

`√(HkSq α 0 (∂_θΨ)) ≤ C (√(HkSq α 0 F) + α √(HkSq α 0 (z ∂_zΨ)))`

with a universal constant `C`.

## Route

Write `σ θ = sin(2θ)^{-η}` (`η = 99/100`), `w z = (1+z)²/z²`, and

* `X = ∫∫ (∂_θΨ)² σ w² = HkSq α 0 (∂_θΨ)`,
* `Y = ∫∫ Ψ² σ w² = HkSq α 0 Ψ`,
* `Q = ∫∫ F² σ w² = HkSq α 0 F`.

1. **The `Ψ`-bound.**  `Honest.HR2.hon_to_ae` puts `(F,Ψ)` in the almost-everywhere class
   `H2W.Ae.AeData`; `Dispatch.hkMem_uM` gives `HkMem α 0 Ψ`; the *unweighted* first-order
   energy inequality of Step 1 of `prop:H2` (`AeS1.unwEnergyD`,
   `α²⟦(z∂_zΨ·w)²⟧ + ⟦(∂_θΨ·w)²⟧ ≤ C HkSq α 0 F`) together with the `σ`-upgrade of the mass
   (`H2W.AeProof.AeSigmaUpgradeU_all`, `⟦w²σΨ²⟧ ≤ C ⟦w²(∂_θΨ)²⟧`, and `σ ≥ 1` a.e. to make the
   unweighted `⟦⟧` finite, via `AeS1.l2Dictionary`) gives `Y ≤ C₁ Q`.
2. **The `σ`-weighted energy inequality for `∂_θΨ`.**  `AngAWeak.aeSigmaSliceCoercive` is
   exactly the slicewise `σ`-coercivity hypothesis of `AngAWeak.aeSigmaEnergyIneq`, which
   therefore gives `⟦α² z²(∂_zΨ)²σ⟧ + ⟦w²(∂_θΨ)²σ⟧ ≤ C₂ (⟦w²σΨ²⟧ + Q)`; throwing away the
   nonnegative first term and using step 1, `X ≤ C₂ (C₁ + 1) Q`.
3. **Honesty of `∂_θΨ`.**  `hkMem_pth_of_aeData` recovers the per-slice integrability from the
   second angular derivative (`AeData.memAng2`) by the weighted interpolation inequality
   `Honest.sliceInterp`.
4. **Arithmetic.**  `√X ≤ √(C₂(C₁+1)) √Q ≤ √(C₂(C₁+1)) (√Q + α √(HkSq α 0 (z∂_zΨ)))`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HR2.HonToAe
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaEnergyIneq
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.AeS1.l2Dictionary
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.Step1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-! ## Small elementary facts -/

/-- Almost every `θ ∈ Iθ` lies in the open interval. -/
theorem ae_mem_Ioo_Iθ_fts :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hEq : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  rw [hEq]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `1 ≤ σ θ = sin(2θ)^{-η}` on the open interval. -/
theorem one_le_sEta_Ioo_fts {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hz : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hpos hle hz
  rw [Work.FTS.EllipticEst.sEta]
  simpa only [Real.one_rpow] using h

/-- **The unweighted angular pairing is dominated by the `σ`-weighted one** (because
`σ ≥ 1` almost everywhere on `Iθ`). -/
theorem lintegral_unweighted_le_sigma (f : ℝ → ℝ → ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)))
      ≤ (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) := by
  refine MeasureTheory.lintegral_mono fun z => ?_
  refine mul_le_mul_of_nonneg_left ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_Ioo_fts hθ
  have h2 : (0 : ℝ) ≤ (f z θ) ^ 2 := sq_nonneg _
  calc (f z θ) ^ 2 = 1 * (f z θ) ^ 2 := (one_mul _).symm
    _ ≤ Work.FTS.EllipticEst.sEta θ * (f z θ) ^ 2 := mul_le_mul_of_nonneg_right h1 h2
    _ = (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_comm _ _

/-- **The `σ`-weighted slice identity**: `∫_θ HkIntegrand α 0 g z θ = w z² ∫_θ g z θ² σ θ`. -/
theorem slice_HkIntegrand_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α g hθ]

/-- The iterated angular derivative of a fibre. -/
theorem pthIter_two_eq_deriv_fts (u : ℝ → ℝ → ℝ) (z : ℝ) : ∀ θ : ℝ,
    Work.Spaces.pthIter 2 u z θ
      = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
  intro θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-! ## The honesty of `∂_θu` in the a.e. class -/

/-- **`HkMem α 0 (∂_θu)` for an `AeData` datum whose mass is honest.**  The per-slice
integrability comes from the weighted interpolation inequality `Honest.sliceInterp` applied to
the fibres (whose `σ`-square-integrable second derivative is `AeData.memAng2`), and the outer
integrability by domination. -/
theorem hkMem_pth_of_aeData {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmu : Work.Spaces.HkMem α 0 u) :
    Work.Spaces.HkMem α 0 (Work.Spaces.pth u) := by
  have hw0sq : (Work.Spaces.w (0 : ℝ)) ^ 2 = 0 := by
    rw [Work.Spaces.w]; norm_num
  -- the per-slice integrability of `(∂_θθu z)² σ`
  have hderiv2 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    intro z hz
    have hmem := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz
    refine hmem.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [pthIter_two_eq_deriv_fts u z θ]
  have hsm : ∀ z : ℝ, 0 < z → ContDiffOn ℝ 2 (fun θ : ℝ => u z θ)
      (Set.Ioo 0 (Real.pi / 2)) := fun z hz =>
    Work.FTS.EllipticEst.Honest.contDiffOn_slice u hz (h.smooth 2)
  have hfib : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := fun z hz =>
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ : ℝ => u z θ) (hsm z hz)
      (Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmu hz) (hderiv2 z hz)).1
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      refine (MeasureTheory.integrableOn_const (C := (0 : ℝ)) ?_ (by simp)).congr_fun
        ?_ measurableSet_Icc
      · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · intro θ hθ
        show (0 : ℝ) = Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) 0 θ
        rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α (Work.Spaces.pth u) hθ, hw0sq]
        ring
    · refine ((hfib z hzpos).const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α (Work.Spaces.pth u) hθ]
  · -- the outer integrability, by domination
    have hpt : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) z θ)
          ≤ 10000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)) := by
      intro z hz
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
      · subst hz0
        rw [slice_HkIntegrand_eq α (Work.Spaces.pth u) 0, slice_HkIntegrand_eq α u 0,
          slice_HkIntegrand_eq α (Work.Spaces.pthIter 2 u) 0, hw0sq]
        norm_num
      · have hsb := (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ : ℝ => u z θ)
          (hsm z hzpos) (Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hmu hzpos)
          (hderiv2 z hzpos)).2
        have hsb' : (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            ≤ 10000 * ((∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)) := by
          simpa only [Work.Spaces.pth, pthIter_two_eq_deriv_fts u z,
            Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta] using hsb
        rw [slice_HkIntegrand_eq α (Work.Spaces.pth u) z, slice_HkIntegrand_eq α u z,
          slice_HkIntegrand_eq α (Work.Spaces.pthIter 2 u) z]
        have h1 := mul_le_mul_of_nonneg_left hsb' (sq_nonneg (Work.Spaces.w z))
        calc (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
            ≤ (Work.Spaces.w z) ^ 2 * (10000 * ((∫ θ in Work.Spaces.Iθ,
                  (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
                + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ))) := h1
          _ = 10000 * (((Work.Spaces.w z) ^ 2
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
              + ((Work.Spaces.w z) ^ 2
                * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ))) := by ring
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
        Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
      have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth u) := hSO.pth
      have hcont : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hSOp α 0
      exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    have hbound_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) z θ‖
          ≤ 10000 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
            + (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth u) z θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pth u) z θ)
      rw [Real.norm_of_nonneg hnn]
      exact hpt z hz
    exact MeasureTheory.Integrable.mono' ((hmu.2.add h.memAng2.2).const_mul 10000)
      haesm hbound_ae

/-! ## The target -/

theorem pthCore : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0
                (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨Cup, hCuppos, hCup⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  obtain ⟨Cunw, hCunwpos, hCunw⟩ := Work.FTS.EllipticEst.AeS1.unwEnergyD
  obtain ⟨Csig, hCsigpos, hCsig⟩ :=
    Work.FTS.EllipticEst.AngAWeak.aeSigmaEnergyIneq
      Work.FTS.EllipticEst.AngAWeak.aeSigmaSliceCoercive
  refine ⟨max 1 (Real.sqrt (Csig * (Cup * Cunw + 1))), ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  · intro α F Ψ h
    have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
      Work.FTS.EllipticEst.Honest.HR2.hon_to_ae h
    have hmemΨ : Work.Spaces.HkMem α 0 Ψ :=
      Work.FTS.EllipticEst.Dispatch.hkMem_uM α Ψ F hAe
    have hmemP : Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) :=
      hkMem_pth_of_aeData hAe hmemΨ
    set Q : ℝ := Work.Spaces.HkSq α 0 F with hQ
    set Y : ℝ := Work.Spaces.HkSq α 0 Ψ with hY
    set X : ℝ := Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ) with hX
    have hQ0 : 0 ≤ Q := by rw [hQ]; exact Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α F
    have hY0 : 0 ≤ Y := by rw [hY]; exact Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α Ψ
    have hX0 : 0 ≤ X := by
      rw [hX]; exact Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α (Work.Spaces.pth Ψ)
    -- the `∫⁻`-form of the σ-weighted mass of `Ψ` and of `∂_θΨ`
    have hYsig : ENNReal.ofReal Y
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
      rw [hY]
      exact Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral α Ψ hmemΨ
    have hPsig : ENNReal.ofReal X
        = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)) := by
      rw [hX]
      exact Work.FTS.EllipticEst.H2W.AeU2.ofReal_HkSq_eq_lintegral α (Work.Spaces.pth Ψ) hmemP
    -- `σ ≥ 1` a.e. makes the unweighted `∫⁻` finite
    have hcomp : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)))
        ≤ ENNReal.ofReal X := by
      rw [hPsig]
      exact lintegral_unweighted_le_sigma (Work.Spaces.pth Ψ)
    have hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcomp
    -- the unweighted `L²`-norm of `∂_θΨ·w` is the unweighted `∫⁻`
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.pth Ψ p.1 p.2 * Work.Spaces.w p.1) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ) :=
        (Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth).pth
      have hp : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth Ψ p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.EllipticEst.SmoothOpen.forall hSOp 0).continuousOn
      have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
        simp only [Work.Spaces.w]
        exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
          (continuousOn_fst.pow 2) (fun p hp => by
            have h1 : (0 : ℝ) < p.1 := hp.1
            exact pow_ne_zero 2 (ne_of_gt h1))
      exact Work.Spaces.aesm_of_continuousOn_Qd _ ((hp.mul hw).pow 2)
    obtain ⟨hL2mem, hL2grad, hunwbnd⟩ := hCunw α Ψ F hAe
    have hunwbnd' : α ^ 2 * Work.Spaces.L2Sq
          (fun z θ => z * Work.Spaces.pz Ψ z θ * Work.Spaces.w z)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth Ψ z θ * Work.Spaces.w z)
        ≤ Cunw * Q := hunwbnd
    obtain ⟨_hL2gradUnw, hpsiEq⟩ :=
      Work.FTS.EllipticEst.AeS1.l2Dictionary hmeas hL2grad.1 hfin
    have hL2nn : 0 ≤ Work.Spaces.L2Sq
        (fun z θ => z * Work.Spaces.pz Ψ z θ * Work.Spaces.w z) := by
      rw [Work.Spaces.L2Sq]
      exact integral_nonneg (fun z => integral_nonneg (fun θ => sq_nonneg _))
    have hL2le : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth Ψ z θ * Work.Spaces.w z)
        ≤ Cunw * Q := by
      have h1 : α ^ 2 * Work.Spaces.L2Sq
            (fun z θ => z * Work.Spaces.pz Ψ z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth Ψ z θ * Work.Spaces.w z)
          ≤ Cunw * Q := hunwbnd'
      nlinarith [h1, mul_nonneg (sq_nonneg α) hL2nn]
    have hPsiSq_le : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)))
        ≤ ENNReal.ofReal (Cunw * Q) := by
      have htoReal : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))).toReal ≤ Cunw * Q := by
        rw [← hpsiEq]
        exact hL2le
      calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)))
          = ENNReal.ofReal ((∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))).toReal) :=
            (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal (Cunw * Q) := ENNReal.ofReal_le_ofReal htoReal
    -- ### Step 1: the `Ψ`-bound
    have hYle : Y ≤ Cup * (Cunw * Q) := by
      have hup := hCup α Ψ F hAe
      rw [← hYsig] at hup
      have hup' : ENNReal.ofReal Y ≤ ENNReal.ofReal (Cup * (Cunw * Q)) := by
        calc ENNReal.ofReal Y
            ≤ ENNReal.ofReal Cup
              * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))) := hup
          _ ≤ ENNReal.ofReal Cup * ENNReal.ofReal (Cunw * Q) :=
              mul_le_mul' le_rfl hPsiSq_le
          _ = ENNReal.ofReal (Cup * (Cunw * Q)) := (ENNReal.ofReal_mul hCuppos.le).symm
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hCuppos.le (mul_nonneg hCunwpos.le hQ0))).mp hup'
    -- ### Step 2: the `σ`-weighted energy inequality
    have hsig := hCsig α Ψ F hAe
    have hsig' : ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pz Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)))
        + ENNReal.ofReal X
        ≤ ENNReal.ofReal Csig * (ENNReal.ofReal Y + ENNReal.ofReal Q) := by
      rw [← hPsig, ← hYsig, ← hQ] at hsig
      exact hsig
    have hXle : X ≤ Csig * (Cup * (Cunw * Q) + Q) := by
      have h1 : ENNReal.ofReal X
          ≤ ENNReal.ofReal Csig * (ENNReal.ofReal Y + ENNReal.ofReal Q) :=
        le_trans (le_add_of_nonneg_left bot_le) hsig'
      have h3 : ENNReal.ofReal Csig * (ENNReal.ofReal Y + ENNReal.ofReal Q)
          = ENNReal.ofReal (Csig * (Y + Q)) := by
        rw [← ENNReal.ofReal_add hY0 hQ0, ← ENNReal.ofReal_mul hCsigpos.le]
      have h4 : ENNReal.ofReal X ≤ ENNReal.ofReal (Csig * (Y + Q)) := by
        rw [← h3]; exact h1
      have h5 : X ≤ Csig * (Y + Q) :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCsigpos.le (add_nonneg hY0 hQ0))).mp h4
      have hYQ : Y + Q ≤ Cup * (Cunw * Q) + Q := by linarith [hYle]
      exact le_trans h5 (mul_le_mul_of_nonneg_left hYQ hCsigpos.le)
    -- ### Step 3: arithmetic
    refine ⟨hmemP, ?_⟩
    have hK : Csig * (Cup * (Cunw * Q) + Q) = Csig * (Cup * Cunw + 1) * Q := by ring
    rw [hK] at hXle
    have hKnn : 0 ≤ Csig * (Cup * Cunw + 1) :=
      mul_nonneg hCsigpos.le (by nlinarith [hCuppos, hCunwpos])
    rw [hX, hQ]
    have hs1 : Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pth Ψ))
        ≤ Real.sqrt (Csig * (Cup * Cunw + 1)) * Real.sqrt (Work.Spaces.HkSq α 0 F) := by
      rw [← Real.sqrt_mul hKnn]
      exact Real.sqrt_le_sqrt hXle
    refine hs1.trans ?_
    have hsQ : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 F) := Real.sqrt_nonneg _
    have hsG : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :=
      Real.sqrt_nonneg _
    have hCge : Real.sqrt (Csig * (Cup * Cunw + 1))
        ≤ max 1 (Real.sqrt (Csig * (Cup * Cunw + 1))) := le_max_right _ _
    have hCnn : 0 ≤ max 1 (Real.sqrt (Csig * (Cup * Cunw + 1))) :=
      le_trans zero_le_one (le_max_left _ _)
    have hα0 : 0 ≤ α := h.hα.le
    calc Real.sqrt (Csig * (Cup * Cunw + 1)) * Real.sqrt (Work.Spaces.HkSq α 0 F)
        ≤ max 1 (Real.sqrt (Csig * (Cup * Cunw + 1)))
            * Real.sqrt (Work.Spaces.HkSq α 0 F) :=
          mul_le_mul_of_nonneg_right hCge hsQ
      _ ≤ max 1 (Real.sqrt (Csig * (Cup * Cunw + 1)))
            * (Real.sqrt (Work.Spaces.HkSq α 0 F)
              + α * Real.sqrt (Work.Spaces.HkSq α 0
                  (fun z θ => z * Work.Spaces.pz Ψ z θ))) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (mul_nonneg hα0 hsG)) hCnn

end Work.FTS.EllipticEst.Honest.Step1
