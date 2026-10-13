import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.slicePairIneqFluxFree
import Submission.Work.FTS.EllipticEst.H2W.SlotA.sharpHardyOpen
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_A_integrable
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceA
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1WMSliceB
-- (inherited from the pre-split file: the chunks need the transitive imports of the module
-- `AeI1Fts/I1Paper_mixed` for such names as `contDiffOn_slice_U`)
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1Paper_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Split out of `AeI1Fts/I1PaperWeakMixed.lean`: the `z`-integrated outer bounds and the
leaf theorem `I1PaperWeakMixed`.  Names and namespace are unchanged. -/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- **Step 2 of the truncation route: the per-`z` slice bound, integrated in `z`.**

The per-`z` bound `slice_second_le_cut_auto` holds for *every* `z`, so multiplying it by the
nonnegative weight `w(z)²χ(z)` and integrating in `z` is legitimate as soon as the two sides are
`z`-integrable.  Here `χ` is an arbitrary nonnegative weight on `Iz`; in the intended application
`χ ∈ C_c^∞((0,∞))` is the radial cutoff whose support keeps `w²χ` bounded. -/
theorem Upsi_slice_bound_integrated (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hχ : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hψ : ContDiff ℝ 2 ψ)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (hL : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * (∫ θ in Iθo, (U u z θ * ψ θ)
            * deriv (deriv (fun θ' => U u z θ' * ψ θ')) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iz)
    (hR : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * (2 * Work.Spaces.eta
              * (∫ θ in Iθo, (U u z θ * ψ θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
              * (∫ θ in Iθo,
                  (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * χ z
        * (∫ θ in Iθo, (U u z θ * ψ θ)
            * deriv (deriv (fun θ' => U u z θ' * ψ θ')) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * χ z
        * (2 * Work.Spaces.eta
              * (∫ θ in Iθo, (U u z θ * ψ θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
              * (∫ θ in Iθo,
                  (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
  have h2le : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  refine MeasureTheory.integral_mono_ae hL hR ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  have hslice : ContDiffOn ℝ 2 (fun θ => U u z θ) Iθo := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · have hzero : (fun θ => U u z θ) = fun _ => (0 : ℝ) := by
        funext θ
        rw [← hz0]
        simp only [U, zero_mul]
      rw [hzero]
      exact contDiffOn_const
    · exact (contDiffOn_slice_U hS hzpos).of_le h2le
  exact mul_le_mul_of_nonneg_left (slice_second_le_cut_auto _ ψ hslice hψ hsep)
    (mul_nonneg (sq_nonneg _) (hχ z hz))

/-- **Step 2, packaged: the truncated slice bound with the right-hand side discharged.**

This is `Upsi_slice_bound_integrated` with `hR` supplied by the two domination lemmas
`Upsi_A_integrable_of_smooth` (the `∫_θσ(Uψ)²` half, from `HkMem α 0 (grad u)`) and
`Upsi_P_integrable_ae` (the `∫_θσ((Uψ)')²` half, from `HkMem α 0 (grad u)` + the a.e. slicewise
hypothesis (3) + the unweighted `z`-finiteness (4)).

The only hypothesis that is *not* a consequence of the target's hypotheses is `hL`, the
`z`-integrability of the left-hand side `z ↦ w²χ ∫_θσ (Uψ)(Uψ)''` — see
`NOTES_I1PaperWeakMixed.md` §"Step 2" for why it is genuinely stronger than what the hypotheses
give (the `𝓗`-slot), and for the case analysis that disposes of it in the final assembly. -/
theorem Upsi_bound_integrated (α : ℝ) (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hV : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (hZ : MeasureTheory.IntegrableOn
      (fun z => z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz)
    (hχm : Measurable χ) (hχnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hχb : ∃ C : ℝ, ∀ z ∈ Work.Spaces.Iz, χ z ≤ C)
    (hχw : ∃ C : ℝ, ∀ z ∈ Work.Spaces.Iz, χ z * (1 + z) ^ 4 ≤ C * z ^ 4)
    (hψcd : ContDiff ℝ 2 ψ)
    (hψb : ∃ C : ℝ, ∀ θ, (ψ θ) ^ 2 ≤ C)
    (hψb' : ∃ C : ℝ, ∀ θ, (deriv ψ θ) ^ 2 ≤ C)
    (hsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (hL : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * (∫ θ in Iθo, (U u z θ * ψ θ)
            * deriv (deriv (fun θ' => U u z θ' * ψ θ')) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * χ z
        * (∫ θ in Iθo, (U u z θ * ψ θ)
            * deriv (deriv (fun θ' => U u z θ' * ψ θ')) θ
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * χ z
        * (2 * Work.Spaces.eta
              * (∫ θ in Iθo, (U u z θ * ψ θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
              * (∫ θ in Iθo,
                  (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
  -- the two halves of the right-hand side are `z`-integrable
  have hAint := Upsi_A_integrable_of_smooth α u χ ψ hS hU hχm hχnn hχb
    hψcd.continuous.measurable (hψb.imp (fun C hC θ _ => hC θ))
  have hPint := Upsi_P_integrable_ae α u χ ψ hS hU hV hZ hχm hχnn hχw hψcd hψb hψb'
  -- transfer the `Iθ`-integrals to the `Iθo`-integrals of the slice bound
  have hAeq : (fun z => (Work.Spaces.w z) ^ 2 * χ z
      * ∫ θ in Iθo, (U u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ, (U u z θ * ψ θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    funext z
    refine congrArg (fun t => (Work.Spaces.w z) ^ 2 * χ z * t) ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))
  have hPeq : (fun z => (Work.Spaces.w z) ^ 2 * χ z
      * ∫ θ in Iθo, (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    funext z
    refine congrArg (fun t => (Work.Spaces.w z) ^ 2 * χ z * t) ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))
  have hAint' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Iθo, (U u z θ * ψ θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz := by
    rw [hAeq]; exact hAint
  have hPint' : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Iθo, (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz := by
    rw [hPeq]; exact hPint
  refine Upsi_slice_bound_integrated u χ ψ hS hχnn hψcd hsep hL ?_
  refine ((hAint'.const_mul (2 * Work.Spaces.eta)).sub
    (hPint'.const_mul ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)))).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z _
  simp only [Pi.sub_apply]
  ring

theorem I1PaperWeakMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by sorry

end

end Work.FTS.EllipticEst.AeI1Fts