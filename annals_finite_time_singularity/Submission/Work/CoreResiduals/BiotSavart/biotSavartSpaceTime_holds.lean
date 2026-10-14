import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.fderiv_extField_eq_farBlock
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radGreen_general_bound
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le
import Submission.Work.StabilityFar.St5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Metric Filter Topology Set
open scoped Topology
open Work.LWP

namespace Work.CoreResiduals.BiotSavart

/-! ## The core-strip `C^{1,α}` statement

The two `sorry`-free inputs of the final assembly are

* `Work.CoreResiduals.BiotSavart.fderiv_extField_eq_farBlock` — the within-derivative on the core
  strip is `farBlock ω` (read off from the two-sided extension `windowExt ω S`, whose `C¹`
  statement is `biotSavartSpacetimeC1_of_dtContinuous`);
* `Work.CoreResiduals.BiotSavart.bundleSliceFderiv_holder` — the *uniform-in-`t`* single-slice
  Schauder estimate `ω ∈ C^{0,α} ⟹ ∇BS ω ∈ C^{0,α}` for the slices of a strip-bundle vorticity.

Everything else is assembled here: boundedness of `farBlock ω` on the core strip
(`norm_bsDerivCLM_le_of_bdd_holder` for the spatial block,
`biotSavart_norm_le_of_bounded_supported` for the time block), the joint `α`-Hölder estimate for
`farBlock ω` on the core strip (`norm_farBlock_sub_le` splits it into the spatial and time blocks;
the spatial block is `bundleSliceFderiv_holder` + `biotSavart_fderiv_timeHolder_of_bundle`, the time
block is `biotSavart_holder_le_sup` applied to `∂ₜω` resp. to the difference of two `∂ₜ`-slices),
and finally the gluing of the core and far estimates. -/

/-- **The core-strip `C^{1,α}` statement.** -/
theorem biotSavart_coreStrip_holder {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    IsContDiffHolderOn ℝ α (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
      (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S) := by
  have hRpos : 0 < R := hbun.1.1
  have hρ' : 0 < 2 * R + 10 := by linarith
  -- unpack the bundle once and for all
  have hbun0 : Work.CoreResiduals.BSAdmissibleStripFull α ω R S := hbun
  obtain ⟨⟨hRpos', hsupp, ⟨M, hM⟩, ⟨H, hH⟩, ⟨N, hN⟩, hmeas⟩,
    ⟨hdc, ⟨M₁, hM₁⟩, hmeasD⟩, ⟨N₁, hN₁⟩⟩ := hbun
  -- ### uniqueness of the within-derivative on the core strip
  have huniq : ∀ p ∈ Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S,
      UniqueDiffWithinAt ℝ (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S) p := by
    intro p hp
    obtain ⟨hpx, hpt⟩ := hp
    refine UniqueDiffWithinAt.prod ?_ (uniqueDiffOn_Icc hS p.2 hpt)
    have hball : Work.StabilityFar.coreRegion (2 * R + 10)
        = Metric.closedBall (0 : Work.LWP.R3) (2 * R + 10) := by
      ext y
      rw [Work.StabilityFar.mem_coreRegion, Metric.mem_closedBall, dist_eq_norm]
      simp
    rw [hball] at hpx ⊢
    refine uniqueDiffWithinAt_convex (convex_closedBall _ _) ?_ (subset_closure hpx)
    rw [interior_closedBall _ (ne_of_gt hρ')]
    exact ⟨0, by simp [Metric.mem_ball, hρ']⟩
  -- ### the within-derivative on the core strip is `farBlock`
  have hfw : ∀ p ∈ Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S,
      fderivWithin ℝ (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
          (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S) p
        = farBlock ω p := by
    intro p hp
    have hpS : p ∈ Set.univ ×ˢ Set.Icc (0:ℝ) S := ⟨trivial, hp.2⟩
    have hcd : ContDiffAt ℝ 1 (extField ω S) p := by
      obtain ⟨hadmw, hdtcw⟩ :=
        windowExt_windowBundle hα hS hbun0 (timeDeriv_xHolderOn_general hα hS hbun0)
      refine biotSavartSpacetimeC1_of_dtContinuous (ω := windowExt ω S) (R := R) (T := S + 1)
        hadmw hdtcw p.1 p.2 ?_
      change p.2 ∈ Set.Ioo (-2 : ℝ) (S + 1)
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hd : HasFDerivAt (extField ω S) (farBlock ω p) p := by
      rw [← fderiv_extField_eq_farBlock hα hS hbun0 p hpS]
      exact (hcd.differentiableAt one_ne_zero).hasFDerivAt
    have hagree : ∀ q ∈ Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S,
        (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) q
          = extField ω S q := by
      intro q hq
      have hfun : (fun y : Work.LWP.R3 => windowExt ω S y q.2) = (fun y => ω y q.2) :=
        funext fun y => windowExt_of_mem_Icc hq.2
      show Work.LWP.biotSavart (fun y => ω y q.2) q.1
        = Work.LWP.biotSavart (fun y => windowExt ω S y q.2) q.1
      rw [hfun]
    have h2 : HasFDerivWithinAt
        (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1) (farBlock ω p)
        (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S) p :=
      hd.hasFDerivWithinAt.congr_of_eventuallyEq
        (Filter.mem_of_superset self_mem_nhdsWithin hagree) (hagree p hp)
    exact h2.fderivWithin (huniq p hp)
  -- ### the uniform bound for `farBlock` on the core strip
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀nn : 0 ≤ M₀ := by rw [hM₀def]; exact le_max_right _ _
  set M₁₀ : ℝ := max M₁ 0 with hM₁₀def
  have hM₁₀nn : 0 ≤ M₁₀ := by rw [hM₁₀def]; exact le_max_right _ _
  set H₀ : ℝ := (H : ℝ) with hH₀def
  have hH₀nn : 0 ≤ H₀ := by rw [hH₀def]; positivity
  set ρ : ℝ := 3 * R + 11 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρnn : 0 ≤ ρ := hρpos.le
  -- the sup bound on the `kDerivCLM` of a slice
  have hCLM : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, ‖x‖ ≤ 2 * R + 10 →
      ‖bsDerivCLM (fun a => ω a t) ρ x‖
        ≤ 4 * (2 * M₀) ^ (α : ℝ) * (2 * (H₀ / 2)) ^ (1 - (α : ℝ)) *
            (4 * Real.pi * (ρ + ‖x‖) ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
          + (4 * Real.pi / 3) * M₀ := by
    intro t ht x hx
    refine norm_bsDerivCLM_le_of_bdd_holder (α := (α : ℝ)) (A := M₀) (H := H₀ / 2) (ρ := ρ)
      hα hα1 hM₀nn (by linarith) hρnn (fun a => ?_) (fun a b => ?_) x
    · exact le_trans (hM t ht a) (le_max_left _ _)
    · have h1 := (hH t ht).dist_le a b
      rw [dist_eq_norm, dist_eq_norm] at h1
      calc ‖ω a t - ω b t‖ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) := by rw [hH₀def]; exact h1
        _ = 2 * (H₀ / 2) * ‖a - b‖ ^ (α : ℝ) := by ring
  -- the derivative of a slice, via the Calderón–Zygmund identity
  have hfd : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, ‖x‖ ≤ 2 * R + 10 →
      fderiv ℝ (Work.LWP.biotSavart (fun a => ω a t)) x
        = (4 * Real.pi)⁻¹ • bsDerivCLM (fun a => ω a t) ρ x := by
    intro t ht x hx
    have hρx : R + ‖x‖ < ρ := by rw [hρdef]; linarith [norm_nonneg x]
    exact (hasFDerivAt_biotSavart_slice (ω := fun a => ω a t) (R := R) (M := M₀) (C := H₀)
      (c := (α : ℝ)) (ρ := ρ) hRpos hM₀nn hα (fun a => le_trans (hM t ht a) (le_max_left _ _))
      (fun a => hsupp t ht a) (hmeas t ht) (fun a b => by
        have h1 := (hH t ht).dist_le a b
        rw [dist_eq_norm, dist_eq_norm] at h1
        calc ‖ω a t - ω b t‖ ≤ H₀ * ‖a - b‖ ^ (α : ℝ) := by rw [hH₀def]; exact h1
          _ = H₀ * ‖a - b‖ ^ (α : ℝ) := rfl) hρx).fderiv
  -- the `∂ₜ`-block is bounded on the core strip
  have hBsupp : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R :=
    slicesSupportedStrip_timeDeriv hS hbun0
  have hDtbdd : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, ‖x‖ ≤ 2 * R + 10 →
      ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x‖
        ≤ M₁₀ * (2 * R + 10 + R + 1) := by
    intro t ht x hx
    have h1 := biotSavart_norm_le_of_bounded_supported (ω := fun y => FiniteTimeSingularity.timeDeriv ω y t)
      (R := R) (M := M₁₀) hRpos hM₁₀nn (fun y => le_trans (hM₁ t ht y) (le_max_left _ _))
      (fun y => hBsupp t ht y) (hmeasD t ht) x
    refine le_trans h1 ?_
    have hxle : ‖x‖ + R + 1 ≤ 2 * R + 10 + R + 1 := by linarith
    exact mul_le_mul_of_nonneg_left hxle hM₁₀nn
  set Bx : ℝ := 4 * (2 * M₀) ^ (α : ℝ) * (2 * (H₀ / 2)) ^ (1 - (α : ℝ)) *
      (4 * Real.pi * (ρ + (2 * R + 10)) ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ))))
      + (4 * Real.pi / 3) * M₀ with hBxdef
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ p ∈ Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S,
      ‖farBlock ω p‖ ≤ B := by
    refine ⟨(4 * Real.pi)⁻¹ * Bx + M₁₀ * (2 * R + 10 + R + 1), ?_⟩
    intro p hp
    have hp2 : p.2 ∈ Set.Icc (0:ℝ) S := hp.2
    have hpx : ‖p.1‖ ≤ 2 * R + 10 := Work.StabilityFar.mem_coreRegion.mp hp.1
    have hx1 : ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1‖
        ≤ (4 * Real.pi)⁻¹ * Bx := by
      rw [hfd p.2 hp2 p.1 hpx, norm_smul, Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hBxdef]
      refine le_trans (hCLM p.2 hp2 p.1 hpx) ?_
      refine add_le_add ?_ (le_refl _)
      have h1 : ρ + ‖p.1‖ ≤ ρ + (2 * R + 10) := by linarith [norm_nonneg p.1]
      have hexp : 0 < (α : ℝ) * (1 - (α : ℝ)) := mul_pos hα (by linarith)
      have h2 : (ρ + ‖p.1‖) ^ ((α : ℝ) * (1 - (α : ℝ)))
          ≤ (ρ + (2 * R + 10)) ^ ((α : ℝ) * (1 - (α : ℝ))) :=
        Real.rpow_le_rpow (by linarith [norm_nonneg p.1, hρpos]) h1 hexp.le
      have h3 : 4 * Real.pi * (ρ + ‖p.1‖) ^ ((α : ℝ) * (1 - (α : ℝ))) / ((α : ℝ) * (1 - (α : ℝ)))
          ≤ 4 * Real.pi * (ρ + (2 * R + 10)) ^ ((α : ℝ) * (1 - (α : ℝ)))
            / ((α : ℝ) * (1 - (α : ℝ))) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hexp.le
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hx2 : ‖(ContinuousLinearMap.snd ℝ Work.LWP.R3 ℝ).smulRight
        (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1)‖
        ≤ M₁₀ * (2 * R + 10 + R + 1) :=
      le_trans (norm_snd_smulRight_le _) (hDtbdd p.2 hp2 p.1 hpx)
    have hsplit : farBlock ω p
        = (fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1).comp
            (ContinuousLinearMap.fst ℝ Work.LWP.R3 ℝ)
          + (ContinuousLinearMap.snd ℝ Work.LWP.R3 ℝ).smulRight
              (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1) := rfl
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hx2
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have hfst : ‖ContinuousLinearMap.fst ℝ Work.LWP.R3 ℝ‖ ≤ 1 :=
      ContinuousLinearMap.norm_fst_le ℝ Work.LWP.R3 ℝ
    calc ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1‖
          * ‖ContinuousLinearMap.fst ℝ Work.LWP.R3 ℝ‖
        ≤ ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1‖ * 1 :=
          mul_le_mul_of_nonneg_left hfst (norm_nonneg _)
      _ = ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1‖ := mul_one _
      _ ≤ (4 * Real.pi)⁻¹ * Bx := hx1
  -- ### the Hölder bound for `farBlock` on the core strip
  obtain ⟨KB, hKBnn, hKB⟩ := bundleSliceFderiv_holder (R' := 2 * R + 10) hα hα1 hbun0
  obtain ⟨KC, hKCnn, hKC⟩ := biotSavart_fderiv_timeHolder_of_bundle (R' := 2 * R + 10) hα hα1 hbun0
  obtain ⟨KA, hKAnn, hKA⟩ := biotSavart_holder_le_sup (R := R) (R' := 2 * R + 10) (α := (α:ℝ))
    hRpos hα hα1
  set N₀ : ℝ := max N₁ 0 with hN₀def
  have hN₀nn : 0 ≤ N₀ := by rw [hN₀def]; exact le_max_right _ _
  have hhold : HolderOn α
      (fderivWithin ℝ (fun q : Work.LWP.R3 × ℝ => Work.LWP.biotSavart (fun y => ω y q.2) q.1)
        (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S))
      (Work.StabilityFar.coreRegion (2 * R + 10) ×ˢ Set.Icc (0:ℝ) S) := by
    set K : ℝ := max 0 (KB + KC + KA * M₁₀ + KA * N₀) with hKdef
    have hKnn : 0 ≤ K := by rw [hKdef]; exact le_max_left _ _
    refine ⟨Real.toNNReal K, Work.StabilityFar.Holder.holderOnWith_of_norm_le
      (C := Real.toNNReal K) ?_⟩
    intro p hp q hq
    rw [Real.coe_toNNReal K hKnn]
    have hd1 : ‖p.1 - q.1‖ ^ (α : ℝ) ≤ dist p q ^ (α : ℝ) := by
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hα.le
      rw [Prod.dist_eq, dist_eq_norm]
      exact le_max_left _ _
    have hd2 : |p.2 - q.2| ^ (α : ℝ) ≤ dist p q ^ (α : ℝ) := by
      refine Real.rpow_le_rpow (abs_nonneg _) ?_ hα.le
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have hdnn : 0 ≤ dist p q ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
    -- the four pieces
    have hA1 : ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
        - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1‖ ≤ KB * dist p q ^ (α : ℝ) := by
      refine le_trans (hKB p.2 hp.2 p.1 q.1 (Work.StabilityFar.mem_coreRegion.mp hp.1)
        (Work.StabilityFar.mem_coreRegion.mp hq.1)) ?_
      exact mul_le_mul_of_nonneg_left hd1 hKBnn
    have hA2 : ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1
        - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1‖ ≤ KC * dist p q ^ (α : ℝ) := by
      refine le_trans (hKC q.1 (Work.StabilityFar.mem_coreRegion.mp hq.1) p.2 hp.2 q.2 hq.2) ?_
      exact mul_le_mul_of_nonneg_left hd2 hKCnn
    have hB1 : ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
        - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1‖
        ≤ KA * M₁₀ * dist p q ^ (α : ℝ) := by
      have h := (hKA (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) M₁₀ hM₁₀nn
        (fun y => le_trans (hM₁ p.2 hp.2 y) (le_max_left _ _)) (fun y => hBsupp p.2 hp.2 y)
        (hmeasD p.2 hp.2)).2 p.1 q.1 (Work.StabilityFar.mem_coreRegion.mp hp.1)
        (Work.StabilityFar.mem_coreRegion.mp hq.1)
      exact le_trans h (mul_le_mul_of_nonneg_left hd1 (mul_nonneg hKAnn hM₁₀nn))
    have hB2 : ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1
        - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖
        ≤ KA * N₀ * dist p q ^ (α : ℝ) := by
      have hlin : Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1
          - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1
          = Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2
              - FiniteTimeSingularity.timeDeriv ω y q.2) q.1 := by
        have h := Work.StabilityFar.Decay.biotSavart_sub
          (f := fun y => FiniteTimeSingularity.timeDeriv ω y p.2)
          (g := fun y => FiniteTimeSingularity.timeDeriv ω y q.2) (R := R) (M := M₁₀)
          hRpos.le hM₁₀nn (fun y => le_trans (hM₁ p.2 hp.2 y) (le_max_left _ _))
          (fun y => le_trans (hM₁ q.2 hq.2 y) (le_max_left _ _))
          (fun y => hBsupp p.2 hp.2 y) (fun y => hBsupp q.2 hq.2 y)
          (hmeasD p.2 hp.2) (hmeasD q.2 hq.2) q.1
        exact h.symm
      have hGnn : 0 ≤ N₀ * |p.2 - q.2| ^ (α : ℝ) :=
        mul_nonneg hN₀nn (Real.rpow_nonneg (abs_nonneg _) _)
      have hbdd' : ∀ y : Work.LWP.R3, ‖FiniteTimeSingularity.timeDeriv ω y p.2
          - FiniteTimeSingularity.timeDeriv ω y q.2‖ ≤ N₀ * |p.2 - q.2| ^ (α : ℝ) := by
        intro y
        have h1 := hN₁ y p.2 hp.2 q.2 hq.2
        have h2 : N₁ ≤ N₀ := by rw [hN₀def]; exact le_max_left _ _
        calc ‖FiniteTimeSingularity.timeDeriv ω y p.2 - FiniteTimeSingularity.timeDeriv ω y q.2‖
            ≤ N₁ * |p.2 - q.2| ^ (α : ℝ) := h1
          _ ≤ N₀ * |p.2 - q.2| ^ (α : ℝ) :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (abs_nonneg _) _)
      have hsupp' : ∀ y : Work.LWP.R3, FiniteTimeSingularity.timeDeriv ω y p.2
          - FiniteTimeSingularity.timeDeriv ω y q.2 ≠ 0 → y ∈ Metric.closedBall 0 R := by
        intro y hy
        by_cases h1 : FiniteTimeSingularity.timeDeriv ω y p.2 = 0
        · refine hBsupp q.2 hq.2 y ?_
          intro hc
          exact hy (by simp only [h1, hc, sub_zero])
        · exact hBsupp p.2 hp.2 y h1
      have hmeas' : AEStronglyMeasurable (fun y : Work.LWP.R3 =>
          FiniteTimeSingularity.timeDeriv ω y p.2 - FiniteTimeSingularity.timeDeriv ω y q.2)
          volume := (hmeasD p.2 hp.2).sub (hmeasD q.2 hq.2)
      have h := (hKA (fun y => FiniteTimeSingularity.timeDeriv ω y p.2
        - FiniteTimeSingularity.timeDeriv ω y q.2) (N₀ * |p.2 - q.2| ^ (α : ℝ)) hGnn
        hbdd' hsupp' hmeas').1 q.1 (Work.StabilityFar.mem_coreRegion.mp hq.1)
      rw [hlin]
      refine le_trans h ?_
      have hstep : KA * (N₀ * |p.2 - q.2| ^ (α : ℝ)) ≤ KA * N₀ * dist p q ^ (α : ℝ) := by
        rw [show KA * (N₀ * |p.2 - q.2| ^ (α : ℝ)) = KA * N₀ * |p.2 - q.2| ^ (α : ℝ) from by ring]
        exact mul_le_mul_of_nonneg_left hd2 (mul_nonneg hKAnn hN₀nn)
      exact hstep
    rw [hfw p hp, hfw q hq]
    have hmain := norm_farBlock_sub_le ω p q
    have h1 : ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
        - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1‖
        ≤ (KB + KC) * dist p q ^ (α : ℝ) := by
      have hsplit : ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1‖
          ≤ ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
              - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1‖
            + ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1
              - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1‖ := by
        have heq : fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
              - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1
            = (fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
                - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1)
              + (fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) q.1
                - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1) := by abel
        rw [heq]
        exact norm_add_le _ _
      calc ‖fderiv ℝ (Work.LWP.biotSavart (fun a => ω a p.2)) p.1
            - fderiv ℝ (Work.LWP.biotSavart (fun a => ω a q.2)) q.1‖
          ≤ KB * dist p q ^ (α : ℝ) + KC * dist p q ^ (α : ℝ) :=
            le_trans hsplit (add_le_add hA1 hA2)
        _ = (KB + KC) * dist p q ^ (α : ℝ) := by ring
    have h2 : ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
        - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖
        ≤ (KA * M₁₀ + KA * N₀) * dist p q ^ (α : ℝ) := by
      have hsplit : ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
            - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖
          ≤ ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
              - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1‖
            + ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1
              - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖ := by
        have heq : Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
              - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1
            = (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
                - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1)
              + (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) q.1
                - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1) := by abel
        rw [heq]
        exact norm_add_le _ _
      calc ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y p.2) p.1
            - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y q.2) q.1‖
          ≤ KA * M₁₀ * dist p q ^ (α : ℝ) + KA * N₀ * dist p q ^ (α : ℝ) :=
            le_trans hsplit (add_le_add hB1 hB2)
        _ = (KA * M₁₀ + KA * N₀) * dist p q ^ (α : ℝ) := by ring
    calc ‖farBlock ω p - farBlock ω q‖
        ≤ (KB + KC) * dist p q ^ (α : ℝ) + (KA * M₁₀ + KA * N₀) * dist p q ^ (α : ℝ) :=
          le_trans hmain (add_le_add h1 h2)
      _ = (KB + KC + KA * M₁₀ + KA * N₀) * dist p q ^ (α : ℝ) := by ring
      _ ≤ K * dist p q ^ (α : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hdnn
          rw [hKdef]; exact le_max_right _ _
  -- ### assembly of the core statement
  refine ⟨?_, ?_, hhold⟩
  · refine (biotSavart_contDiffOn_strip hα hα1 hbun0).mono ?_
    intro q hq
    exact ⟨trivial, hq.2⟩
  · rw [IsBoundedFunOn, isBounded_iff_forall_norm_le]
    refine ⟨B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [hfw p hp]
    exact hB p hp

/-- **The space-time Schauder estimate of R2.**

Unfolding the definition (`Work.CoreResiduals.BiotSavartSpaceTime α`, which carries the range
`0 < α < 1`, the hypothesis `0 < S`, and the *full* bundle
`Work.CoreResiduals.BSAdmissibleStripFull α ω R S` = strip admissibility `BSAdmissibleStrip α ω R S`
+ the time-regularity `TimeDerivStrip ω S` + the second-order time-regularity
`TimeDerivStripHolder α ω S` of `∂ₜω`): for every strip vorticity

* supported in a fixed ball `B(0,R)`,
* uniformly bounded on `[0,S]`, uniformly `x`-Hölder of exponent `α` and uniformly Hölder in `t` of
  exponent `α` there, with ae-strongly-measurable slices,
* differentiable in `t` on the strip with uniformly bounded and measurable `∂ₜω`, and with
  `∂ₜω` itself Hölder in `t` of exponent `α`, uniformly in `x`,

the reconstructed velocity `q ↦ BS(ω(·,q.2))(q.1)` lies in `IsContDiffHolderOn ℝ α` on
`ℝ³ × [0,S]`.

Four `sorry`-free attempts at this path diagnosed and corrected the statement, and every correction
is now part of the definition: the range `0 < α < 1`, the hypothesis `0 < S` (at `S = 0` the strip is
thin and `fderivWithin` is opaque), the `t`-differentiability of the slices and the second-order
time-regularity of `∂ₜω` are all forced by the conclusion; this version's reviews confirmed the
bundle is sufficient as well as necessary.

This is the classical space-time Schauder estimate: `ω` is jointly `α`-Hölder on the strip, its
slices satisfy the hypotheses of the single-slice Calderón–Zygmund statement
`Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one` *uniformly in `t`* (the `x`-slot of
`fderivWithin` is that CZ transform, α-Hölder in `x` by the estimate and in `t` from the order-`0`
operator applied to `ω(·,t) - ω(·,t')`), and the `t`-slot is `BS(∂ₜω(·,t))`, jointly α-Hölder from
`TimeDerivStripHolder` (a bounded compactly supported field has `C^{0,γ}` Biot–Savart image for
every `γ < 1`, since `δ log(1/δ) ≤ Cδ^α`).  The auxiliary modules of `BiotSavart/`
(`norm_taylor_error_le`, `norm_bsField_diff_bound`, `continuous_bsDerivCLM`, `KfBall/*`, the
mean-value integrals) carry the quantitative estimate. -/
theorem biotSavartSpaceTime_holds {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1) :
    Work.CoreResiduals.BiotSavartSpaceTime α := by
  refine ⟨hα, hα1, ?_⟩
  intro ω R S hS hbun
  have hRpos : 0 < R := hbun.1.1
  have hρ : 0 < 2 * R + 5 := by linarith
  have hlt : 2 * R + 5 < 2 * R + 10 := by norm_num
  exact Work.StabilityFar.St4.isContDiffHolderOn_glue (α := α) (ρ := 2 * R + 5)
    (ρ' := 2 * R + 10) (T := S) hρ hlt (biotSavart_coreStrip_holder hα hα1 hS hbun)
    (biotSavart_farStrip_holder_pos hα hα1 hS hbun)

end Work.CoreResiduals.BiotSavart
