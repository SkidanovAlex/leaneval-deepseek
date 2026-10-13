/-
Work module for the Elgindi finite-time singularity project.

# `BSlotTop/SliceAngGenFts`: the one-dimensional angular estimate, assembled

This is the clean-cone copy of `Work.FTS.EllipticEst.remov.slice_ang_gen`
(`Submission/Work/FTS/EllipticEst/remov/slice_ang_gen.lean`), with the two `sorry`-carrying
inputs replaced by proved declarations:

* the far half `remov.slice_ang_v_far` ⟶ `remov.slice_ang_v_far_live_of_top`
  (`Submission/Work/FTS/EllipticEst/remov/EllFarTop.lean`, proved, sorry-free), fed with its
  `htop` hypothesis (the top-order bound in the reflected variable, for `shiftV u = u/cos`
  reflected) supplied by `remov.farTopXAuxLive_of_top` applied to the **proved** top divided
  slot `remov.EllFarTopDiv.sinWeight_xDivX_top_le'` (`∫_0^{π/8}((U/x)^{(k+1)})² sin(2x)^{2k-γ}
  ≤ C·FarR`);

* the final assembly `remov.slice_ang_gen_final` ⟶ `BSlotTop.sliceAngGenFinalFts`.

The outer half is the proved `remov.slice_ang_v_outer`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.slice_ang_asm
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.slice_ang_v_outer
import Submission.Work.FTS.EllipticEst.remov.EllFarTop
import Submission.Work.FTS.EllipticEst.remov.EllFarTopDiv
import Submission.Work.FTS.EllipticEst.Prop.BSlotTop.SliceAngGenFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop.BSlotTop

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The one-dimensional angular estimate** (the `OneD`-shaped statement of `TT.ESW`). -/
theorem sliceAngGenFts (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      1 ≤ γ → γ ≤ 5 / 4 →
      ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ →
      (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
          (fun θ => (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (iteratedDeriv j u θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
            + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨Co, hCopos, hvout⟩ := Work.FTS.EllipticEst.remov.slice_ang_v_outer k hk
  -- the top-order slot in the reflected divided variable, fed through
  -- `farTopXAuxLive_of_top` into the reflected `shiftV` form expected by
  -- `slice_ang_v_far_live_of_top`
  obtain ⟨Cf, hCfpos, hvfar⟩ :=
    Work.FTS.EllipticEst.remov.slice_ang_v_far_live_of_top k hk
      (Work.FTS.EllipticEst.remov.farTopXAuxLive_of_top k hk
        (Work.FTS.EllipticEst.remov.EllFarTopDiv.sinWeight_xDivX_top_le' k hk))
  -- the `v`-slot bounds on the whole angular interval
  have hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.SliceHyp k γ u g → ∀ m : ℕ, m ≤ k + 1 →
        MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
        ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
    refine ⟨Co + Cf, by linarith, ?_⟩
    intro γ u g h m hm
    obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩ := h
    obtain ⟨ho1, ho2⟩ :=
      hvout γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    obtain ⟨hf1, hf2⟩ :=
      hvfar γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 m hm
    have hU : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ∪ Set.Icc (3 * Real.pi / 8) (Real.pi / 2)
        = Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ, Set.Icc_union_Icc_eq_Icc (by positivity)
        (by linarith [Real.pi_pos])]
    constructor
    · have hunion := ho1.union hf1
      rwa [hU] at hunion
    · rw [Work.FTS.EllipticEst.remov.integral_split_Iθ
        (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) ho1 hf1]
      linarith
  obtain ⟨C, hC, hfin⟩ := sliceAngGenFinalFts k hk hV
  exact ⟨C, hC, fun γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 =>
    hfin γ u g ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩⟩

end Work.FTS.EllipticEst.Prop.BSlotTop
