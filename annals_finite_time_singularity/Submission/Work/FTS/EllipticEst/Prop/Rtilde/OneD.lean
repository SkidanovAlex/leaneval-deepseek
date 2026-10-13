import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Prop.Rtilde.SliceGen
import Submission.Work.FTS.EllipticEst.remov.slice_ang_v_outer
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.OneD`: the one-dimensional angular estimate `slice_ang_gen` (`ESW.OneD`)
from the two window bounds.

The outer window `[0, 3π/8]` is `remov.slice_ang_v_outer` (proved); the far window
`[3π/8, π/2]` is the input `FarB`.  Their sum gives `VBound`, and `SliceGen.genFinal`
converts that into the `u^{(k+2)}`-estimate.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Prop.Rtilde

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The outer-window (`[0, 3π/8]`) weighted `v = u / cos θ` bound. -/
def OutB (k : ℕ) (Co : ℝ) : Prop :=
  0 < Co ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
    ∀ m : ℕ, m ≤ k + 1 →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (Set.Icc 0 (3 * Real.pi / 8)) ∧
      (∫ θ in Set.Icc 0 (3 * Real.pi / 8),
          (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Co * Work.FTS.EllipticEst.remov.AngRHS k γ u g

/-- The far-window (`[3π/8, π/2]`) weighted `v = u / cos θ` bound. -/
def FarB (k : ℕ) (Cf : ℝ) : Prop :=
  0 < Cf ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
    ∀ m : ℕ, m ≤ k + 1 →
      MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (Set.Icc (3 * Real.pi / 8) (Real.pi / 2)) ∧
      (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Cf * Work.FTS.EllipticEst.remov.AngRHS k γ u g

/-- `remov.slice_ang_v_outer` is the outer-window bound. -/
theorem outB (k : ℕ) (hk : 2 ≤ k) : ∃ Co : ℝ, OutB k Co := by
  obtain ⟨C, hC, h⟩ := Work.FTS.EllipticEst.remov.slice_ang_v_outer k hk
  refine ⟨C, hC, ?_⟩
  rintro γ u g ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, h1, h2, h3, h4, h5, h6⟩ m hm
  exact h γ u g hγ1 hγ2 hu hcont hu0 hupi hg h1 h2 h3 h4 h5 h6 m hm

/-- The two window bounds combine into the full `Iθ`-`VBound`. -/
theorem vBound_of_windows (k : ℕ) (hk : 2 ≤ k) {Co Cf : ℝ} (hOut : OutB k Co)
    (hFar : FarB k Cf) : VBound k (Co + Cf) := by
  obtain ⟨hCo, hout⟩ := hOut
  obtain ⟨hCf, hfarb⟩ := hFar
  refine ⟨by linarith, ?_⟩
  intro γ u g hsh m hm
  obtain ⟨ho1, ho2⟩ := hout γ u g hsh m hm
  obtain ⟨hf1, hf2⟩ := hfarb γ u g hsh m hm
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

/-- The far-window bound gives the full one-dimensional estimate `ESW.OneD k`. -/
theorem oneD_of_far (k : ℕ) (hk : 2 ≤ k) {Cf : ℝ} (hFar : FarB k Cf) :
    Work.FTS.EllipticEst.TT.ESW.OneD k := by
  obtain ⟨Co, hOut⟩ := outB k hk
  obtain ⟨C, hC, hfin⟩ := genFinal k hk (vBound_of_windows k hk hOut hFar)
  exact ⟨C, hC, fun γ u g hγ1 hγ2 hu hcont hu0 hupi hg hH1 hH2 hH3 hH4 hH5 hH6 =>
    hfin γ u g ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hH1, hH2, hH3, hH4, hH5, hH6⟩⟩

end Work.FTS.EllipticEst.Prop.Rtilde
