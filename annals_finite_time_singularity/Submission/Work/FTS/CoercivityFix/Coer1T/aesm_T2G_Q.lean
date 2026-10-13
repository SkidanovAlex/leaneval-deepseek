import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.L12f_continuousOn
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

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

/-!
# A.e. strong measurability of the `T₂`-integrand in the interior class `SmoothQuad`

The integrand `T2 α f z θ * D_θ f z θ * thetaW α z θ` of the `T₂`-pairing is a product of a
measurable function of `(z,θ)` (the angular data `D_θΓ`, the radial coefficient
`2z/(c(1+z)²)`, the weight `thetaW α = w²·sin(2θ)^{-γ}`), a function of `z` alone
(`L₁₂(f)`, continuous on `(0,∞)` by `HardyHyp`) and `D_θ f`, which is continuous on the open
quadrant for data of class `SmoothQuad` (genuine `C^∞`, not analyticity).

This is the interior-class port of the private lemma `aesm_T2G` of
`Submission/Work/Coercivity/wip_T2_ge.lean`, where the smoothness hypothesis is the analytic
class `Work.Spaces.SmoothNbhd f`; that hypothesis is incompatible with a cut-off (see the
`SmoothQuad` discussion in `Work.FTS.LocData.Defs`), so the port is needed on the route.
-/

/-- `D_θ f` is a.e. strongly measurable on the quadrant for `SmoothQuad` data: `D_θ` preserves
genuine `C^∞`-smoothness on the open quadrant (`Work.FTS.LocData.contDiffOn_Dth`), and the open
quadrant differs from the closed one by a null set. -/
theorem aesm_Dth_smoothQuad {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hD : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_Dth (isOpen_Ioi.prod isOpen_Ioo) hsm
  refine Work.Spaces.aesm_of_continuousOn_Qd _ (hD.continuousOn.mono ?_)
  intro p hp
  exact ⟨Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0) hp.1, hp.2⟩

/-- A function of `z` alone which is continuous on `(0,∞)` is a.e. strongly measurable on the
quadrant; applied to `L₁₂(f)`, which is continuous on `(0,∞)` under `HardyHyp`. -/
theorem aesm_of_continuousOn_Ioi {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (hg.comp continuous_fst.continuousOn (fun _ hp => hp.1))

theorem aesm_T2G_Q (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsq : Work.FTS.LocData.SmoothQuad f) (hfH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Coercivity.T2 α f z θ * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set P : Measure (ℝ × ℝ) :=
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) with hP
  -- ### The angular factor `(z,θ) ↦ D_θΓ(θ)`, as a function on the product
  have hmDthGam : Measurable (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2) := by
    have h : (fun p : ℝ × ℝ => Work.Coercivity.DthGam α p.1 p.2)
        = fun p => Real.sin (2 * p.2) * deriv (fun t : ℝ => Work.Spaces.Gam α t) p.2 := by
      funext p
      rw [Work.Coercivity.DthGam_eq]
    rw [h]
    exact (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).mul
      ((measurable_deriv (fun t : ℝ => Work.Spaces.Gam α t)).comp measurable_snd)
  -- ### The radial coefficient `(z,θ) ↦ 2z/(c(1+z)²)`
  have hmτ : Measurable (fun p : ℝ × ℝ => 2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2)) :=
    ((measurable_const.mul measurable_id).div
      (measurable_const.mul ((measurable_const.add measurable_id).pow_const 2))).comp
        measurable_fst
  -- ### The weight `thetaW α` splits into two measurable factors
  have hmw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) := by
    have h : Measurable (fun z : ℝ => Work.Spaces.w z ^ 2) := by
      show Measurable (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2)
      exact (((measurable_const.add measurable_id).pow_const 2).div
        (measurable_id.pow_const 2)).pow_const 2
    exact h.comp measurable_fst
  have hmsig : Measurable
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) :=
    (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).pow_const _
  -- ### `L₁₂(f)` is continuous on `(0,∞)` under `HardyHyp`
  have hL12 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1) P :=
    aesm_of_continuousOn_Ioi (Work.Coercivity.L12f_continuousOn f hfH)
  -- ### `D_θ f` is continuous on the open quadrant for `SmoothQuad` data
  have hDth : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) P :=
    aesm_Dth_smoothQuad hsq
  -- ### The product
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      -(Work.Coercivity.DthGam α p.1 p.2) * (2 * p.1 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        * Work.Coercivity.L12f f p.1 * Work.Spaces.Dth f p.1 p.2
        * (Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)))) P :=
    ((((hmDthGam.neg.aestronglyMeasurable.mul hmτ.aestronglyMeasurable).mul hL12).mul hDth).mul
      (hmw.aestronglyMeasurable.mul hmsig.aestronglyMeasurable))
  refine hprod.congr ?_
  filter_upwards with p
  simp only [Function.uncurry, Work.Coercivity.T2, Work.Coercivity.thetaW]

end Work.FTS.CoercivityFix.Coer1T
