import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.cc.Subcut.MajDefs
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Xn6Limit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open MeasureTheory Set Filter
open scoped Real

set_option autoImplicit false

/-! ## Measurability of the two indicator families -/

/-- The indicator of `UN N` is measurable on the plane. -/
theorem measurable_indicator_UN (N : ℕ) :
    Measurable (fun p : ℝ × ℝ => (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) p) :=
  measurable_const.indicator (Work.FTS.GalBasis.cc.measurableSet_UN N)

/-- The indicator of `LN N` is measurable on the line. -/
theorem measurable_indicator_LN (N : ℕ) :
    Measurable (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ) :=
  measurable_const.indicator (Work.FTS.GalBasis.cc.measurableSet_LN N)

/-- **All the (a.e.) strong measurability facts about the majorant `Maj` and its two pieces.**

`Maj α C κN N f z θ = C · (1_{UN N}(z,θ) · HkIntegrand α 4 f z θ + 1_{LN N}(θ) · ∑_{b<4} (zslotW α b f z θ)²)`
with `zslotW α b f z θ = DzIter b f z θ * Wt α z θ`.

The five conjuncts are needed by a consumer that integrates `Maj` and splits the integral into the
summands `A z θ = HkIntegrand α 4 f z θ * 1_{UN N}(z,θ)` and
`B b z θ = 1_{LN N}(θ) * (DzIter b f z θ * Wt α z θ)²`:
 * conjunct 1: `Function.uncurry (Maj …)` is a.e. strongly measurable for the product measure
   `(volume.restrict Iz).prod (volume.restrict Iθ)`;
 * conjuncts 2 and 3: same for the uncurried `A` and for the uncurried `B b` (all `b`), which is
   what `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` needs to give a.e. strong
   measurability of the marginals `z ↦ ∫_θ A z θ` and `z ↦ ∫_θ B b z θ` w.r.t. `volume.restrict Iz`;
 * conjuncts 4 and 5: for every `z > 0` the `θ`-slices of `A` and `B b` are a.e. strongly measurable
   for `volume.restrict Iθ`; this is what turns pointwise domination by `Maj`'s slice into
   `IntegrableOn` (via `MeasureTheory.Integrable.mono'`).

Proof hints.  Measurability of `p ↦ (UN N).indicator (fun _ => (1:ℝ)) p` and
`θ ↦ (LN N).indicator (fun _ => (1:ℝ)) θ` is `Measurable.indicator` with `measurableSet_UN` /
`measurableSet_LN`; `(fun p : ℝ×ℝ => HkIntegrand α 4 f p.1 p.2)` and
`(fun p => DzIter b f p.1 p.2 * Wt α p.1 p.2)` are continuous on the open quadrant
(`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`,
`Work.FTS.EllipticEst.SmoothOpen.DzIter` and
`Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd`; `Work.FTS.Apriori.Limit.Qd` and
`Work.FTS.EllipticEst.Q0` are both definitionally `Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)`), so
`Work.Spaces.aesm_of_continuousOn_Qd` applies; multiply, square, sum over `b ∈ Finset.range 4`
(`Finset.aestronglyMeasurable_sum`), multiply by the constant `C`
(`AEStronglyMeasurable.const_mul`), and rewrite `Maj` pointwise with `Maj_eq_sum_form`.  For the
slices use `Work.Spaces.aesm_slice_of_continuousOn_Qd` and note that for fixed `z > 0` the functions
`θ ↦ (UN N).indicator (fun _ => (1:ℝ)) (z,θ)` and `θ ↦ (LN N).indicator (fun _ => (1:ℝ)) θ` are
measurable (the first is the indicator of the measurable preimage
`Set.preimage (fun θ : ℝ => (z,θ)) (UN N)`). -/
theorem Maj_aesm {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (C κN : ℝ) (N : ℕ) :
    MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (Work.FTS.GalBasis.cc.Maj α C κN N f))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ
          * (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ b : ℕ, MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun z θ : ℝ =>
          (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
            * (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
      (∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ
          * (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∀ z : ℝ, 0 < z → ∀ b : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ
          * (Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the product measure on the quadrant
  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hμ
  -- continuity of the two slot densities on the open quadrant
  have hHk : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hsm.continuousOn_HkIntegrand α 4
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.StrongLWP.Xn6Limit.continuousOn_Wt_Qd α
  have hDzW : ∀ b : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun b =>
    ((hsm.DzIter b).continuousOn).mul hWt
  -- a.e. strong measurability of the uncurried slot densities
  have haesmHk : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2) μ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hHk
  have haesmDzW : ∀ b : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) μ :=
    fun b => Work.Spaces.aesm_of_continuousOn_Qd _ (hDzW b)
  -- measurability of the two indicators
  have hindU : Measurable
      (fun p : ℝ × ℝ => (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) p) :=
    measurable_indicator_UN N
  have hindL : Measurable
      (fun p : ℝ × ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) p.2) :=
    (measurable_indicator_LN N).comp measurable_snd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- conjunct 1: the majorant itself
    have hsum : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        ∑ b ∈ Finset.range 4, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) p.2
          * (Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) μ :=
      Finset.aestronglyMeasurable_fun_sum (Finset.range 4)
        (fun b _ => hindL.aestronglyMeasurable.mul ((haesmDzW b).pow 2))
    have hmain : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
        C * ((Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (p.1, p.2)
          * Work.Spaces.HkIntegrand α 4 f p.1 p.2
          + ∑ b ∈ Finset.range 4, (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) p.2
              * (Work.Spaces.DzIter b f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)) μ :=
      (((hindU.aestronglyMeasurable.mul haesmHk).add hsum).const_mul C)
    refine hmain.congr (Eventually.of_forall fun p => ?_)
    exact (Work.FTS.GalBasis.cc.Maj_eq_sum_form α C κN N f p.1 p.2).symm
  · -- conjunct 2: the `UN`-part
    exact haesmHk.mul hindU.aestronglyMeasurable
  · -- conjunct 3: the `LN`-part, for every `b`
    intro b
    exact hindL.aestronglyMeasurable.mul ((haesmDzW b).pow 2)
  · -- conjunct 4: the `θ`-slices of the `UN`-part
    intro z hz
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hHk hz
    have h2 : Measurable
        (fun θ : ℝ => (Work.FTS.GalBasis.cc.UN N).indicator (fun _ => (1 : ℝ)) (z, θ)) :=
      hindU.comp (measurable_const.prodMk measurable_id)
    exact h1.mul h2.aestronglyMeasurable
  · -- conjunct 5: the `θ`-slices of the `LN`-part
    intro z hz b
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.DzIter b f z θ * Work.Spaces.Wt α z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hDzW b) hz
    have h2 : Measurable
        (fun θ : ℝ => (Work.FTS.GalBasis.cc.LN N).indicator (fun _ => (1 : ℝ)) θ) :=
      measurable_indicator_LN N
    exact h2.aestronglyMeasurable.mul (h1.pow 2)

end Work.FTS.GalBasis.cc.Subcut
