import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.proj_meas` — measurability of the sliding box mean

`boxMean ℓ d u Φ = (boxMass ℓ d u)⁻¹ · ∫_{B(u)} Φ(fun _ => z) dz` is, for continuous `Φ`,
an `AEMeasurable` function of the sliding centre `u`.

Both factors are parametric Bochner integrals of *jointly measurable* functions, hence
`AEStronglyMeasurable` in the parameter (`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`,
Tonelli–Fubini measurability of the marginal): the box mass is `∫_z boxInd ℓ d u z` and the
numerator is `∫_z 1_{B(u)}(z)·g z` with `g z = Φ(fun _ => z)`.  The conclusion follows from
`AEMeasurable.inv` and `AEMeasurable.mul`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The sliding box mean is `AEMeasurable` in the sliding centre. -/
lemma aemeasurable_boxMean_aux {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : X1 → ℝ} (hΦc : Continuous Φ) :
    AEMeasurable (fun u : ℝ³ => boxMean ℓ d u Φ) (volume : Measure ℝ³) := by
  classical
  set g : ℝ³ → ℝ := fun z => Φ (fun _ : Fin 1 => z) with hg
  have hgm : Measurable g := by
    rw [hg]
    refine hΦc.measurable.comp ?_
    rw [measurable_pi_iff]
    intro i
    exact measurable_id
  have hS : MeasurableSet {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} :=
    Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d
  -- the numerator `u ↦ ∫_{B(u)} g`
  have hnum : AEMeasurable (fun u : ℝ³ => ∫ z in dlBox ℓ d u, g z) (volume : Measure ℝ³) := by
    have hGm : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => if p.2 ∈ dlBox ℓ d p.1 then g p.2 else 0)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      (Measurable.ite hS (hgm.comp measurable_snd) measurable_const).aestronglyMeasurable
    have h := hGm.integral_prod_right' (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
    refine h.aemeasurable.congr ?_
    filter_upwards with u
    have hfun : (fun y : ℝ³ => (if y ∈ dlBox ℓ d u then g y else 0))
        = (dlBox ℓ d u).indicator g := by
      funext y
      by_cases hy : y ∈ dlBox ℓ d u
      · rw [if_pos hy, Set.indicator_of_mem hy]
      · rw [if_neg hy, Set.indicator_of_notMem hy]
    rw [hfun, MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
  -- the box mass `u ↦ ∫_z boxInd ℓ d u z`
  have hmass : AEMeasurable (fun u : ℝ³ => Work.SmallBoxSliding.boxMass ℓ d u)
      (volume : Measure ℝ³) := by
    have hBm : Measurable (fun p : ℝ³ × ℝ³ => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2) := by
      have hfun : (fun p : ℝ³ × ℝ³ => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
          = {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ)) := by
        funext p
        obtain ⟨u, z⟩ := p
        simp only [Work.SmallBoxSliding.boxInd]
        by_cases hz : z ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show (u, z) ∈
            {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} from hz)]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show (u, z) ∉
            {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1} from hz)]
      rw [hfun]
      exact measurable_const.indicator hS
    exact (hBm.aestronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))).aemeasurable
  have hbox : (fun u : ℝ³ => boxMean ℓ d u Φ)
      = fun u : ℝ³ => (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
          (∫ z in dlBox ℓ d u, g z) := rfl
  rw [hbox]
  exact hmass.inv.mul hnum

end Work.UBBInputs9.B.pd_aux
