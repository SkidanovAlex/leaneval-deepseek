import Mathlib.Analysis.Fourier.AddCircleMulti
import Submission.Work.BoseBoxFock.SamplingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace Work.BoseBoxFock

theorem parseval_torus_box (P : UnitAddTorus (Fin 3) → ℂ)
    (hP : MeasureTheory.MemLp P 2 Work.BoseBoxFock.torusVol) :
    (∑' n : Fin 3 → ℤ, ‖UnitAddTorus.mFourierCoeff (⇑(hP.toLp P)) n‖ ^ 2)
      = ∫ x in Work.BoseBoxFock.boxIoc, ‖P (Work.BoseBoxFock.torusProj x)‖ ^ 2 := by
  -- Parseval on the torus (the `L²` class `hP.toLp P` of `P`).
  have hsum := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin 3) (hP.toLp P)
  have htsum : ∑' n : Fin 3 → ℤ, ‖UnitAddTorus.mFourierCoeff (⇑(hP.toLp P)) n‖ ^ 2
      = ∫ t : UnitAddTorus (Fin 3), ‖(hP.toLp P) t‖ ^ 2 := hsum.tsum_eq
  rw [htsum]
  -- The half-open box `(-1/2,1/2]³` is exactly the fundamental domain of `integral_preimage`.
  have hbox : boxIoc
      = {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} := by
    ext x
    simp only [boxIoc, Set.mem_pi, Set.mem_univ, Set.mem_Ioc, Set.mem_ofPred_eq, true_implies]
    constructor <;> intro h i
    · exact ⟨(h i).1, by linarith [(h i).2]⟩
    · exact ⟨(h i).1, by linarith [(h i).2]⟩
  -- Torus integral = integral over the box of the projected function.
  have hR : ∫ x in boxIoc, ‖P (torusProj x)‖ ^ 2 = ∫ t : UnitAddTorus (Fin 3), ‖P t‖ ^ 2 := by
    rw [hbox, ← UnitAddTorus.integral_preimage (d := Fin 3) (fun t => ‖P t‖ ^ 2)
      (fun _ => (-(1/2) : ℝ))]
  -- `hP.toLp P` agrees with `P` almost everywhere.
  have hL : ∫ t : UnitAddTorus (Fin 3), ‖(hP.toLp P) t‖ ^ 2 = ∫ t, ‖P t‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hP.coeFn_toLp] with t ht
    rw [ht]
  rw [hL, ← hR]

end Work.BoseBoxFock
