import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Submission.Work.BoseBoxFock.SamplingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- The coordinate map appearing in the definition of `torusLift` is measurable.  Coordinatewise it
reads off the representative of a point of `𝕋³ = (ℝ/ℤ)³` in the half-open box `(-1/2,1/2]³`, which
is (the projection of) Mathlib's measurable equivalence `UnitAddTorus.measurableEquivPiIoc`; the
final `WithLp.toLp 2` is measurable by `WithLp.measurable_toLp`. -/
lemma measurable_torusLiftRep :
    Measurable (fun t : UnitAddTorus (Fin 3) =>
      WithLp.toLp 2 fun i : Fin 3 => (AddCircle.equivIoc 1 (-(1/2) : ℝ) (t i)).1) := by
  have hcoord : Measurable fun t : UnitAddTorus (Fin 3) =>
      fun i : Fin 3 => (AddCircle.equivIoc 1 (-(1/2) : ℝ) (t i)).1 := by
    refine Measurable.of_eval fun i => ?_
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc 1 (-(1/2) : ℝ)).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp hcoord

/-- `torusLift g` is, by definition, the composition of `g` with the measurable coordinate map of
`measurable_torusLiftRep`. -/
lemma torusLift_eq_comp (g : ℝ³ → ℂ) :
    torusLift g = g ∘ (fun t : UnitAddTorus (Fin 3) =>
      WithLp.toLp 2 fun i : Fin 3 => (AddCircle.equivIoc 1 (-(1/2) : ℝ) (t i)).1) := rfl

/-- **The lift of a smooth compactly supported function on `ℝ³` is `L²` on the torus.** -/
theorem torusLift_memLp {g : ℝ³ → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.MemLp (Work.BoseBoxFock.torusLift g) 2 Work.BoseBoxFock.torusVol := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
  refine MeasureTheory.MemLp.of_bound ?_ C ?_
  · rw [torusLift_eq_comp g]
    exact (hg.continuous.measurable.comp measurable_torusLiftRep).aestronglyMeasurable
  · filter_upwards with t
    simpa only [torusLift] using hC _

end Work.BoseBoxFock
