import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `L²` seminorm is invariant under the shift `t ↦ x - t`

For Lebesgue measure `volC N` on configuration space `Conf N = Fin N → E3`
(which is left-translation invariant by instance, and negation invariant by
hypothesis `hneg`), the reflection map `t ↦ x - t` is measure preserving
(`Measure.map_sub_left_eq_self`).  Since that map is moreover a measurable
embedding, `MeasurableEmbedding.eLpNorm_map_measure` applies *without any
measurability hypothesis on `f`*, giving the invariance of the `L²` seminorm
of `t ↦ ‖f (x - t)‖`; the norm on the outside is absorbed by `eLpNorm_norm`.
-/

namespace Work.BoseSym.Mollify

open MeasureTheory

theorem eLpNorm_shift_norm_eq {N : ℕ}
    (hneg : MeasureTheory.Measure.IsNegInvariant (Work.BoseSym.volC N))
    (f : Work.BoseSym.Conf N → ℝ) (x : Work.BoseSym.Conf N)
    (hf : MeasureTheory.AEStronglyMeasurable f (Work.BoseSym.volC N)) :
    MeasureTheory.eLpNorm (fun t => ‖f (x - t)‖) 2 (Work.BoseSym.volC N)
      = MeasureTheory.eLpNorm f 2 (Work.BoseSym.volC N) := by
  -- `volC N = volume` is left-translation invariant (instance) and, by `hneg`,
  -- negation invariant; hence `t ↦ x - t` preserves it.
  have hmap : Measure.map (fun t : Work.BoseSym.Conf N => x - t) (Work.BoseSym.volC N)
      = Work.BoseSym.volC N :=
    @MeasureTheory.Measure.map_sub_left_eq_self (Work.BoseSym.Conf N) _ _ _ _
      (Work.BoseSym.volC N) hneg _ x
  have hemp : MeasurableEmbedding (fun t : Work.BoseSym.Conf N => x - t) :=
    measurableEmbedding_subLeft x
  calc MeasureTheory.eLpNorm (fun t : Work.BoseSym.Conf N => ‖f (x - t)‖) 2
        (Work.BoseSym.volC N)
      = MeasureTheory.eLpNorm
          ((fun s : Work.BoseSym.Conf N => ‖f s‖) ∘ (fun t : Work.BoseSym.Conf N => x - t))
          2 (Work.BoseSym.volC N) := rfl
    _ = MeasureTheory.eLpNorm (fun s : Work.BoseSym.Conf N => ‖f s‖) 2
          (Measure.map (fun t : Work.BoseSym.Conf N => x - t) (Work.BoseSym.volC N)) :=
          (MeasurableEmbedding.eLpNorm_map_measure (μ := Work.BoseSym.volC N) (p := 2)
            (f := fun t : Work.BoseSym.Conf N => x - t)
            (g := fun s : Work.BoseSym.Conf N => ‖f s‖) hemp).symm
    _ = MeasureTheory.eLpNorm (fun s : Work.BoseSym.Conf N => ‖f s‖) 2
          (Work.BoseSym.volC N) := by
          rw [hmap]
    _ = MeasureTheory.eLpNorm f 2 (Work.BoseSym.volC N) := MeasureTheory.eLpNorm_norm f hf

end Work.BoseSym.Mollify
