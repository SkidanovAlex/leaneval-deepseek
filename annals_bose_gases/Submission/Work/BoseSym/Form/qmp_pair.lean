import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Form

open MeasureTheory

/-- Auxiliary lemma: for a finite index type `ι` and two distinct indices `i ≠ j`, the
two-coordinate map `x ↦ (x i, x j)` pushes the product Lebesgue measure on `ι → E3`
forward to a measure which is absolutely continuous with respect to the product of
two copies of the Lebesgue measure on `E3`.

The configuration space splits as a product: the coordinates other than `j` on one
side, the single coordinate `j` on the other.  This identification is measure
preserving, and transports the two-coordinate map to the product of the evaluations
at `i` (on the first factor) and at `j` (on the second factor). -/
lemma qmp_pair_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : ι → E3 => (x i, x j))
      (Measure.pi (fun _ : ι => (volume : Measure E3)))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
  classical
  -- evaluation of the first factor of the split at `i`
  have hA := Measure.quasiMeasurePreserving_eval
    (μ := fun _ : {k : ι // k ≠ j} => (volume : Measure E3)) ⟨i, hij⟩
  -- evaluation of the second factor of the split at `j`
  have hB := Measure.quasiMeasurePreserving_eval
    (μ := fun _ : {k : ι // ¬(k ≠ j)} => (volume : Measure E3)) ⟨j, fun h => h rfl⟩
  -- the two-coordinate map on the split configuration space
  have hmap := QuasiMeasurePreserving.prodMap hA hB
  -- the measure preserving identification of the configuration space with the product
  have he := (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure E3))
    (fun k : ι => k ≠ j)).quasiMeasurePreserving
  refine (hmap.comp he).congr (by fun_prop) ?_
  filter_upwards with x
  apply Prod.ext
  · simp only [Function.comp_apply, Prod.map_fst, Function.eval,
      MeasurableEquiv.piEquivPiSubtypeProd_apply]
  · simp only [Function.comp_apply, Prod.map_snd, Function.eval,
      MeasurableEquiv.piEquivPiSubtypeProd_apply]

theorem qmp_pair {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasureTheory.Measure.QuasiMeasurePreserving (fun x : Work.BoseSym.Conf N => (x i, x j))
      (Work.BoseSym.volC N)
      ((MeasureTheory.volume : MeasureTheory.Measure Work.BoseSym.E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseSym.E3)) := by
  exact qmp_pair_pi i j hij

end Work.BoseSym.Form
