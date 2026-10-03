import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

namespace Work.ORP311

theorem matOp_add {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.matOp (G := G) (A + B) = Work.ORVonNeumann.Rep.matOp (G := G) A + Work.ORVonNeumann.Rep.matOp (G := G) B := by
  -- `matOp` has the entrywise form `matOp A = ∑ i, (hinclude i).comp (∑ j, A i j ∘ hcoord j)`;
  -- checking it coordinatewise via `matOp_ext` reduces the claim to `∑` and `comp` additivity.
  apply Work.ORVonNeumann.Rep.matOp_ext
  intro i
  rw [Work.ORVonNeumann.Rep.hcoord_matOp, ContinuousLinearMap.comp_add,
    Work.ORVonNeumann.Rep.hcoord_matOp, Work.ORVonNeumann.Rep.hcoord_matOp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.add_apply, Subalgebra.coe_add, ContinuousLinearMap.add_comp]

end Work.ORP311
