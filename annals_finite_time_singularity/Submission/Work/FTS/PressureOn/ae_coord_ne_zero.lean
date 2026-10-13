import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

open MeasureTheory

/-- The coordinate hyperplane `{y : R3 | y i = 0}` is Lebesgue-null: it is the kernel of the
(continuous, surjective) `i`-th coordinate functional `EuclideanSpace.projₗ i`, a strict
submodule of `R3`, and a strict vector subspace of a finite-dimensional real normed space is
null for every additive Haar measure (`MeasureTheory.Measure.addHaar_submodule`). -/
theorem volume_coordHyperplane_eq_zero (i : Fin 3) :
    volume {y : R3 | y i = 0} = 0 := by
  -- the set is the kernel of the `i`-th coordinate functional
  have hset : {y : R3 | y i = 0} =
      (Submodule.comap (EuclideanSpace.projₗ (𝕜 := ℝ) i) (⊥ : Submodule ℝ ℝ) :
        Set R3) := by
    ext y; simp
  rw [hset]
  refine Measure.addHaar_submodule volume _ ?_
  -- the submodule is strict: the `i`-th basis vector is not in it
  intro h
  have hmem : (EuclideanSpace.single i (1 : ℝ) : R3) ∈
      Submodule.comap (EuclideanSpace.projₗ (𝕜 := ℝ) i) (⊥ : Submodule ℝ ℝ) := by
    rw [h]; exact Submodule.mem_top
  simp at hmem

theorem ae_coord_ne_zero : ∀ᵐ y : Work.FTS.PressureOn.R3, y 0 ≠ 0 ∧ y 2 ≠ 0 := by
  have h0 : ∀ᵐ y : R3, y 0 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_coordHyperplane_eq_zero 0
  have h2 : ∀ᵐ y : R3, y 2 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using volume_coordHyperplane_eq_zero 2
  filter_upwards [h0, h2] with y hy0 hy2
  exact ⟨hy0, hy2⟩

end Work.FTS.PressureOn
