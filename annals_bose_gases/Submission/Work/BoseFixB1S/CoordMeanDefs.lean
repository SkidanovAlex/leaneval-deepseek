import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseFixB1S.PiAnovaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.CoordMeanDefs` — the coordinate mean on a product measure

The basic definition used by the ANOVA/Efron–Stein development
(`Submission/Work/BoseFixB1S/piAnovaLeCoordMeans.lean`): for a (finite) measure `ν` on `α`
and a coordinate `j : Fin (k+1)`, the **coordinate mean**

`coordMean ν j u x = (ν univ).toReal⁻¹ ∫ z, u (Function.update x j z) ∂ν`

is the mean of `u` in the coordinate `j`, i.e. the conditional mean of `u` given all the
other coordinates of the product space `(Fin (k+1) → α)`.

This file also records the elementary facts that this mean is independent of the coordinate
`j` (both as a definitional computation and in the form needed when a function is
independent of some other coordinate).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

variable {α : Type*} [MeasurableSpace α]

/-- The **coordinate mean** of `u` in the coordinate `j` of the product `(Fin N → α)`;
the conditional mean of `u` given all the other coordinates. -/
def coordMean (ν : Measure α) {N : ℕ} (j : Fin N)
    (u : (Fin N → α) → ℝ) : (Fin N → α) → ℝ :=
  fun x => (1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν

@[simp]
theorem coordMean_apply (ν : Measure α) {N : ℕ} (j : Fin N)
    (u : (Fin N → α) → ℝ) (x : Fin N → α) :
    coordMean ν j u x = (1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν := rfl

/-- The coordinate mean in the coordinate `j` is independent of the coordinate `j`. -/
theorem coordMean_indep_self (ν : Measure α) {k : ℕ} (j : Fin (k + 1))
    (u : (Fin (k + 1) → α) → ℝ) :
    ∀ x z, coordMean ν j u (Function.update x j z) = coordMean ν j u x := by
  intro x z
  simp only [coordMean]
  congr 1
  apply integral_congr_ae
  filter_upwards with z'
  rw [Function.update_idem]

/-- The coordinate mean in a coordinate different from `j` of a function independent of `j`
is again independent of `j`. -/
theorem coordMean_indep_other (ν : Measure α) [SigmaFinite ν] {k : ℕ} (j i : Fin (k + 1))
    (hij : j ≠ i) {u : (Fin (k + 1) → α) → ℝ}
    (hu : ∀ x z, u (Function.update x j z) = u x) :
    ∀ x z, coordMean ν i u (Function.update x j z) = coordMean ν i u x := by
  intro x z
  simp only [coordMean]
  congr 1
  apply integral_congr_ae
  filter_upwards with z'
  rw [Function.update_comm hij z z' x, hu]

end Work.BoseFixB1S
