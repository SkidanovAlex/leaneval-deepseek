import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory

/-- A null set `A ⊆ ℝ³` gives a null cylinder in the `N`-particle configuration space:
the preimage of `A` under the `i`-th coordinate projection has product-measure zero. -/
lemma volume_coord_preimage_null {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (i : Fin N)
    (hvol : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A = 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))
      {x : Submission.BoseGases.X N | x i ∈ A} = 0 := by
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_eval_preimage_null (i := i)
    (μ := fun _ : Fin N => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    hvol

theorem tube_indicator_integral_zero {N : ℕ} {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} (i : Fin N)
    (hA : A ⊆ Submission.BoseGases.acube a)
    (hvol : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A = 0) :
    ∫ x in Submission.BoseGases.abox N a,
      (A.indicator (fun _ => (1 : ℝ)) (x i)) ^ 2 = 0 := by
  classical
  -- the cylinder `{x | x i ∈ A}` has measure zero in the product measure on `X N`
  have hnull := volume_coord_preimage_null i hvol
  -- the integrand vanishes outside that cylinder, hence almost everywhere on the box
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))) ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro x hx
  change x i ∈ A
  by_contra hxA
  exact hx (fun _ => by simp [Set.indicator_of_notMem hxA])

end Work.UBBInputs8.A
