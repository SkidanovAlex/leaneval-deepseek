import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Complex

open MeasureTheory Filter
open scoped Topology

/-- If `F : X → ℂ → ℂ` is jointly measurable and each `u ↦ F x u` is complex differentiable at
`0`, then `x ↦ deriv (fun u => F x u) 0` is a.e. measurable.  Proof: the difference quotients
`x ↦ (F x (1/(n+1)) - F x 0) * (n+1)` are measurable and converge pointwise to the derivative,
and a pointwise limit of measurable functions is a.e. measurable. -/
theorem aemeasurable_deriv_parametric {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (F : X → ℂ → ℂ) (hF : Measurable (Function.uncurry F))
    (hd : ∀ x, DifferentiableAt ℂ (fun u : ℂ => F x u) 0) :
    AEMeasurable (fun x => deriv (fun u : ℂ => F x u) 0) μ := by
  refine aemeasurable_of_tendsto_metrizable_ae' (μ := μ)
    (f := fun n x => (F x (1 / ((n : ℂ) + 1)) - F x 0) * ((n : ℂ) + 1)) ?_ ?_
  · intro n
    have hm : Measurable (fun x : X => F x (1 / ((n : ℂ) + 1))) :=
      hF.comp (Measurable.prodMk measurable_id measurable_const)
    have hm0 : Measurable (fun x : X => F x 0) :=
      hF.comp (Measurable.prodMk measurable_id measurable_const)
    exact ((hm.sub hm0).mul_const _).aemeasurable
  · refine Eventually.of_forall fun x => ?_
    have hderiv : HasDerivAt (fun u : ℂ => F x u) (deriv (fun u : ℂ => F x u) 0) 0 :=
      (hd x).hasDerivAt
    have ha : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
      · filter_upwards with n
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact inv_ne_zero (Nat.cast_add_one_ne_zero n)
    refine (hderiv.tendsto_slope_zero.comp ha).congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply, smul_eq_mul, zero_add, inv_inv, one_div]
    ring

end Commons.Analysis.Complex