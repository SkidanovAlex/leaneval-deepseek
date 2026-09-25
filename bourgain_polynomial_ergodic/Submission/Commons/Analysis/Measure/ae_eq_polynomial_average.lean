import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Dynamics.Ergodic.MeasurePreserving

namespace Commons.Analysis.Measure

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- If two functions agree a.e. then so do their polynomial ergodic averages along any
measure-preserving map `T` (no invertibility assumption is needed: `T^[k]` pushes the
null set `{f ≠ g}` to a null set).  This lets one replace a merely a.e.-measurable `L^p`
function by a measurable representative without changing the average. -/
theorem ae_eq_polynomial_average {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}
    (hT : MeasurePreserving T μ μ) {f g : X → ℝ} (h : f =ᵐ[μ] g) (P : Polynomial ℤ) (N : ℕ) :
    (fun x : X => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (T^[(P.eval (i : ℤ)).toNat] x))
      =ᵐ[μ] (fun x : X => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (T^[(P.eval (i : ℤ)).toNat] x)) := by
  rw [Filter.EventuallyEq]
  have hterm : ∀ i ∈ Finset.range N,
      ∀ᵐ x ∂μ, f (T^[(P.eval (i : ℤ)).toNat] x) = g (T^[(P.eval (i : ℤ)).toNat] x) :=
    fun i _ => (hT.iterate _).quasiMeasurePreserving.ae h
  filter_upwards [(eventually_all_finset (Finset.range N)).mpr hterm] with x hx
  congr 1
  exact Finset.sum_congr rfl (fun i hi => hx i hi)

end Commons.Analysis.Measure