import Mathlib.FieldTheory.Finiteness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Filter Set MeasureTheory
open scoped Topology

namespace Commons.MeasureTheory.Integral

/-- If `f : ℝ → V` has bounded variation on `uIcc a b`, where `V` is a finite-dimensional real
normed space, then its derivative is interval integrable on `a..b`.

This is the vector-valued generalisation of `BoundedVariationOn.intervalIntegrable_deriv`; the
proof decomposes `f` along a continuous linear equivalence with a coordinate space `ι → ℝ`, uses
the real-valued statement on each coordinate, and pushes the resulting `ℝ`-valued integrability
back through the inverse equivalence, using that `f` is a.e. differentiable. -/
theorem BoundedVariationOn.intervalIntegrable_deriv_of_finiteDimensional {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : ℝ → V} {a b : ℝ} (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  classical
  let B := Module.Basis.ofVectorSpace ℝ V
  let e : V ≃L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) := B.equivFun.toContinuousLinearEquiv
  let eL : V →L[ℝ] (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) := e
  let eS : (Module.Basis.ofVectorSpaceIndex ℝ V → ℝ) →L[ℝ] V := e.symm
  have hΦ : BoundedVariationOn (fun x => e (f x)) (uIcc a b) :=
    e.lipschitz.comp_boundedVariationOn hf
  have key : ∀ i, IntervalIntegrable (fun x => deriv (fun t => e (f t) i) x) volume a b := by
    intro i
    have hc : BoundedVariationOn (fun x => e (f x) i) (uIcc a b) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).lipschitz.comp_boundedVariationOn hΦ
    exact hc.intervalIntegrable_deriv
  have hpi : IntervalIntegrable (fun x => fun i => deriv (fun t => e (f t) i) x) volume a b := by
    constructor
    · exact integrable_pi_iff.mpr (fun i => (key i).1)
    · exact integrable_pi_iff.mpr (fun i => (key i).2)
  have hcomp : IntervalIntegrable
      (fun x => e.symm (fun i => deriv (fun t => e (f t) i) x)) volume a b := by
    constructor
    · exact eS.integrableOn_comp hpi.1
    · exact eS.integrableOn_comp hpi.2
  have hae : ∀ᵐ x ∂volume, x ∈ uIoc a b →
      (fun x => e.symm (fun i => deriv (fun t => e (f t) i) x)) x = deriv f x := by
    filter_upwards [hf.ae_differentiableAt_of_mem_uIcc] with x hx hxm
    have hdf : HasDerivAt f (deriv f x) x := (hx (uIoc_subset_uIcc hxm)).hasDerivAt
    have hdc : HasDerivAt (fun t => e (f t)) (e (deriv f x)) x :=
      (ContinuousLinearMap.hasFDerivAt eL).comp_hasDerivAt x hdf
    have hcoord : (fun i => deriv (fun t => e (f t) i) x) = e (deriv f x) := by
      funext i
      have hci : HasDerivAt (fun t => e (f t) i)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i) (e (deriv f x))) x :=
        (ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i)).comp_hasDerivAt x hdc
      simpa using hci.deriv
    rw [hcoord]
    exact e.symm_apply_apply (deriv f x)
  have heq : (fun x => e.symm (fun i => deriv (fun t => e (f t) i) x))
      =ᵐ[volume.restrict (uIoc a b)] deriv f := by
    rw [Filter.EventuallyEq]
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_uIoc] with x hx hxm
    exact hx hxm
  exact hcomp.congr_ae heq

theorem intervalIntegrable_deriv_of_absolutelyContinuousOnInterval {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f : ℝ → F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  BoundedVariationOn.intervalIntegrable_deriv_of_finiteDimensional hf.boundedVariationOn

end Commons.MeasureTheory.Integral