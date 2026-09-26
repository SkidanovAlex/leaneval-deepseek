import Mathlib
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.Poisson.Std
import Submission.Work.Modular.Poisson.TorusInversion
import Submission.Work.Modular.Poisson.Fund
import Submission.Work.Poisson.summable_translates

/-!
# Periodisation of a Schwartz function over a lattice

We define `periodize L f x = ∑_{x' ∈ L} f (x + x')` as a continuous function, and record its
basic properties. We also define the character `charFun y z = exp (-2πi ⟪z, y⟫)` and express the
Fourier transform as an integral against it.
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The periodisation `∑_{x' ∈ L} f (· + x')` of a Schwartz function over a lattice. -/
def periodize (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) : C(EuclideanSpace ℝ ι, ℂ) :=
  ∑' x' : L, (f : C(EuclideanSpace ℝ ι, ℂ)).comp
    (ContinuousMap.addRight (x' : EuclideanSpace ℝ ι))

lemma periodize_apply (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    periodize L f x = ∑' x' : L, f (x + x') := by
  rw [periodize, ← ContinuousMap.tsum_apply (Work.Poisson.summable_translates L f) x]
  exact tsum_congr fun x' => rfl

lemma periodize_periodic (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) (a : L) :
    periodize L f (x + a) = periodize L f x := by
  rw [periodize_apply, periodize_apply]
  trans ∑' x' : L, f (x + ((x' + a : L) : EuclideanSpace ℝ ι))
  · exact tsum_congr fun x' => by
      simp only [Submodule.coe_add]
      abel
  · exact Equiv.tsum_eq (Equiv.addRight a) (fun b : L => f (x + (b : EuclideanSpace ℝ ι)))

/-- The coordinate map `EuclideanSpace ℝ ι ≃ₗ (ι → ℝ)`: `d` followed by the canonical
identification. -/
def coordMap (d : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι ≃ₗ[ℝ] (ι → ℝ) :=
  d.trans (EuclideanSpace.equiv ι ℝ).toLinearEquiv

@[simp] lemma coordMap_apply (d : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : coordMap d x = EuclideanSpace.equiv ι ℝ (d x) := rfl

lemma coordMap_symm_apply (d : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)
    (y : ι → ℝ) : (coordMap d).symm y = d.symm ((EuclideanSpace.equiv ι ℝ).symm y) := rfl

lemma coordMap_apply_eq (d : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) :
    EuclideanSpace.equiv ι ℝ (d x) = coordMap d x := rfl

/-- The Fourier character `z ↦ exp (-2π i ⟪z, y⟫)`. -/
def charFun (y z : EuclideanSpace ℝ ι) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ z y : ℂ))

lemma fourier_eq_integral_charFun (f : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (y : EuclideanSpace ℝ ι) :
    𝓕 f y = ∫ z, charFun y z * f z := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
    simp only [smul_eq_mul, charFun]
    congr 1
    push_cast
    ring)

end Work.Modular
