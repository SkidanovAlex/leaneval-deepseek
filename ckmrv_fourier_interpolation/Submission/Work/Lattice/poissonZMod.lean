import Mathlib
import Submission.Work.Lattice.poissonBasics
import Submission.Work.Lattice.poissonTorus
import Submission.Work.Lattice.continuous_periodization
import Submission.Work.Lattice.summable_schwartz_intVec
import Submission.Work.Lattice.fourierCLM_eq_integral_unitCube

/-!
# Poisson summation over `ℤⁿ`

For a Schwartz function `f` on `ℝⁿ` one has `∑_{v ∈ ℤⁿ} f v = ∑_{w ∈ ℤⁿ} f̂ w`, where `f̂` is the
Fourier transform with the convention `f̂ w = ∫ x, exp (-2 π I ⟪w, x⟫) f x`.

The proof follows the one-dimensional argument: the periodization `P x = ∑_{v ∈ ℤⁿ} f (x + v)`
descends to a continuous function on the torus `(ℝ/ℤ)ⁿ`, whose Fourier coefficients are the
values `f̂ w` of the Fourier transform (this is `fourierCLM_eq_integral_unitCube`), and then
pointwise Fourier inversion on the torus (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`)
evaluated at the origin gives the formula.
-/

namespace Work.Lattice

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

/-- The periodization descends to a continuous function on the torus. -/
theorem continuous_torusLift {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Continuous (torusLift f) := by
  let π : (Fin n → ℝ) → UnitAddTorus (Fin n) := fun x i => ((x i : ℝ) : UnitAddCircle)
  have hπ : IsOpenQuotientMap π :=
    IsOpenQuotientMap.piMap (fun _ : Fin n =>
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1:ℝ))))
  have hcomp : torusLift f ∘ π = periodization f := by
    funext x; exact torusLift_apply f x
  exact (hπ.isQuotientMap.continuous_iff).mpr (hcomp ▸ continuous_periodization f)

/-- **Poisson summation over `ℤⁿ`.** For a Schwartz function `f` on `ℝⁿ`,
`∑_{v ∈ ℤⁿ} f v = ∑_{w ∈ ℤⁿ} f̂ w`, where `f̂` is the Fourier transform
`w ↦ ∫ x, exp (-2 π I ⟪w, x⟫) f x` (Mathlib's `FourierTransform.fourierCLM`) and `v`, `w` range
over `ℤⁿ ⊆ ℝⁿ`. -/
theorem poissonZMod {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (∑' v : Fin n → ℤ, f (WithLp.toLp 2 fun i => (v i : ℝ)))
      = ∑' w : Fin n → ℤ,
          (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
            (WithLp.toLp 2 fun i => (w i : ℝ)) := by
  have hcont : Continuous (torusLift f) := continuous_torusLift f
  have hcoeff : ∀ w : Fin n → ℤ,
      UnitAddTorus.mFourierCoeff (torusLift f) w
        = (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
            (WithLp.toLp 2 (intVecToReal w)) := by
    intro w
    rw [mFourierCoeff_torusLift]
    exact (fourierCLM_eq_integral_unitCube f w).symm
  have hsum : Summable fun w : Fin n → ℤ => UnitAddTorus.mFourierCoeff (torusLift f) w :=
    (summable_schwartz_intVec
      (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)).congr
        (fun w => (hcoeff w).symm)
  have hhas := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := ⟨torusLift f, hcont⟩) hsum (0 : UnitAddTorus (Fin n))
  have h1 : (∑' w : Fin n → ℤ, UnitAddTorus.mFourierCoeff (torusLift f) w)
      = torusLift f 0 := by
    have hh : HasSum (fun w : Fin n → ℤ => UnitAddTorus.mFourierCoeff (torusLift f) w)
        (torusLift f 0) := by
      simpa [UnitAddTorus.mFourier, fourier_zero_arg, smul_eq_mul] using hhas
    exact hh.tsum_eq
  have h2 : torusLift f 0 = periodization f 0 := by
    have hh := torusLift_apply f (0 : Fin n → ℝ)
    rw [show (fun i : Fin n => ((0 : Fin n → ℝ) i : UnitAddCircle)) = 0 from by
      funext i; simp] at hh
    exact hh
  have hL : (∑' v : Fin n → ℤ, f (WithLp.toLp 2 fun i => (v i : ℝ))) = periodization f 0 := by
    rw [periodization]
    simp only [zero_add]
    rfl
  rw [hL, ← h2, ← h1]
  exact tsum_congr hcoeff

end Work.Lattice
