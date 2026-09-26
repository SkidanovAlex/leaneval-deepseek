import Submission.Work.Lattice.poissonBasics

/-!
# Characters on the torus and the Fourier coefficients of the periodization

`fourier` at integer points is `1`; consequently the exponential monomials `mFourier (-w)`
are invariant under integer translations of their argument, and the Fourier coefficient of
the lifted periodization is the integral over the unit cube of the periodization twisted by
`mFourier (-w)`.
-/

namespace Work.Lattice

open MeasureTheory Set
open scoped FourierTransform SchwartzMap

theorem fourier_intCast (k n : ℤ) : fourier (T := 1) k ((n : ℝ) : UnitAddCircle) = 1 := by
  have h : ((n : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp [zsmul_eq_mul]⟩
  rw [h, fourier_apply]
  simp

theorem fourier_zero_arg {T : ℝ} (k : ℤ) : (fourier k) (0 : AddCircle T) = 1 := by
  rw [fourier_apply]
  simp

theorem fourier_add_apply {T : ℝ} (k : ℤ) (x y : AddCircle T) :
    (fourier k) (x + y) = (fourier k) x * (fourier k) y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The monomials `mFourier (-w)` on the torus are invariant under integer translations. -/
theorem mFourier_add_intVec {n : ℕ} (w : Fin n → ℤ) (x : Fin n → ℝ) (v : Fin n → ℤ) :
    UnitAddTorus.mFourier (-w) (fun i => ((x i + (v i : ℝ) : ℝ) : UnitAddCircle))
      = UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [AddCircle.coe_add, fourier_add_apply, fourier_intCast, mul_one]

theorem norm_mFourier_le {n : ℕ} (w : Fin n → ℤ) (z : UnitAddTorus (Fin n)) :
    ‖UnitAddTorus.mFourier (-w) z‖ ≤ 1 := by
  calc ‖UnitAddTorus.mFourier (-w) z‖ ≤ ‖UnitAddTorus.mFourier (-w)‖ :=
        ContinuousMap.norm_coe_le_norm _ _
    _ = 1 := UnitAddTorus.mFourier_norm

theorem norm_mFourier_mul_le {n : ℕ} (w : Fin n → ℤ) (z : UnitAddTorus (Fin n)) (c : ℂ) :
    ‖UnitAddTorus.mFourier (-w) z * c‖ ≤ ‖c‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg c) (norm_mFourier_le w z)

/-- The Fourier coefficient of the lifted periodization, as an integral over the unit cube. -/
theorem mFourierCoeff_torusLift {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (w : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (torusLift f) w
      = ∫ x in unitCube n,
          UnitAddTorus.mFourier (-w) (fun i => (x i : UnitAddCircle)) • periodization f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusLift f) w (fun _ => (0:ℝ))]
  have hset : {x : Fin n → ℝ | ∀ i, x i ∈ Ioc ((0:ℝ)) ((0:ℝ) + 1)} = unitCube n := by
    ext x; simp [unitCube]
  rw [hset]
  congr 1
  ext x
  rw [torusLift_apply]

end Work.Lattice
