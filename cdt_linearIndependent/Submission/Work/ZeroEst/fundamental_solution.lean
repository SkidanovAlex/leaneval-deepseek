import Mathlib
import Submission.Work.ZeroEst3.fundamentalPhi

/-!
# Existence of a fundamental solution matrix for `q · Φ' = A · Φ` over `ℚ⟦X⟧`

Let `q ∈ ℚ[X]` have non-zero constant term and `A = (A i k)` a matrix of polynomials.
We produce a matrix `Φ` of formal power series with

* `Φ(0) = 1`,
* `q · Φ' = A · Φ`   (entrywise, `A` acting by matrix multiplication),
* `IsUnit Φ.det`.

Since `q(0) ≠ 0`, `q` is a unit of `ℚ⟦X⟧`, so we may rewrite the equation as
`Φ' = (q⁻¹ • A) · Φ`.  Existence of a solution of the latter with `Φ(0) = 1` is the
content of `Work.ZeroEst3.fundamentalPhi` (coefficient-wise recursion), and we
transport it across the (unit) factor `q`.
-/

namespace Work.ZeroEst

open PowerSeries Matrix

theorem fundamental_solution (m : ℕ) (q : Polynomial ℚ)
    (A : Fin m → Fin m → Polynomial ℚ) (hq0 : q.coeff 0 ≠ 0) :
    ∃ Φ : Matrix (Fin m) (Fin m) (PowerSeries ℚ),
      (∀ i j, (Φ i j).coeff 0 = if i = j then 1 else 0) ∧
      (∀ i j, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (Φ i j)
        = ∑ k, (A i k : PowerSeries ℚ) * Φ k j) ∧
      IsUnit Φ.det := by
  -- `q` is a unit of `ℚ⟦X⟧` because its constant coefficient is non-zero
  have hunit : IsUnit ((q : PowerSeries ℚ)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [show (q : PowerSeries ℚ).coeff 0 = q.coeff 0 from by simp]
    exact isUnit_iff_ne_zero.mpr hq0
  obtain ⟨u, hu⟩ := hunit
  -- solve `Φ' = B Φ` with `B = u⁻¹ • A`
  obtain ⟨Φ, hΦ0, hΦode⟩ :=
    Work.ZeroEst3.fundamentalPhi m
      (fun i k => (↑(u⁻¹) : PowerSeries ℚ) * (A i k : PowerSeries ℚ))
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- initial condition
    intro i j
    rw [hΦ0 i j, Matrix.one_apply]
  · -- the ODE `q Φ' = A Φ`
    intro i j
    rw [hΦode i j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hu]
    have huu : (↑u : PowerSeries ℚ) * ↑(u⁻¹) = 1 := by simp
    calc (↑u : PowerSeries ℚ) * (↑(u⁻¹) * (A i k : PowerSeries ℚ) * Φ k j)
        = ((↑u : PowerSeries ℚ) * ↑(u⁻¹)) * ((A i k : PowerSeries ℚ) * Φ k j) := by ring
      _ = (A i k : PowerSeries ℚ) * Φ k j := by rw [huu, one_mul]
  · -- `det Φ` is a unit: it has constant coefficient `det 1 = 1`
    have hmap : PowerSeries.constantCoeff.mapMatrix Φ = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0 i j]
    have hdet : PowerSeries.constantCoeff Φ.det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    rw [PowerSeries.isUnit_iff_constantCoeff, hdet]
    exact isUnit_one

end Work.ZeroEst
