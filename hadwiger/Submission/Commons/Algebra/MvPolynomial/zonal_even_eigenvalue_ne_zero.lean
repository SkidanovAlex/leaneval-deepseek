import Mathlib
import Submission.Commons.Algebra.MvPolynomial.zonal_radial
import Submission.Commons.Algebra.MvPolynomial.zonal_integral_ne_zero
import Submission.Commons.Algebra.MvPolynomial.zonal_pole_value_ne_zero
import Submission.Commons.Analysis.MeasureTheory.zonal_normalized_eigenvalue
import Submission.Commons.Analysis.MeasureTheory.zonal_fibre_integral_abs_poly

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory
open scoped BigOperators

namespace Commons.Algebra.MvPolynomial

/-- The fibre sphere of the coordinate hyperplane `j ≠ i` has nonzero surface measure. -/
private theorem fibreSphere_measureReal_ne_zero {n : ℕ} (i : Fin n) (hn : 2 ≤ n) :
    (MeasureTheory.volume.toSphere :
        Measure (Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1)).real Set.univ
      ≠ 0 := by
  have hcard : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  haveI : Nonempty {j : Fin n // j ≠ i} := ⟨⟨j, hj⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ {j : Fin n // j ≠ i}) := inferInstance
  have hne : (MeasureTheory.volume.toSphere :
      Measure (Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1)) ≠ 0 :=
    MeasureTheory.Measure.toSphere_ne_zero (MeasureTheory.volume)
  have huniv : (MeasureTheory.volume.toSphere :
      Measure (Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1)) Set.univ ≠ 0 :=
    fun h => hne (MeasureTheory.Measure.measure_univ_eq_zero.mp h)
  rw [MeasureTheory.measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨huniv, MeasureTheory.measure_ne_top _ _⟩

theorem zonal_even_eigenvalue_ne_zero
    {n : ℕ} {m : ℕ} (i : Fin n) (hn : 2 ≤ n)
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZmem : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m))
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hRmem : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m - 2))
    (hdec : ((∑ j : Fin n, (MvPolynomial.C ((EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) j)) * (MvPolynomial.X j)) ^ (2 * m)) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R)
    (c : ℝ)
    (hsc : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
            MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
        ∂MeasureTheory.volume.toSphere) = c * MvPolynomial.eval (fun j : Fin n => (u : EuclideanSpace ℝ (Fin n)) j) Z) :
    c ≠ 0 := by
  classical
  -- The zonal profile polynomial `P` with `Z(θ) = P(θᵢ)` on the sphere and non-vanishing
  -- weighted one-dimensional integral.
  obtain ⟨P, hPrad, hPint⟩ := zonal_integral_ne_zero i hn Z R hZmem hlapZ hRmem hdec
  -- The pole `eᵢ` of the sphere.
  have hmem : (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm]
    simp
  let eS : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨EuclideanSpace.single i (1 : ℝ), hmem⟩
  have heScoe : (eS : EuclideanSpace ℝ (Fin n)) = EuclideanSpace.single i (1 : ℝ) := rfl
  -- The sphere integral tested at the pole is nonzero.
  have hint : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |inner ℝ (eS : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
          MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
      ∂MeasureTheory.volume.toSphere) ≠ 0 := by
    have h1 : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (eS : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
            MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) Z
        ∂MeasureTheory.volume.toSphere)
        = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |(θ : EuclideanSpace ℝ (Fin n)) i| *
              Polynomial.eval ((θ : EuclideanSpace ℝ (Fin n)) i) P
          ∂MeasureTheory.volume.toSphere) := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [hPrad θ]
      congr 1
      rw [heScoe, EuclideanSpace.inner_single_left]
      simp
    rw [h1, Commons.Analysis.MeasureTheory.zonal_fibre_integral_abs_poly i hn P]
    set s : ℝ := (MeasureTheory.volume.toSphere :
      Measure (Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1)).real Set.univ with hs
    have hsne : s ≠ 0 := by rw [hs]; exact fibreSphere_measureReal_ne_zero i hn
    have hstep : (∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
              (|t| * Polynomial.eval t P) *
                (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
            ∂MeasureTheory.volume.toSphere))
        = s * (∫ t : ℝ in Set.Ioo (-1) 1,
              |t| * Polynomial.eval t P *
                (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)) := by
      have hinner : ∀ t : ℝ,
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
              (|t| * Polynomial.eval t P) *
                (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
            ∂MeasureTheory.volume.toSphere)
          = s * ((|t| * Polynomial.eval t P) *
                (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)) := by
        intro t
        rw [hs, MeasureTheory.integral_const]
        simp
      have hcong : (∫ t : ℝ in Set.Ioo (-1) 1,
            (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
                (|t| * Polynomial.eval t P) *
                  (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
              ∂MeasureTheory.volume.toSphere))
          = ∫ t : ℝ in Set.Ioo (-1) 1,
              s * ((|t| * Polynomial.eval t P) *
                (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hinner t]
      rw [hcong, MeasureTheory.integral_const_mul]
    rw [hstep]
    exact mul_ne_zero hsne hPint
  -- Testing `hsc` at the pole gives `c * Z(eᵢ) ≠ 0`.
  have hz : c * (MvPolynomial.eval (fun j : Fin n => (eS : EuclideanSpace ℝ (Fin n)) j) Z)
      ≠ 0 := by
    rw [← hsc eS]
    exact hint
  intro hc
  exact hz (by rw [hc, zero_mul])

end Commons.Algebra.MvPolynomial
