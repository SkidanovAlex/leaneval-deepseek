import Mathlib
import Submission.Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_ne_zero
import Submission.Commons.Analysis.MeasureTheory.cosine_harmonic_scalar
import Submission.Commons.Algebra.MvPolynomial.exists_zonalHarmonic

namespace Commons.Analysis.MeasureTheory

set_option linter.style.haveILetI false

open scoped BigOperators

/-- The Funk--Hecke eigenvalue of the cosine transform is uniform on the space of
harmonic homogeneous polynomials of a fixed degree: there is one scalar `c`,
depending only on the dimension `n` and the degree `k`, such that for every
harmonic homogeneous polynomial `P` of degree `k` and every unit vector `u`,
`∫ |⟨u,θ⟩| P(θ) dθ = c · P(u)`. -/
lemma cosine_harmonic_scalar_uniform {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ c : ℝ, ∀ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
          ∂MeasureTheory.volume.toSphere) =
        c * MvPolynomial.eval (fun i : Fin n => (u : EuclideanSpace ℝ (Fin n)) i) P := by
  classical
  obtain ⟨c, hc⟩ :=
    harmonic_cosine_integral_axis_scalar (n := n) (k := k) (hn2 := hn2)
  refine ⟨c, ?_⟩
  intro P hPh hPlap u
  have he0norm : ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    FhCHS5.e0Vec_unit n
  obtain ⟨L, hLu⟩ := Fh1.exists_isometry_unit (n := n)
    (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (u : EuclideanSpace ℝ (Fin n))
    he0norm (mem_sphere_zero_iff_norm.mp u.2)
  let Q : MvPolynomial (Fin n) ℝ := Fh2.substA n L P
  have hQh : Q ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    dsimp only [Q]
    exact Fh2.substA_mem_homogeneous n L hPh
  have hQlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0 := by
    dsimp only [Q]
    rw [Fh2.substA_lap n L P, hPlap]
    simp [Fh2.substA]
  have hLu' : L (FhCHS5.e0Vec n) = (u : FhCHS5.E n) := by
    simpa [FhCHS5.e0Vec, FhCHS.axisVec] using hLu
  have hrot := FhCHS5.cosine_transform_rotate n L P
  rw [hLu'] at hrot
  have hQeval : MvPolynomial.eval
        (fun i : Fin n => (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) i) Q
      = MvPolynomial.eval (fun i : Fin n => (u : EuclideanSpace ℝ (Fin n)) i) P := by
    dsimp only [Q]
    rw [FhCHS.substA_eval' n L P (EuclideanSpace.single (0 : Fin n) (1 : ℝ)), hLu]
  have hax := hc Q hQh hQlap
  calc
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
          MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
      ∂MeasureTheory.volume.toSphere)
        = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            |inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n))
              (θ : EuclideanSpace ℝ (Fin n))| *
              MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) Q
          ∂MeasureTheory.volume.toSphere) := by
          simpa [FhCHS5.e0Vec, FhCHS.axisVec] using hrot.symm
    _ = c * MvPolynomial.eval
          (fun i : Fin n => (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)) i) Q :=
          hax
    _ = c * MvPolynomial.eval (fun i : Fin n => (u : EuclideanSpace ℝ (Fin n)) i) P := by
          rw [hQeval]

theorem cosine_even_degree_scalar_ne_zero
    {n : ℕ} {m : ℕ} (hn : 2 ≤ n)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hg : ∃ P : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2 * m) ∧
      (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j P)) = 0 ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g θ = MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P)
    (hgne : ∃ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g u ≠ 0)
    (c : ℝ)
    (hsc : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g θ
        ∂MeasureTheory.volume.toSphere) = c * g u) :
    c ≠ 0 := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨P, hPh, hPlap, hPg⟩ := hg
  obtain ⟨u0, hu0⟩ := hgne
  obtain ⟨cdeg, hdeg⟩ := cosine_harmonic_scalar_uniform (n := n) (k := 2 * m) hn
  have hint_eq : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |inner ℝ (u0 : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g θ
      ∂MeasureTheory.volume.toSphere) = cdeg * g u0 := by
    calc
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          |inner ℝ (u0 : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| * g θ
        ∂MeasureTheory.volume.toSphere)
          = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              |inner ℝ (u0 : EuclideanSpace ℝ (Fin n)) (θ : EuclideanSpace ℝ (Fin n))| *
                MvPolynomial.eval (fun j : Fin n => (θ : EuclideanSpace ℝ (Fin n)) j) P
            ∂MeasureTheory.volume.toSphere) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with θ
              rw [hPg θ]
      _ = cdeg * MvPolynomial.eval (fun j : Fin n => (u0 : EuclideanSpace ℝ (Fin n)) j) P :=
              hdeg P hPh hPlap u0
      _ = cdeg * g u0 := by rw [hPg u0]
  have hc_eq : c = cdeg := by
    refine mul_right_cancel₀ hu0 ?_
    rw [← hsc u0, hint_eq]
  rw [hc_eq]
  obtain ⟨Z, R, hZmem, hZlap, hRmem, hZdec⟩ :=
    Commons.Algebra.MvPolynomial.exists_zonalHarmonic (n := n) (k := 2 * m)
      (a := (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : EuclideanSpace ℝ (Fin n)))
  refine Commons.Algebra.MvPolynomial.zonal_even_eigenvalue_ne_zero (0 : Fin n) hn
    Z R hZmem hZlap hRmem ?_ cdeg ?_
  · simpa using hZdec
  · intro u
    exact hdeg Z hZmem hZlap u

end Commons.Analysis.MeasureTheory
