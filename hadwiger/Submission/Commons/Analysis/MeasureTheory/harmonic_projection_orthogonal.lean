import Mathlib
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_orthonormal_basis
import Submission.Commons.Analysis.MeasureTheory.sphere_restriction_pairing_pos

open MeasureTheory

namespace Commons.Analysis.MeasureTheory

/-!
### Orthogonality of the orthonormal projection on a measure space

Let `(α, μ)` be a measure space, `Y : Fin d → α → ℝ` an orthonormal family in
`L²(μ)` (i.e. `∫ x, Y i x * Y j x ∂μ = if i = j then 1 else 0`), and `a : α → ℝ`
a function integrable against every `Y j`.  The "projection" of `a` onto the span
of the `Y j` is `∑ j, (∫ y, a y * Y j y ∂μ) * Y j`.  These lemmas show that this
projection is orthogonal (in the `L²`-pairing) to every `Y l`, and hence to every
element `H` of the span of the `Y j` (when `H` is given pointwise as a finite
linear combination of the `Y j`).

They are stated abstractly over an arbitrary measure space so that they apply
verbatim to the sphere `S^{n-1}` with its surface measure `volume.toSphere`.
-/

/-- Integrability of `(a - projection) * Y l`. -/
theorem orthonormal_integrable_proj_mul
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {d : ℕ} (Y : Fin d → α → ℝ) (a : α → ℝ)
    (hYint : ∀ i j, MeasureTheory.Integrable (fun x => Y i x * Y j x) μ)
    (haint : ∀ j, MeasureTheory.Integrable (fun x => a x * Y j x) μ)
    (l : Fin d) :
    MeasureTheory.Integrable
      (fun x => (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x) μ := by
  have hcongr : (fun x => (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x)
      = (fun x => a x * Y l x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * (Y j x * Y l x)) := by
    funext x
    simp only [sub_mul]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcongr]
  exact (haint l).sub (MeasureTheory.integrable_finsetSum Finset.univ
    (fun j _ => (hYint j l).const_mul _))

/-- The orthonormal projection of `a` is orthogonal to `Y l`. -/
theorem orthonormal_projection_integral_zero
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {d : ℕ} (Y : Fin d → α → ℝ) (a : α → ℝ)
    (hYint : ∀ i j, MeasureTheory.Integrable (fun x => Y i x * Y j x) μ)
    (horth : ∀ i j, (∫ x, Y i x * Y j x ∂μ) = if i = j then 1 else 0)
    (haint : ∀ j, MeasureTheory.Integrable (fun x => a x * Y j x) μ)
    (l : Fin d) :
    (∫ x, (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x ∂μ) = 0 := by
  have hcongr : (fun x => (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x)
      = (fun x => a x * Y l x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * (Y j x * Y l x)) := by
    funext x
    simp only [sub_mul]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcongr]
  rw [MeasureTheory.integral_sub (haint l) (MeasureTheory.integrable_finsetSum Finset.univ
        (fun j _ => (hYint j l).const_mul _))]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => (hYint j l).const_mul _)]
  simp only [MeasureTheory.integral_const_mul]
  simp only [horth]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- The orthonormal projection of `a` is orthogonal to any element of the span of
the `Y l`, given pointwise as a finite linear combination of the `Y l`. -/
theorem orthonormal_projection_integral_eq_zero
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {d : ℕ} (Y : Fin d → α → ℝ) (a : α → ℝ) (H : α → ℝ)
    (hYint : ∀ i j, MeasureTheory.Integrable (fun x => Y i x * Y j x) μ)
    (horth : ∀ i j, (∫ x, Y i x * Y j x ∂μ) = if i = j then 1 else 0)
    (haint : ∀ j, MeasureTheory.Integrable (fun x => a x * Y j x) μ)
    (hrep : ∃ c' : Fin d → ℝ, ∀ x, H x = ∑ l : Fin d, c' l * Y l x) :
    (∫ x, (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * H x ∂μ) = 0 := by
  obtain ⟨c', hc'⟩ := hrep
  have h1 : (∫ x, (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * H x ∂μ)
      = ∫ x, (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) *
          (∑ l : Fin d, c' l * Y l x) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hc' x]
  rw [h1]
  have h2 : (fun x => (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) *
          (∑ l : Fin d, c' l * Y l x))
      = (fun x => ∑ l : Fin d, c' l *
          ((a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x)) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h2]
  rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun l _ => (orthonormal_integrable_proj_mul Y a hYint haint l).const_mul _)]
  simp only [MeasureTheory.integral_const_mul]
  have hz : ∀ l : Fin d,
      (∫ x, (a x - ∑ j : Fin d, (∫ y, a y * Y j y ∂μ) * Y j x) * Y l x ∂μ) = 0 :=
    fun l => orthonormal_projection_integral_zero Y a hYint horth haint l
  simp only [hz, mul_zero]
  simp

set_option linter.unusedVariables false in
theorem harmonic_projection_orthogonal
    {n : ℕ} {k : ℕ} [Nonempty (Fin n)]
    (d : ℕ) (Y : Fin d → MvPolynomial (Fin n) ℝ)
    (hY : (∀ j : Fin d, Y j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k ∧
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (Y j))) = 0) ∧
      (∀ i j : Fin d,
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y i) *
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j)
          ∂MeasureTheory.volume.toSphere) = if i = j then 1 else 0) ∧
      (∀ H : MvPolynomial (Fin n) ℝ,
        H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
        (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0 →
        ∃ c : Fin d → ℝ, ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) H =
            ∑ j : Fin d, c j * MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j)))
    (H : MvPolynomial (Fin n) ℝ)
    (hH : H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapH : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hintY : ∀ j : Fin d, MeasureTheory.Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => a θ *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j))
      MeasureTheory.volume.toSphere)
    (haint : MeasureTheory.Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => a θ *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) H)
      MeasureTheory.volume.toSphere) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (a θ - ∑ j : Fin d,
            (∫ φ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
                a φ * MvPolynomial.eval (fun l : Fin n => (φ : EuclideanSpace ℝ (Fin n)) l) (Y j)
              ∂MeasureTheory.volume.toSphere) *
            MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j)) *
        MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) H
      ∂MeasureTheory.volume.toSphere) = 0 := by
  obtain ⟨c', hc'⟩ := hY.2.2 H hH hlapH
  exact orthonormal_projection_integral_eq_zero
    (Y := fun j (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
      MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) (Y j))
    (a := a)
    (H := fun (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
      MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) H)
    (hYint := fun i j => Commons.Algebra.MvPolynomial.integrable_eval_mul (Y i) (Y j))
    (horth := fun i j => hY.2.1 i j)
    (haint := fun j => hintY j)
    ⟨c', hc'⟩

end Commons.Analysis.MeasureTheory
