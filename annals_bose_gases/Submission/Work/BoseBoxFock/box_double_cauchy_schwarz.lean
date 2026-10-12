import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.periodic_double_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

open MeasureTheory

/-- **Cauchy–Schwarz (Hilbert–Schmidt) for double integrals.**  On a finite measure space `(X, μ)`
the iterated integral of a product of two bounded, a.e. strongly measurable kernels `D`, `G` is
bounded by the product of the `L²` norms of the two factors:

`‖∫_w ∫_y D w y · G w y‖ ≤ √(∫_w ∫_y ‖D w y‖²) · √(∫_w ∫_y ‖G w y‖²)`.

Everything is phrased on the product measure `μ ⊗ μ`, so no measurability of a partial integral is
needed: Fubini (`MeasureTheory.integral_prod`, applicable because both integrands are bounded and
`μ ⊗ μ` is finite) identifies the iterated integral with the integral against `μ ⊗ μ`, and the
`L²` Cauchy–Schwarz inequality on `(X × X, μ ⊗ μ)` (`Work.BoseBoxFock.norm_integral_mul_le_sqrt`)
finishes. -/
theorem double_integral_cauchy_schwarz {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {D G : X → X → ℂ}
    (hDm : AEStronglyMeasurable (Function.uncurry D) (μ.prod μ))
    (hGm : AEStronglyMeasurable (Function.uncurry G) (μ.prod μ))
    (hDb : ∃ C : ℝ, ∀ w y, ‖D w y‖ ≤ C) (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) :
    ‖∫ w, ∫ y, D w y * G w y ∂μ ∂μ‖
      ≤ Real.sqrt (∫ w, ∫ y, ‖D w y‖ ^ 2 ∂μ ∂μ)
        * Real.sqrt (∫ w, ∫ y, ‖G w y‖ ^ 2 ∂μ ∂μ) := by
  obtain ⟨CD, hD⟩ := hDb
  obtain ⟨CG, hG⟩ := hGb
  -- replace the bounds by nonnegative ones (this costs nothing and avoids assuming `0 ≤ C`)
  have hCD : ∀ w y, ‖D w y‖ ≤ max CD 0 := fun w y => le_trans (hD w y) (le_max_left _ _)
  have hCG : ∀ w y, ‖G w y‖ ≤ max CG 0 := fun w y => le_trans (hG w y) (le_max_left _ _)
  have hDm' : AEStronglyMeasurable (fun p : X × X => D p.1 p.2) (μ.prod μ) := hDm
  have hGm' : AEStronglyMeasurable (fun p : X × X => G p.1 p.2) (μ.prod μ) := hGm
  -- integrability of the three uncurried integrands (bounded on a finite measure space)
  have hprod : Integrable (fun p : X × X => D p.1 p.2 * G p.1 p.2) (μ.prod μ) := by
    refine Integrable.of_bound (hDm'.mul hGm') (max CD 0 * max CG 0) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul (hCD p.1 p.2) (hCG p.1 p.2) (norm_nonneg _) (le_max_right _ _)
  have hsqD : Integrable (fun p : X × X => ‖D p.1 p.2‖ ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound (hDm'.norm.pow 2) ((max CD 0) ^ 2) ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCD p.1 p.2) 2
  have hsqG : Integrable (fun p : X × X => ‖G p.1 p.2‖ ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound (hGm'.norm.pow 2) ((max CG 0) ^ 2) ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hCG p.1 p.2) 2
  -- Fubini: the iterated integrals are integrals against the product measure
  have hFub : ∫ w, ∫ y, D w y * G w y ∂μ ∂μ
      = ∫ p : X × X, D p.1 p.2 * G p.1 p.2 ∂(μ.prod μ) :=
    (integral_prod _ hprod).symm
  have hFubD : ∫ w, ∫ y, ‖D w y‖ ^ 2 ∂μ ∂μ
      = ∫ p : X × X, ‖D p.1 p.2‖ ^ 2 ∂(μ.prod μ) :=
    (integral_prod _ hsqD).symm
  have hFubG : ∫ w, ∫ y, ‖G w y‖ ^ 2 ∂μ ∂μ
      = ∫ p : X × X, ‖G p.1 p.2‖ ^ 2 ∂(μ.prod μ) :=
    (integral_prod _ hsqG).symm
  rw [hFub, hFubD, hFubG]
  exact norm_integral_mul_le_sqrt hDm' hGm' ⟨max CD 0, fun p => hCD p.1 p.2⟩
    ⟨max CG 0, fun p => hCG p.1 p.2⟩

theorem box_double_cauchy_schwarz {ℓ : ℝ} (hℓ : 0 < ℓ)
    {D G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hDm : MeasureTheory.AEStronglyMeasurable (Function.uncurry D)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))))
    (hGm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)).prod
        (MeasureTheory.volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))))
    (hDb : ∃ C : ℝ, ∀ w y, ‖D w y‖ ≤ C) (hGb : ∃ C : ℝ, ∀ w y, ‖G w y‖ ≤ C) :
    ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, D w y * G w y‖
      ≤ Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖D w y‖ ^ 2)
        * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖G w y‖ ^ 2) := by
  -- the corpus box is a genuine box, hence carries finite volume
  haveI hfin : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Work.BoseK15.corpusBox.boxL ℓ)) := by
    rw [Work.BoseBoxFock.corpusBox_boxL_eq_cell hℓ, MeasureTheory.isFiniteMeasure_restrict,
      Work.BoseFixR.cell_eq_boxL]
    exact Work.BoseFixR.volume_boxL_ne_top ℓ
  exact Work.BoseBoxFock.double_integral_cauchy_schwarz hDm hGm hDb hGb

end Work.BoseBoxFock
