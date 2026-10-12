import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.norm_integral_mul_le_sqrt
import Submission.Work.BoseBoxFock.periodic_double_fold
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Pointwise

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus box `Λ(ℓ) = ℓ • [-1/2,1/2]³` of `Work.BoseK15.corpusBox` is the closed cube
`[-ℓ/2, ℓ/2]³ = Work.BoseFixR.cell ℓ` (for `ℓ > 0`). -/
lemma corpusBox_boxL_eq_cell {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.boxL ℓ = Work.BoseFixR.cell ℓ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Work.BoseFixR.mem_cell]
    intro i
    have hyi : |y i| ≤ 1 / 2 := by
      simpa [Work.BoseB4.unitCell] using hy i
    have h1 : (ℓ • y) i = ℓ * y i := by simp
    rw [h1, abs_mul, abs_of_pos hℓ]
    have := mul_le_mul_of_nonneg_left hyi (le_of_lt hℓ)
    linarith
  · intro hx
    refine ⟨ℓ⁻¹ • x, ?_, ?_⟩
    · change ∀ i, |(ℓ⁻¹ • x) i| ≤ 1 / 2
      intro i
      have hxi : |x i| ≤ ℓ / 2 := (Work.BoseFixR.mem_cell.mp hx) i
      have h1 : (ℓ⁻¹ • x) i = ℓ⁻¹ * x i := by simp
      rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
      have hmul : ℓ⁻¹ * |x i| ≤ ℓ⁻¹ * (ℓ / 2) :=
        mul_le_mul_of_nonneg_left hxi (le_of_lt (inv_pos.mpr hℓ))
      have heq : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
      linarith
    · show ℓ • (ℓ⁻¹ • x) = x
      exact smul_inv_smul₀ hℓ.ne' x

theorem periodic_double_integral_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : EuclideanSpace ℝ (Fin 3) → ℂ}
      {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ},
      (∀ (m : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)),
        D (z + ℓ • Work.BoseBoxFock.latVec m) = D z) →
      Measurable D →
      (∃ K : ℝ, ∀ z, ‖D z‖ ≤ K) →
      Measurable (Function.uncurry G) →
      (∃ K : ℝ, ∀ w y, ‖G w y‖ ≤ K) →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, D (w - y) * G w y‖
        ≤ C * Real.sqrt (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖D z‖ ^ 2)
            * Real.sqrt (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
                ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖G w y‖ ^ 2) := by
  refine ⟨Real.sqrt (ℓ ^ 3), Real.sqrt_nonneg _, ?_⟩
  intro D G hper hDmeas hDbdd hGmeas hGbdd
  obtain ⟨KD, hKD⟩ := hDbdd
  obtain ⟨KG, hKG⟩ := hGbdd
  -- move everything to the closed box `[-ℓ/2,ℓ/2]³ = Work.BoseFixR.cell ℓ`
  rw [corpusBox_boxL_eq_cell hℓ]
  -- the restricted measure is finite (the box has volume `ℓ³`)
  have hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Work.BoseFixR.cell ℓ)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Work.BoseFixR.cell_eq_boxL,
      Work.BoseFixR.volume_boxL]
    exact ENNReal.ofReal_ne_top
  set μ : Measure E3 := (volume : Measure E3).restrict (Work.BoseFixR.cell ℓ) with hμdef
  haveI : IsFiniteMeasure μ := hfin
  -- measurability of the two factors of the uncurried integrand
  have hmD : Measurable (fun p : E3 × E3 => D (p.1 - p.2)) :=
    hDmeas.comp (continuous_fst.sub continuous_snd).measurable
  have hmG : Measurable (fun p : E3 × E3 => G p.1 p.2) := hGmeas
  -- integrability of the uncurried integrand (bounded on a finite measure space)
  have hFint : Integrable (fun p : E3 × E3 => D (p.1 - p.2) * G p.1 p.2) (μ.prod μ) := by
    refine Integrable.of_bound (hmD.mul hmG).aestronglyMeasurable (KD * KG) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul (hKD _) (hKG _ _) (norm_nonneg _)
      (le_trans (norm_nonneg (D 0)) (hKD 0))
  -- Fubini: the iterated integral is the integral against the product measure
  have hFub : ∫ w, ∫ y, D (w - y) * G w y ∂μ ∂μ
      = ∫ p : E3 × E3, D (p.1 - p.2) * G p.1 p.2 ∂(μ.prod μ) :=
    (integral_prod _ hFint).symm
  -- integrability of `‖D(p.1-p.2)‖²` and `‖G(p.1,p.2)‖²`
  have hDsq : Integrable (fun p : E3 × E3 => ‖D (p.1 - p.2)‖ ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound ((hmD.norm.pow_const 2).aestronglyMeasurable) (KD ^ 2) ?_
    filter_upwards with p
    have h1 : ‖(‖D (p.1 - p.2)‖ ^ 2 : ℝ)‖ = ‖D (p.1 - p.2)‖ ^ 2 :=
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) (hKD _) 2
  have hGsq : Integrable (fun p : E3 × E3 => ‖G p.1 p.2‖ ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound ((hmG.norm.pow_const 2).aestronglyMeasurable) (KG ^ 2) ?_
    filter_upwards with p
    have h1 : ‖(‖G p.1 p.2‖ ^ 2 : ℝ)‖ = ‖G p.1 p.2‖ ^ 2 :=
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) (hKG _ _) 2
  -- the folded first factor and the second factor
  have hDfold : ∫ p : E3 × E3, ‖D (p.1 - p.2)‖ ^ 2 ∂(μ.prod μ)
      = ℓ ^ 3 * ∫ z, ‖D z‖ ^ 2 ∂μ := by
    rw [integral_prod _ hDsq]
    exact periodic_double_fold hℓ (h := fun z => ‖D z‖ ^ 2) (fun m z => by rw [hper m z])
  have hGprod : ∫ p : E3 × E3, ‖G p.1 p.2‖ ^ 2 ∂(μ.prod μ)
      = ∫ w, ∫ y, ‖G w y‖ ^ 2 ∂μ ∂μ :=
    integral_prod _ hGsq
  rw [hFub]
  calc ‖∫ p : E3 × E3, D (p.1 - p.2) * G p.1 p.2 ∂(μ.prod μ)‖
      ≤ Real.sqrt (∫ p : E3 × E3, ‖D (p.1 - p.2)‖ ^ 2 ∂(μ.prod μ))
          * Real.sqrt (∫ p : E3 × E3, ‖G p.1 p.2‖ ^ 2 ∂(μ.prod μ)) :=
        norm_integral_mul_le_sqrt (X := E3 × E3) (μ := μ.prod μ)
          (f := fun p : E3 × E3 => D (p.1 - p.2)) (g := fun p : E3 × E3 => G p.1 p.2)
          hmD.aestronglyMeasurable hmG.aestronglyMeasurable
          ⟨KD, fun p => hKD _⟩ ⟨KG, fun p => hKG _ _⟩
    _ = Real.sqrt (ℓ ^ 3 * ∫ z, ‖D z‖ ^ 2 ∂μ)
          * Real.sqrt (∫ w, ∫ y, ‖G w y‖ ^ 2 ∂μ ∂μ) := by
        rw [hDfold, hGprod]
    _ = Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ z, ‖D z‖ ^ 2 ∂μ)
          * Real.sqrt (∫ w, ∫ y, ‖G w y‖ ^ 2 ∂μ ∂μ) := by
        rw [Real.sqrt_mul (by positivity)]

end Work.BoseBoxFock
