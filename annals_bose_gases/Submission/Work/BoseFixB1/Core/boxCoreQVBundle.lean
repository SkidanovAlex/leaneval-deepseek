import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.boxCoreQVBundle`

The two mode factors `boxCoreU`, `boxCoreV` are unimodular multiples of `χ`, hence have the same
norm; so the hypothesis `hχbdd` bounds `boxCoreU` on `A` as well. And `boxCoreQ` vanishes off
`A × A`. Therefore multiplying the (already integrable) doubly projected state `boxCoreQ` by
`boxCoreV` (in the `z` slot) or by `boxCoreU` (in the `y` slot) preserves integrability, both
slicewise and on the product measure. All the bounds used are *pointwise*: on `A` we use
`hχbdd`, off `A` the factor `boxCoreQ` — and with it the whole product — vanishes.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.BoseFixB1.Core

set_option maxHeartbeats 1000000

/-- `boxCoreU χ p y` and `boxCoreV χ p y` have the same norm: both are the unimodular multiple
`χ y` of a phase. -/
lemma boxCoreU_norm_eq (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (p y : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.BoseFixB1.boxCoreU χ p y‖ = ‖Work.BoseFixB1.boxCoreV χ p y‖ := by
  have hU : Complex.I * ((inner ℝ p y : ℝ) : ℂ) = ((inner ℝ p y : ℝ) : ℂ) * Complex.I :=
    mul_comm _ _
  have hV : -(Complex.I * ((inner ℝ p y : ℝ) : ℂ)) = (((-inner ℝ p y : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [Work.BoseFixB1.boxCoreU, Work.BoseFixB1.boxCoreV, norm_mul, norm_mul, hV, hU]
  simp only [Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `boxCoreV χ p` is continuous when `χ` is. -/
lemma continuous_boxCoreV {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3)) : Continuous fun z => Work.BoseFixB1.boxCoreV χ p z := by
  unfold Work.BoseFixB1.boxCoreV
  fun_prop

/-- `boxCoreU χ p` is continuous when `χ` is. -/
lemma continuous_boxCoreU {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3)) : Continuous fun y => Work.BoseFixB1.boxCoreU χ p y := by
  unfold Work.BoseFixB1.boxCoreU
  fun_prop

theorem boxCoreQVBundle {N : ℕ} {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχcont : Continuous χ)
    (p : EuclideanSpace ℝ (Fin 3))
    (hχbdd : ∃ C, ∀ z ∈ A, ‖Work.BoseFixB1.boxCoreV χ p z‖ ≤ C)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (i : Fin (N + 2)) (j' : Fin (N + 1))
    (x : Submission.BoseGases.X N)
    (hQint : ∀ y, MeasureTheory.IntegrableOn
        (fun z => ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)) A MeasureTheory.volume)
    (hQprod : MeasureTheory.Integrable
        (Function.uncurry (fun y z => ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)))
        ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A))) :
    (∀ y, MeasureTheory.IntegrableOn
        (fun z => Work.BoseFixB1.boxCoreV χ p z
          * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)) A MeasureTheory.volume)
    ∧ MeasureTheory.Integrable
        (Function.uncurry (fun y z => Work.BoseFixB1.boxCoreV χ p z
          * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)))
        ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A))
    ∧ MeasureTheory.Integrable
        (Function.uncurry (fun y z => Work.BoseFixB1.boxCoreU χ p y
          * (Work.BoseFixB1.boxCoreV χ p z
            * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ))))
        ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)) := by
  obtain ⟨C, hC⟩ := hχbdd
  have hCmax : ∀ z ∈ A, ‖Work.BoseFixB1.boxCoreV χ p z‖ ≤ max C 0 :=
    fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hVcont : Continuous fun z => Work.BoseFixB1.boxCoreV χ p z :=
    continuous_boxCoreV hχcont p
  have hUcont : Continuous fun y => Work.BoseFixB1.boxCoreU χ p y :=
    continuous_boxCoreU hχcont p
  have hUnorm : ∀ y, ‖Work.BoseFixB1.boxCoreU χ p y‖ = ‖Work.BoseFixB1.boxCoreV χ p y‖ :=
    fun y => boxCoreU_norm_eq χ p y
  have h1 : ∀ y, MeasureTheory.IntegrableOn
      (fun z => Work.BoseFixB1.boxCoreV χ p z
        * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)) A MeasureTheory.volume := by
    intro y
    have hdom : Integrable (fun z =>
        max C 0 * ‖((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)‖)
        (volume.restrict A) :=
      (hQint y).norm.const_mul (max C 0)
    refine Integrable.mono' hdom ?_ ?_
    · exact hVcont.aestronglyMeasurable.mul (hQint y).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => by
        by_cases hz : z ∈ A
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hCmax z hz) (norm_nonneg _)
        · have hQz : Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z = 0 :=
            Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_right i j' x hz
          rw [hQz]
          simp
  have h2 : MeasureTheory.Integrable
      (Function.uncurry (fun y z => Work.BoseFixB1.boxCoreV χ p z
        * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ)))
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)) := by
    show Integrable (fun t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.boxCoreV χ p t.2
        * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 : ℝ) : ℂ))
      ((volume.restrict A).prod (volume.restrict A))
    have hdom : Integrable (fun t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        max C 0 * ‖((Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 : ℝ) : ℂ)‖)
        ((volume.restrict A).prod (volume.restrict A)) :=
      (hQprod.norm).const_mul (max C 0)
    refine Integrable.mono' hdom ?_ ?_
    · exact ((hVcont.comp continuous_snd).aestronglyMeasurable).mul hQprod.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        by_cases hz : t.2 ∈ A
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hCmax t.2 hz) (norm_nonneg _)
        · have hQz : Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 = 0 :=
            Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_right i j' x hz
          rw [hQz]
          simp
  have h3 : MeasureTheory.Integrable
      (Function.uncurry (fun y z => Work.BoseFixB1.boxCoreU χ p y
        * (Work.BoseFixB1.boxCoreV χ p z
          * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x y z : ℝ) : ℂ))))
      ((MeasureTheory.volume.restrict A).prod (MeasureTheory.volume.restrict A)) := by
    show Integrable (fun t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.boxCoreU χ p t.1
        * (Work.BoseFixB1.boxCoreV χ p t.2
          * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 : ℝ) : ℂ)))
      ((volume.restrict A).prod (volume.restrict A))
    have hdom : Integrable (fun t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        max C 0 * ‖Work.BoseFixB1.boxCoreV χ p t.2
          * ((Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 : ℝ) : ℂ)‖)
        ((volume.restrict A).prod (volume.restrict A)) :=
      (h2.norm).const_mul (max C 0)
    refine Integrable.mono' hdom ?_ ?_
    · exact ((hUcont.comp continuous_fst).aestronglyMeasurable).mul h2.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        by_cases hy : t.1 ∈ A
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (le_trans (le_of_eq (hUnorm t.1)) (hCmax t.1 hy)) (norm_nonneg _)
        · have hQy : Work.BoseFixB1.boxCoreQ volA A Φ i j' x t.1 t.2 = 0 :=
            Work.BoseFixB1.boxCoreQ_eq_zero_of_notMem_left i j' x hy
          rw [hQy]
          simp
  exact ⟨h1, h2, h3⟩

end Work.BoseFixB1.Core
