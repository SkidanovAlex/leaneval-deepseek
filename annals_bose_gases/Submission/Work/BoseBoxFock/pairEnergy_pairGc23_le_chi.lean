import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGChiAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

theorem pairEnergy_pairGc23_le_chi {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * Work.BoseBoxFock.memX23 ℓ p Θ₀ w y * Work.BoseBoxFock.pinL2 ℓ Θ₀) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ (fun w' => Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * Work.BoseBoxFock.dirX23 ℓ p Θ₀ z.1 z.2 * Work.BoseBoxFock.pinL2 ℓ Θ₀) →
      Continuous (Function.uncurry (Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B)) →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.memX23 ℓ p Θ₀ z.1 z.2) = Work.BoseBoxFock.pinL2 ℓ Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ, ‖Work.BoseBoxFock.chiS ℓ z.1‖ ^ 2 * Work.BoseBoxFock.dirX23 ℓ p Θ₀ z.1 z.2) ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ →
      Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 ℓ Θ₀ * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by
  obtain ⟨Cg, hCg0, hCg⟩ := pairEnergy_le_of_integral_bounds_chi (ℓ := ℓ) hℓ
  refine ⟨Cg * ℓ ^ 6, by positivity, ?_⟩
  intro p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceM hsliceD
  obtain ⟨CM, hCM0, hCM⟩ := memX23_le hℓ p hΘ₀.continuous
  obtain ⟨CD, hCD0, hCD⟩ := dirX23_le hℓ p hΘ₀
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinD0 : 0 ≤ pinDirChi ℓ Θ₀ := pinDirChi_nonneg ℓ Θ₀
  have hcs0 : 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 :=
    mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)
  have hM0 : ∀ z : E3 × E3, 0 ≤ memX23 ℓ p Θ₀ z.1 z.2 :=
    fun z => integral_nonneg fun x => by positivity
  have hD0 : ∀ z : E3 × E3, 0 ≤ dirX23 ℓ p Θ₀ z.1 z.2 :=
    fun z => Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hMs : StronglyMeasurable (Function.uncurry (memX23 ℓ p Θ₀)) :=
    stronglyMeasurable_memX23 (ℓ := ℓ) p hΘ₀.continuous
  have hDs : StronglyMeasurable (Function.uncurry (dirX23 ℓ p Θ₀)) :=
    stronglyMeasurable_dirX23 (ℓ := ℓ) p hΘ₀
  have hP0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀ :=
    fun z => mul_nonneg (mul_nonneg hcs0 (hM0 z)) hpin0
  have hQ0 : ∀ z : E3 × E3,
      0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀ :=
    fun z => mul_nonneg (mul_nonneg hcs0 (hD0 z)) hpin0
  have hPint : IntegrableOn (fun z : E3 × E3 =>
      cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * CM * pinL2 ℓ Θ₀) ?_ ?_
    · exact ((hMs.const_mul (cA ^ 2 * cB ^ 2 * ℓ ^ 6)).mul_const
        (pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 z)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hCM z.1 hz.1 z.2 hz.2) hcs0) hpin0
  -- integrability of `‖χ_ℓ(w)‖² · Q`
  have hWQint : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 *
      (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀))
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * CD * pinL2 ℓ Θ₀)) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2) volume :=
        (((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun z : E3 × E3 =>
          cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀) volume :=
        ((hDs.const_mul (cA ^ 2 * cB ^ 2 * ℓ ^ 6)).mul_const (pinL2 ℓ Θ₀)).aestronglyMeasurable
      exact (h1.mul h2).mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hQ0 z))]
      calc ‖chiS ℓ z.1‖ ^ 2
            * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
          ≤ Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀) :=
            mul_le_mul_of_nonneg_right (hKc z.1) (hQ0 z)
        _ ≤ Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * CD * pinL2 ℓ Θ₀) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hCD z.1 hz.1 z.2 hz.2) hcs0) hpin0) hKc0
  have hP : (∫ z in boxL ℓ ×ˢ boxL ℓ,
        cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀ := by
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, hsliceM]
  have hQ : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 *
        (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀))
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀ := by
    have hEq : (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 *
          (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀))
        = fun z : E3 × E3 => (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀) *
            (‖chiS ℓ z.1‖ ^ 2 * dirX23 ℓ p Θ₀ z.1 z.2) := by
      funext z; ring
    rw [hEq, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hsliceD (mul_nonneg hcs0 hpin0)
  have hC := hCg (G := pairGc23 ℓ p hp Θ₀ A B)
    (P := fun z : E3 × E3 => cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
    (Q := fun z : E3 × E3 => cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀)
    (A := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀)
    (B := cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
    (by positivity) (by positivity) hP0 hQ0
    (fun z => hval z.1 z.2) (fun z => hdb z) hder hcont hPint hWQint hP hQ
  have h1 : Cg * (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀
        + cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
      = (Cg * ℓ ^ 6) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    ring
  linarith [hC, h1.le]

end Work.BoseBoxFock
