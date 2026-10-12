import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integralBoundsChiParam
import Submission.Work.BoseBoxFock.pairGSliceIdent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

/- **The parametric χ-weighted assembly at the `pairGc21` fibre.**  Same conclusion as
`pairEnergy_pairGc21_le_chi`, but with the window data `Kg`, `Kc` supplied as hypotheses, so that
the constant is the explicit `ℓ ^ 6 * max (2 * Kg + ℓ⁻² * Kc) 2` rather than a `Classical.choose`d
one.  This is the one-line instantiation of
`pairEnergy_le_of_integral_bounds_chi_param` at `P = cA⁴ℓ⁶ pinL2 · memY21` and
`Q = cA⁴ℓ⁶ pinL2 · dirY21`. -/

theorem pgc21_le_param {ℓ Kg Kc : ℝ} (hℓ : 0 < ℓ) (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
      ‖fderiv ℝ (Work.BoseBoxFock.chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.chiS ℓ w‖ ^ 2 ≤ Kc) :
    ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA →
      (∀ u y : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * Work.BoseBoxFock.pinL2 ℓ Θ₀
            * Work.BoseBoxFock.memY21 ℓ p Θ₀ y u) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        DifferentiableAt ℝ (fun u' => Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A u' z.2) z.1) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
        ‖fderiv ℝ (fun u' => Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * Work.BoseBoxFock.pinL2 ℓ Θ₀
            * Work.BoseBoxFock.dirY21 ℓ p Θ₀ z.2 z.1) →
      Continuous (Function.uncurry (Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A)) →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.memY21 ℓ p Θ₀ z.2 z.1) = Work.BoseBoxFock.pinL2 ℓ Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        ‖Work.BoseBoxFock.chiS ℓ z.1‖ ^ 2 * Work.BoseBoxFock.dirY21 ℓ p Θ₀ z.2 z.1)
        ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ →
      Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairGc21 ℓ p hp Θ₀ A)
        ≤ ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * cA ^ 4
            * Work.BoseBoxFock.pinL2 ℓ Θ₀
            * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by
  intro n p hp Θ₀ A cA hΘ₀ hcA hval hder hdb hcont hsliceM hsliceDChi
  obtain ⟨CM, hCM0, hCM⟩ := memY21_le hℓ p hΘ₀.continuous
  obtain ⟨CD, hCD0, hCD⟩ := dirY21_le hℓ p hΘ₀
  have hbox : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinDChi0 : 0 ≤ pinDirChi ℓ Θ₀ := pinDirChi_nonneg ℓ Θ₀
  have hc0 : 0 ≤ cA ^ 4 * ℓ ^ 6 := by positivity
  have hcc : 0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ := mul_nonneg hc0 hpin0
  have hM0 : ∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      0 ≤ memY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => integral_nonneg fun x => by positivity
  have hD0 : ∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      0 ≤ dirY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hMs : StronglyMeasurable (Function.uncurry (memY21 ℓ p Θ₀)) :=
    stronglyMeasurable_memY21 (ℓ := ℓ) p hΘ₀.continuous
  have hDs : StronglyMeasurable (Function.uncurry (dirY21 ℓ p Θ₀)) :=
    stronglyMeasurable_dirY21 (ℓ := ℓ) p hΘ₀
  have hP0 : ∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => mul_nonneg hcc (hM0 z)
  have hQ0 : ∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      0 ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1 :=
    fun z => mul_nonneg hcc (hD0 z)
  have hPint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * CM) ?_ ?_
    · have hswap : Measurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (z.2, z.1)) := Measurable.prod measurable_snd measurable_fst
      exact ((hMs.comp_measurable hswap).const_mul
        (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀)).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 z)]
      exact mul_le_mul_of_nonneg_left (hCM z.2 hz.2 z.1 hz.1) hcc
  have hWQint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ‖chiS ℓ z.1‖ ^ 2 * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1))
      (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound
      (C := Kc * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * CD)) ?_ ?_
    · have hswap : Measurable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (z.2, z.1)) := Measurable.prod measurable_snd measurable_fst
      have h1 : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) ×
            EuclideanSpace ℝ (Fin 3) => ‖chiS ℓ z.1‖ ^ 2 *
            (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)) volume :=
        ((((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).aestronglyMeasurable).mul
          ((hDs.comp_measurable hswap).aestronglyMeasurable.const_mul _)
      exact h1.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hQ0 z))]
      exact mul_le_mul (hKc z.1) (mul_le_mul_of_nonneg_left (hCD z.2 hz.2 z.1 hz.1) hcc)
        (hQ0 z) hKc0
  have hP : (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀ := by
    rw [MeasureTheory.integral_const_mul, hsliceM]
  have hWQ : (∫ z in Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ,
        ‖chiS ℓ z.1‖ ^ 2 * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1))
      ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀ := by
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          ‖chiS ℓ z.1‖ ^ 2 * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1))
        = fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
            (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀) *
              (‖chiS ℓ z.1‖ ^ 2 * dirY21 ℓ p Θ₀ z.2 z.1) := by
      funext z
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hsliceDChi hcc
  have hmain := pairEnergy_le_of_integral_bounds_chi_param (ℓ := ℓ) hℓ hKg0 hKc0 hKg hKc
    (G := pairGc21 ℓ p hp Θ₀ A)
    (P := fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
    (Q := fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)
    (A := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀)
    (B := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
    (mul_nonneg hcc hpin0) (mul_nonneg hcc hpinDChi0) hP0 hQ0
    (fun z => hval z.1 z.2) (fun z => hdb z) hder hcont hPint hWQint hP hWQ
  have hsplit : max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
        * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀
          + cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
      = ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * cA ^ 4 * pinL2 ℓ Θ₀
          * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    ring
  exact hmain.trans_eq hsplit

end Work.BoseBoxFock
