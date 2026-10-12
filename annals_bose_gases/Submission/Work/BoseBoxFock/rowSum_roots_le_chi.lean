import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairDirChi_slices
import Submission.Work.BoseBoxFock.pairG_dir_leB_chi
import Submission.Work.BoseBoxFock.rowSum_roots_le
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

/-- `pairEnergy_pairGc13_le_chi` with the constant pulled out of the arity. -/
private theorem pgc13_dir_uniform_chi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : E3, ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ z.1 * memY13 ℓ p Θ₀ z.2) →
      Continuous (Function.uncurry (pairGc13 ℓ p hp Θ₀ A B)) →
      (∫ w in boxL ℓ, memX13 ℓ p Θ₀ w) = pinL2 ℓ Θ₀ →
      (∫ y in boxL ℓ, memY13 ℓ p Θ₀ y) = ℓ ^ 3 * pinL2 ℓ Θ₀ →
      (∫ w in boxL ℓ, ‖chiS ℓ w‖ ^ 2 * dirX13 ℓ p Θ₀ w) ≤ pinDirChi ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc13 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Kg, hKg0, hKg⟩ := exists_chiS_grad_bound ℓ hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2,
    mul_nonneg (by positivity) (le_max_of_le_left (add_nonneg (by linarith) (by positivity))), ?_⟩
  intro n p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceX hsliceY hsliceDChi
  obtain ⟨Cx, hCx0, hCx⟩ := memX13_le hℓ p hΘ₀.continuous
  obtain ⟨Cy, hCy0, hCy⟩ := memY13_le hℓ p hΘ₀.continuous
  obtain ⟨Cd, hCd0, hCd⟩ := dirX13_le hℓ p hΘ₀
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hMx0 : ∀ w, 0 ≤ memX13 ℓ p Θ₀ w := fun w => integral_nonneg fun z => by positivity
  have hMy0 : ∀ y, 0 ≤ memY13 ℓ p Θ₀ y := fun y => integral_nonneg fun z => by positivity
  have hDx0 : ∀ w, 0 ≤ dirX13 ℓ p Θ₀ w :=
    fun w => Finset.sum_nonneg fun j _ => integral_nonneg fun z => by positivity
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinD0 : 0 ≤ pinDirChi ℓ Θ₀ := pinDirChi_nonneg ℓ Θ₀
  have hMxs : StronglyMeasurable (memX13 ℓ p Θ₀) :=
    stronglyMeasurable_memX13 (ℓ := ℓ) p hΘ₀.continuous
  have hMys : StronglyMeasurable (memY13 ℓ p Θ₀) :=
    stronglyMeasurable_memY13 (ℓ := ℓ) p hΘ₀.continuous
  have hDxs : StronglyMeasurable (dirX13 ℓ p Θ₀) := stronglyMeasurable_dirX13 (ℓ := ℓ) p hΘ₀
  have hcs0 : 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 :=
    mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)
  have hPhi0 : ∀ w, 0 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w :=
    fun w => mul_nonneg hcs0 (hMx0 w)
  -- the mass bound
  have hmass : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀) := by
    have h1 := setIntegral_prod_le_factor (ℓ := ℓ)
      (f := fun w y => ‖pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2)
      (Φ := fun w => cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w)
      (Ψ := memY13 ℓ p Θ₀)
      (fun w y => by positivity)
      hPhi0 hMy0 (hMxs.const_mul _) hMys
      ⟨cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx, fun w hw =>
        mul_le_mul_of_nonneg_left (hCx w hw) hcs0⟩
      ⟨Cy, fun y hy => hCy y hy⟩
      (fun w y => hval w y)
    rw [MeasureTheory.integral_const_mul] at h1
    rw [hsliceX, hsliceY] at h1
    exact h1
  -- the χ-weighted Dirichlet bound
  have hdirW : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2))
      ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDirChi ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀) := by
    have hPhi : StronglyMeasurable (fun w : E3 =>
        cA ^ 2 * cB ^ 2 * ℓ ^ 3 * (‖chiS ℓ w‖ ^ 2 * dirX13 ℓ p Θ₀ w)) :=
      ((((continuous_chiS ℓ).norm.pow 2).stronglyMeasurable).mul hDxs).const_mul
        (cA ^ 2 * cB ^ 2 * ℓ ^ 3)
    have hpt : ∀ w y : E3, (fun w y => ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) w y
        ≤ (fun w : E3 => cA ^ 2 * cB ^ 2 * ℓ ^ 3 * (‖chiS ℓ w‖ ^ 2 * dirX13 ℓ p Θ₀ w)) w
          * (fun y : E3 => memY13 ℓ p Θ₀ y) y :=
      fun w y => (mul_le_mul_of_nonneg_left (hdb (w, y)) (by positivity)).trans_eq (by ring)
    have h1 := setIntegral_prod_le_factor (ℓ := ℓ)
      (f := fun w y => ‖chiS ℓ w‖ ^ 2 * (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2))
      (Φ := fun w => cA ^ 2 * cB ^ 2 * ℓ ^ 3 * (‖chiS ℓ w‖ ^ 2 * dirX13 ℓ p Θ₀ w))
      (Ψ := memY13 ℓ p Θ₀)
      (fun w y => mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity))
      (fun w => mul_nonneg hcs0 (mul_nonneg (by positivity) (hDx0 w)))
      hMy0 hPhi hMys
      ⟨cA ^ 2 * cB ^ 2 * ℓ ^ 3 * (Kc * Cd), fun w hw =>
        mul_le_mul_of_nonneg_left
          (mul_le_mul (hKc w) (hCd w hw) (hDx0 w) hKc0) hcs0⟩
      ⟨Cy, fun y hy => hCy y hy⟩
      hpt
    rw [MeasureTheory.integral_const_mul] at h1
    refine h1.trans ?_
    rw [hsliceY]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsliceDChi hcs0)
      (mul_nonneg (by positivity) hpin0)
  -- pointwise bounds on the box squared
  have hGbound : ∀ z ∈ boxL ℓ ×ˢ boxL ℓ,
      ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2 ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy := by
    rintro ⟨w, y⟩ hz
    refine (hval w y).trans ?_
    calc cA ^ 2 * cB ^ 2 * ℓ ^ 3 * memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (memX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) := by ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (Cx * Cy) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hCx w hz.1) (hCy y hz.2) (hMy0 y) hCx0) hcs0
      _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy := by ring
  have hDbound : ∀ z ∈ boxL ℓ ×ˢ boxL ℓ, (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy := by
    rintro ⟨w, y⟩ hz
    refine (hdb (w, y)).trans ?_
    calc cA ^ 2 * cB ^ 2 * ℓ ^ 3 * dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (dirX13 ℓ p Θ₀ w * memY13 ℓ p Θ₀ y) := by ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 3) * (Cd * Cy) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hCd w hz.1) (hCy y hz.2) (hMy0 y) hCd0) hcs0
      _ = cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy := by ring
  -- integrability of the mass integrand
  have hGsq_int : IntegrableOn (fun z : E3 × E3 => ‖pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top
      ((aestronglyMeasurable_fibre hcont).mono_measure Measure.restrict_le_self)
      (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hGbound z hz
  -- integrability of the χ-weighted Dirichlet integrand
  have hWQ_int : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top ?_
      (Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy)) ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_
        ((aesm_dirIntegrand hcont).mono_measure Measure.restrict_le_self)
      exact (((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity))]
      exact mul_le_mul (hKc z.1) (hDbound z hz)
        (Finset.sum_nonneg fun j _ => by positivity) hKc0
  -- integrability of the pair-energy integrand
  have hF_int : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * pairGc13 ℓ p hp Θ₀ A B z.1 z.2‖ ^ 2)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine IntegrableOn.of_bound volume_boxL_prod_lt_top
      ((aesm_LHSIntegrand hcont).mono_measure Measure.restrict_le_self)
      ((2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cx * Cy)
        + 2 * Kc * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Cd * Cy)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (LHSIntegrand_le hℓ hKg hKc (fun w y => hder (w, y)) z.1 z.2).trans ?_
    have h3 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc :=
      add_nonneg (by linarith) (by positivity)
    have h4 : 0 ≤ 2 * Kc := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (hGbound z hz) h3)
      (mul_le_mul_of_nonneg_left (hDbound z hz) h4)
  -- the assembly
  have hmain : L1Tails.pairEnergy ℓ (pairGc13 ℓ p hp Θ₀ A B)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
            * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        + 2 * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDirChi ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀)) :=
    pairEnergy_le_of_box_bounds_chi (ℓ := ℓ) hℓ hKg0 hKc0
      (by have := hpin0; positivity)
      (by have := hpinD0; positivity)
      hKg hKc
      hF_int hGsq_int hWQ_int (Eventually.of_forall fun z => hder z) hmass hdirW
  -- the arithmetic
  have h0 : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg cA) (sq_nonneg cB)) (by positivity)) hpin0
  have hkey : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * pinL2 ℓ Θ₀ + 2 * pinDirChi ℓ Θ₀
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (pinL2 ℓ Θ₀ + pinDirChi ℓ Θ₀) := by
    have h1 : 2 * Kg + (ℓ ^ 2)⁻¹ * Kc ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 :=
      le_max_left _ _
    have h2 : (2 : ℝ) ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 := le_max_right _ _
    nlinarith [h1, h2, hpin0, hpinD0]
  have hcalc : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
            * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        + 2 * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDirChi ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀))
      ≤ (ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀
          * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    calc (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinL2 ℓ Θ₀
              * (ℓ ^ 3 * pinL2 ℓ Θ₀))
          + 2 * (cA ^ 2 * cB ^ 2 * ℓ ^ 3 * pinDirChi ℓ Θ₀ * (ℓ ^ 3 * pinL2 ℓ Θ₀))
        = (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀)
            * ((2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * pinL2 ℓ Θ₀ + 2 * pinDirChi ℓ Θ₀) := by ring
      _ ≤ (cA ^ 2 * cB ^ 2 * ℓ ^ 6 * pinL2 ℓ Θ₀)
            * (max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (pinL2 ℓ Θ₀ + pinDirChi ℓ Θ₀)) :=
          mul_le_mul_of_nonneg_left hkey h0
      _ = (ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2) * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀
            * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by ring
  linarith [hmain, hcalc]

/-- `pairEnergy_pairGc23_le_chi` with the constant pulled out of the arity. -/
private theorem pgc23_dir_uniform_chi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : E3, ‖pairGc23 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * memX23 ℓ p Θ₀ w y * pinL2 ℓ Θ₀) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => pairGc23 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 6 * dirX23 ℓ p Θ₀ z.1 z.2 * pinL2 ℓ Θ₀) →
      Continuous (Function.uncurry (pairGc23 ℓ p hp Θ₀ A B)) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, memX23 ℓ p Θ₀ z.1 z.2) = pinL2 ℓ Θ₀ →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * dirX23 ℓ p Θ₀ z.1 z.2) ≤ pinDirChi ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc23 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Cg, hCg0, hCg⟩ := pairEnergy_le_of_integral_bounds_chi (ℓ := ℓ) hℓ
  refine ⟨Cg * ℓ ^ 6, by positivity, ?_⟩
  intro n p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceM hsliceD
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

/-- `pairEnergy_pairGc21_le_chi` with the constant pulled out of the arity. -/
private theorem pgc21_dir_uniform_chi {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA →
      (∀ u y : E3, ‖pairGc21 ℓ p hp Θ₀ A u y‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ y u) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun u' => pairGc21 ℓ p hp Θ₀ A u' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1) →
      Continuous (Function.uncurry (pairGc21 ℓ p hp Θ₀ A)) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, memY21 ℓ p Θ₀ z.2 z.1) = pinL2 ℓ Θ₀ →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * dirY21 ℓ p Θ₀ z.2 z.1) ≤ pinDirChi ℓ Θ₀ →
      L1Tails.pairEnergy ℓ (pairGc21 ℓ p hp Θ₀ A)
        ≤ C * cA ^ 4 * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
  obtain ⟨Cg, hCg0, hCg⟩ := pairEnergy_le_of_integral_bounds_chi (ℓ := ℓ) hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨Cg * ℓ ^ 6, by positivity, ?_⟩
  intro n p hp Θ₀ A cA hΘ₀ hcA hval hder hdb hcont hsliceM hsliceDChi
  obtain ⟨CM, hCM0, hCM⟩ := memY21_le hℓ p hΘ₀.continuous
  obtain ⟨CD, hCD0, hCD⟩ := dirY21_le hℓ p hΘ₀
  have hbox : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hpin0 : 0 ≤ pinL2 ℓ Θ₀ := integral_nonneg fun z => by positivity
  have hpinDChi0 : 0 ≤ pinDirChi ℓ Θ₀ := pinDirChi_nonneg ℓ Θ₀
  have hc0 : 0 ≤ cA ^ 4 * ℓ ^ 6 := mul_nonneg (by positivity) (by positivity)
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
  have hC := hCg (G := pairGc21 ℓ p hp Θ₀ A)
    (P := fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * memY21 ℓ p Θ₀ z.2 z.1)
    (Q := fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * dirY21 ℓ p Θ₀ z.2 z.1)
    (A := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀)
    (B := cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
    (mul_nonneg hcc hpin0) (mul_nonneg hcc hpinDChi0) hP0 hQ0
    (fun z => hval z.1 z.2) (fun z => hdb z) hder hcont hPint hWQint hP hWQ
  have h1 : Cg * (cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinL2 ℓ Θ₀
        + cA ^ 4 * ℓ ^ 6 * pinL2 ℓ Θ₀ * pinDirChi ℓ Θ₀)
      = (Cg * ℓ ^ 6) * cA ^ 4 * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
    ring
  linarith [hC, h1.le]

/-- The χ-weighted uniform fibre bound for the honest fibre `pairG13`. -/
private theorem pairG13_dir_uniform_chi {l : ℝ} (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A → Measurable B →
        (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
        L1Tails.pairEnergy l (pairG13 p Θ A B)
          ≤ K * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
  obtain ⟨K, hK0, hK⟩ := pgc13_dir_uniform_chi (ℓ := l) hl
  refine ⟨K, hK0, ?_⟩
  intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
  obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
    pairGc13_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
  rw [pairEnergy_congr_box hl hEq]
  exact hK p hp hΘ₀ hcA hcB hval hder hdb hcont (setIntegral_memX13 hl p hΘ₀)
    (setIntegral_memY13 hl p hp hΘ₀) (pairGchi_slice13 (pairDirChi_dirX13 hl p hΘ₀))

/-- The χ-weighted uniform fibre bound for the honest fibre `pairG23`. -/
private theorem pairG23_dir_uniform_chi {l : ℝ} (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A → Measurable B →
        (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
        L1Tails.pairEnergy l (pairG23 p Θ A B)
          ≤ K * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
  obtain ⟨K, hK0, hK⟩ := pgc23_dir_uniform_chi (ℓ := l) hl
  refine ⟨K, hK0, ?_⟩
  intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
  obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
    pairGc23_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
  rw [pairEnergy_congr_box hl hEq]
  exact hK p hp hΘ₀ hcA hcB hval hder hdb hcont (setIntegral_memX23 hl p hp hΘ₀)
    (pairGchi_slice2 (D := fun z => dirX23 l p Θ₀ z.1 z.2) (pairDirChi_dirX23 hl p hp hΘ₀))

/-- The χ-weighted uniform fibre bound for the honest fibre `pairG21`. -/
private theorem pairG21_dir_uniform_chi {l : ℝ} (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A →
        (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
        L1Tails.pairEnergy l (pairG21 p Θ A)
          ≤ K * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
  obtain ⟨K, hK0, hK⟩ := pgc21_dir_uniform_chi (ℓ := l) hl
  refine ⟨K, hK0, ?_⟩
  intro n p hp Θ Θ₀ A cA hΘ₀ hΘ hA hAb hcA
  obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
    pairGc21_core (ℓ := l) hl p hp hΘ₀ hΘ hA hAb hcA
  rw [pairEnergy_congr_box hl hEq]
  exact hK p hp hΘ₀ hcA hval hder hdb hcont (setIntegral_memY21 hl p hp hΘ₀)
    (pairGchi_slice2 (D := fun z => dirY21 l p Θ₀ z.2 z.1) (pairDirChi_dirY21 hl p hp hΘ₀))

private theorem rowDirUniformChi {l : ℝ} (hl : 0 < l) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A → Measurable B →
        (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
        L1Tails.pairEnergy l (pairG13 p Θ A B)
          ≤ K * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) ∧
      (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A → Measurable B →
        (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
        L1Tails.pairEnergy l (pairG23 p Θ A B)
          ≤ K * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) ∧
      (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ},
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A →
        (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
        L1Tails.pairEnergy l (pairG21 p Θ A)
          ≤ K * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) := by
  obtain ⟨K13, hK13, h13⟩ := pairG13_dir_uniform_chi hl
  obtain ⟨K23, hK23, h23⟩ := pairG23_dir_uniform_chi hl
  obtain ⟨K21, hK21, h21⟩ := pairG21_dir_uniform_chi hl
  refine ⟨max K13 (max K23 K21), le_trans hK13 (le_max_left _ _), ?_, ?_, ?_⟩
  · intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hpL : (0 : ℝ) ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpD : (0 : ℝ) ≤ pinDirChi l Θ₀ := integral_nonneg fun x => by positivity
    have hZ : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
      positivity
    calc L1Tails.pairEnergy l (pairG13 p Θ A B)
        ≤ K13 * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) :=
          h13 p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
      _ = K13 * (cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) := by ring
      _ ≤ max K13 (max K23 K21)
            * (cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hZ
      _ = max K13 (max K23 K21) * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀
            * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by ring
  · intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hpL : (0 : ℝ) ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpD : (0 : ℝ) ≤ pinDirChi l Θ₀ := integral_nonneg fun x => by positivity
    have hZ : (0 : ℝ) ≤ cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
      positivity
    calc L1Tails.pairEnergy l (pairG23 p Θ A B)
        ≤ K23 * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) :=
          h23 p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
      _ = K23 * (cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) := by ring
      _ ≤ max K13 (max K23 K21)
            * (cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_left K23 K21) (le_max_right K13 _)) hZ
      _ = max K13 (max K23 K21) * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀
            * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by ring
  · intro n p hp Θ Θ₀ A cA hΘ₀ hΘ hA hAb hcA
    have hpL : (0 : ℝ) ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpD : (0 : ℝ) ≤ pinDirChi l Θ₀ := integral_nonneg fun x => by positivity
    have hZ : (0 : ℝ) ≤ cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by positivity
    calc L1Tails.pairEnergy l (pairG21 p Θ A)
        ≤ K21 * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) :=
          h21 p hp hΘ₀ hΘ hA hAb hcA
      _ = K21 * (cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) := by ring
      _ ≤ max K13 (max K23 K21) * (cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) :=
          mul_le_mul_of_nonneg_right
            (le_trans (le_max_right K23 K21) (le_max_right K13 (max K23 K21))) hZ
      _ = max K13 (max K23 K21) * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by ring

/-! ## 4.  The constant as a function of `ℓ` -/

/-- The uniform fibre constant of `ℓ`, for `ℓ ≤ 0` set to `0` (only `ℓ > 0` is ever used). -/
private noncomputable def rowDirConstantChi (l : ℝ) : ℝ :=
  if h : 0 < l then Classical.choose (rowDirUniformChi h) else 0

private theorem rowDirConstantChi_nonneg (l : ℝ) : 0 ≤ rowDirConstantChi l := by
  unfold rowDirConstantChi
  split
  · exact (Classical.choose_spec (rowDirUniformChi ‹0 < l›)).1
  · exact le_refl 0

/-- The three uniform fibre bounds at the chosen constant. -/
private theorem rowDirConstantChi_spec {l : ℝ} (hl : 0 < l) :
    (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
      {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      L1Tails.pairEnergy l (pairG13 p Θ A B)
        ≤ rowDirConstantChi l * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) ∧
    (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
      {Θ Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      L1Tails.pairEnergy l (pairG23 p Θ A B)
        ≤ rowDirConstantChi l * cA ^ 2 * cB ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) ∧
    (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
      {Θ Θ₀ : Xn n → ℂ} {A : E3 → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A →
      (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
      L1Tails.pairEnergy l (pairG21 p Θ A)
        ≤ rowDirConstantChi l * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)) := by
  rw [rowDirConstantChi, dif_pos hl]
  exact (Classical.choose_spec (rowDirUniformChi hl)).2

/-- The row constant `Cf ℓ = 3·(√K(ℓ) + 1)`: three fibres per pair, and one unit of slack for the
mass budget. -/
private noncomputable def rowCfChi (l : ℝ) : ℝ := 3 * (Real.sqrt (rowDirConstantChi l) + 1)

private theorem rowCfChi_nonneg (l : ℝ) : 0 ≤ rowCfChi l := by
  rw [rowCfChi]; positivity

/-! ## 5.  The row sum -/

/-- Square root of the Dirichlet bound: the bound of `pairG13_dir_uniform_chi` is
`C·cA²cA²·pL·(pD + pL)`, whose square root is `√C·(cA²·(√pL·√(pD + pL)))`. -/
private lemma rs_sqrt_pairEnergy_le_chi {l : ℝ} {G : E3 → E3 → ℂ} {C cA pL pD : ℝ}
    (hC : 0 ≤ C) (hpL : 0 ≤ pL) (hpD : 0 ≤ pD)
    (h : L1Tails.pairEnergy l G ≤ C * cA ^ 2 * cA ^ 2 * pL * (pD + pL)) :
    Real.sqrt (L1Tails.pairEnergy l G)
      ≤ Real.sqrt C * (cA ^ 2 * (Real.sqrt pL * Real.sqrt (pD + pL))) := by
  have hpDpL : 0 ≤ pD + pL := by linarith
  set sc := Real.sqrt C * (cA ^ 2 * (Real.sqrt pL * Real.sqrt (pD + pL))) with hsc
  have hsc0 : 0 ≤ sc := by rw [hsc]; positivity
  have hsq : sc ^ 2 = C * cA ^ 2 * cA ^ 2 * pL * (pD + pL) := by
    rw [hsc, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hpL, Real.sq_sqrt hpDpL]
    ring
  rw [Real.sqrt_le_left hsc0, hsq]
  exact h

/-- Square root of the mass bound: the fibre `L²` bounds are perfect squares. -/
private lemma rs_sqrt_massBox_le_chi {l : ℝ} {G : E3 → E3 → ℂ} {A2 L2 : ℝ}
    (hA2 : 0 ≤ A2) (hL2 : 0 ≤ L2) (h : massBox l G ≤ A2 * A2 * L2 ^ 2) :
    Real.sqrt (massBox l G) ≤ A2 * L2 := by
  have h0 : 0 ≤ A2 * L2 := mul_nonneg hA2 hL2
  have hsq : (A2 * L2) ^ 2 = A2 * A2 * L2 ^ 2 := by ring
  rw [Real.sqrt_le_left h0, hsq]
  exact h

theorem rowSum_roots_le_chi :
    ∃ Cf : ℝ → ℝ, (∀ l, 0 ≤ Cf l) ∧
      ∀ {n : ℕ} {l : ℝ}, 0 < l →
        ∀ {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ},
        Measurable Θ → (∃ K : ℝ, ∀ x, ‖Θ x‖ ≤ K) →
        Function.support Θ ⊆ Work.MB.boxPow n l →
        MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ x‖ ^ 2) →
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
        Measurable A → (∃ K : ℝ, ∀ x, ‖A x‖ ≤ K) →
        MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖A x‖ ^ 2) →
        0 ≤ cA → (∀ x, ‖A x‖ ≤ cA) →
        ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG13 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG13 p Θ A A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG21 p Θ A)))
            + (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A A))
              + Real.sqrt (Work.BoseBoxFock.massBox l (Work.BoseBoxFock.pairG23 p Θ A A))))
          ≤ Cf l * (n : ℝ) * (n : ℝ)
              * (cA ^ 2 * (Real.sqrt (Work.BoseBoxFock.pinL2 l Θ₀)
                    * Real.sqrt (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
                + (∫ x : EuclideanSpace ℝ (Fin 3), ‖A x‖ ^ 2)
                  * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2)) := by
  classical
  refine ⟨rowCfChi, fun l => rowCfChi_nonneg l, ?_⟩
  intro n l hl Θ Θ₀ A cA hΘm hΘb hΘs hΘL hΘ₀ hΘind hAm hAb hAL hcA hAc
  obtain ⟨h13, h23, h21⟩ := rowDirConstantChi_spec hl
  have hΘm' : MeasureTheory.AEStronglyMeasurable Θ := hΘm.aestronglyMeasurable
  have hAm' : MeasureTheory.AEStronglyMeasurable A := hAm.aestronglyMeasurable
  have hpL2 : 0 ≤ Work.BoseBoxFock.pinL2 l Θ₀ := integral_nonneg fun x => by positivity
  have hpD2 : 0 ≤ Work.BoseBoxFock.pinDirChi l Θ₀ := pinDirChi_nonneg l Θ₀
  have hA2 : 0 ≤ ∫ x : E3, ‖A x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hL2 : 0 ≤ ∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2 := integral_nonneg fun x => by positivity
  set X := cA ^ 2 * (Real.sqrt (Work.BoseBoxFock.pinL2 l Θ₀)
    * Real.sqrt (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀)) with hX
  set Y := (∫ x : E3, ‖A x‖ ^ 2) * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) with hY
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hbudget : 3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y ≤ rowCfChi l * (X + Y) := by
    rw [rowCfChi]
    nlinarith [hX0, hY0, Real.sqrt_nonneg (rowDirConstantChi l)]
  have key : ∀ p ∈ Submission.BoseGases.pairSet n,
      ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
          + Real.sqrt (massBox l (pairG13 p Θ A A)))
        + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
          + Real.sqrt (massBox l (pairG21 p Θ A)))
        + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
          + Real.sqrt (massBox l (pairG23 p Θ A A))))
      ≤ 3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    obtain ⟨hsup13, hsup23, hsup21⟩ := pairG_supports p hpne hΘs
    have hPE13 : L1Tails.pairEnergy l (pairG13 p Θ A A)
        ≤ rowDirConstantChi l * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) :=
      h13 p hpne hΘ₀ hΘind hAm hAm hAc hAc hcA hcA
    have hPE23 : L1Tails.pairEnergy l (pairG23 p Θ A A)
        ≤ rowDirConstantChi l * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) :=
      h23 p hpne hΘ₀ hΘind hAm hAm hAc hAc hcA hcA
    have hPE21 : L1Tails.pairEnergy l (pairG21 p Θ A)
        ≤ rowDirConstantChi l * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
      have h := h21 p hpne hΘ₀ hΘind hAm hAc hcA
      have he : rowDirConstantChi l * cA ^ 4 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀)
          = rowDirConstantChi l * cA ^ 2 * cA ^ 2 * pinL2 l Θ₀ * (pinDirChi l Θ₀ + pinL2 l Θ₀) := by
        ring
      rwa [he] at h
    have hM13 : massBox l (pairG13 p Θ A A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG13_L2 p hpne hsup13 hΘm' hΘL hAm' hAL hAm' hAL
      simpa only [massBox] using h
    have hM23 : massBox l (pairG23 p Θ A A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG23_L2 p hpne hsup23 hΘm' hΘL hAm' hAL hAm' hAL
      simpa only [massBox] using h
    have hM21 : massBox l (pairG21 p Θ A)
        ≤ ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
            * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) ^ 2 := by
      have h := pairG21_L2 p hpne hsup21 hΘm' hΘL hAm' hAL
      have he : (∫ x : E3, ‖A x‖ ^ 2) ^ 2 * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) ^ 2
          = ((∫ x : E3, ‖A x‖ ^ 2) * (∫ x : E3, ‖A x‖ ^ 2))
              * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2) ^ 2 := by ring
      rw [he] at h
      simpa only [massBox] using h
    have hs13 : Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
        ≤ Real.sqrt (rowDirConstantChi l) * X := by
      simpa only [hX] using rs_sqrt_pairEnergy_le_chi (rowDirConstantChi_nonneg l) hpL2 hpD2 hPE13
    have hs23 : Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
        ≤ Real.sqrt (rowDirConstantChi l) * X := by
      simpa only [hX] using rs_sqrt_pairEnergy_le_chi (rowDirConstantChi_nonneg l) hpL2 hpD2 hPE23
    have hs21 : Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
        ≤ Real.sqrt (rowDirConstantChi l) * X := by
      simpa only [hX] using rs_sqrt_pairEnergy_le_chi (rowDirConstantChi_nonneg l) hpL2 hpD2 hPE21
    have hm13 : Real.sqrt (massBox l (pairG13 p Θ A A)) ≤ Y := by
      simpa only [hY] using rs_sqrt_massBox_le_chi hA2 hL2 hM13
    have hm23 : Real.sqrt (massBox l (pairG23 p Θ A A)) ≤ Y := by
      simpa only [hY] using rs_sqrt_massBox_le_chi hA2 hL2 hM23
    have hm21 : Real.sqrt (massBox l (pairG21 p Θ A)) ≤ Y := by
      simpa only [hY] using rs_sqrt_massBox_le_chi hA2 hL2 hM21
    linarith [hs13, hs23, hs21, hm13, hm23, hm21]
  have hsum_le :
      ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
              + Real.sqrt (massBox l (pairG13 p Θ A A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
              + Real.sqrt (massBox l (pairG21 p Θ A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
              + Real.sqrt (massBox l (pairG23 p Θ A A))))
        ≤ ∑ _p ∈ Submission.BoseGases.pairSet n,
            (3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y) :=
    Finset.sum_le_sum key
  have hsum_const : ∑ _p ∈ Submission.BoseGases.pairSet n,
      (3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y)
      = ((Submission.BoseGases.pairSet n).card : ℝ)
        * (3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hterm0 : 0 ≤ 3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y := by positivity
  have hcard : ((Submission.BoseGases.pairSet n).card : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have h : (Submission.BoseGases.pairSet n).card ≤ n * n := by
      calc (Submission.BoseGases.pairSet n).card
          ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_le_univ _
        _ = n * n := by simp [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast h
  calc ∑ p ∈ Submission.BoseGases.pairSet n,
          ((Real.sqrt (L1Tails.pairEnergy l (pairG13 p Θ A A))
              + Real.sqrt (massBox l (pairG13 p Θ A A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG21 p Θ A))
              + Real.sqrt (massBox l (pairG21 p Θ A)))
            + (Real.sqrt (L1Tails.pairEnergy l (pairG23 p Θ A A))
              + Real.sqrt (massBox l (pairG23 p Θ A A))))
      ≤ ((Submission.BoseGases.pairSet n).card : ℝ)
          * (3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y) := by
        rw [hsum_const] at hsum_le
        exact hsum_le
    _ ≤ ((n : ℝ) * (n : ℝ)) * (3 * (Real.sqrt (rowDirConstantChi l) * X) + 3 * Y) :=
        mul_le_mul_of_nonneg_right hcard hterm0
    _ ≤ ((n : ℝ) * (n : ℝ)) * (rowCfChi l * (X + Y)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = rowCfChi l * (n : ℝ) * (n : ℝ) * (X + Y) := by ring



end Work.BoseBoxFock
