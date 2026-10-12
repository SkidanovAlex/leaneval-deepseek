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

/-!
# `Work.BoseBoxFock.pairEnergy_pairGc13_le_chi` — the χ-weighted `pairGc13` fibre estimate

`FINDING_pairG_dir_leB_chi.md` records the plan: the pair energy of the row's fibres is `χ_ℓ`-weighted
in its first variable, so the correct state content is `pinDirChi` (the `χ_ℓ`-weighted Dirichlet
content of `pairRowDirChi`) rather than the unweighted `pinDir`.  This file is the `pairGc13` twin of
`pairEnergy_pairGc13_le` (`pairGFibre.lean`): the *same* proof, with

* the slice hypothesis `∫ dirX13 ≤ pinDir` replaced by `∫ ‖χ_ℓ‖²·dirX13 ≤ pinDirChi`;
* the assembly `pairEnergy_le_of_box_bounds` replaced by the χ-weighted
  `pairEnergy_le_of_box_bounds_chi` (`pairGChiAux`), whose Dirichlet budget carries the weight
  `‖χ_ℓ(w)‖²` and the constant `2` (instead of `2Kc`);
* hence the constant `max (2Kg + ℓ⁻²Kc) 2` in place of `max (2Kg + ℓ⁻²Kc) (2Kc)`.

The file is complete: the target's body is a real proof.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

theorem pairEnergy_pairGc13_le_chi {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
      ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ → 0 ≤ cA → 0 ≤ cB →
      (∀ w y : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B w y‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Work.BoseBoxFock.memX13 ℓ p Θ₀ w * Work.BoseBoxFock.memY13 ℓ p Θ₀ y) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ (fun w' => Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1) →
      (∀ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ cA ^ 2 * cB ^ 2 * ℓ ^ 3 * Work.BoseBoxFock.dirX13 ℓ p Θ₀ z.1 * Work.BoseBoxFock.memY13 ℓ p Θ₀ z.2) →
      Continuous (Function.uncurry (Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B)) →
      (∫ w in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.memX13 ℓ p Θ₀ w) = Work.BoseBoxFock.pinL2 ℓ Θ₀ →
      (∫ y in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.memY13 ℓ p Θ₀ y) = ℓ ^ 3 * Work.BoseBoxFock.pinL2 ℓ Θ₀ →
      (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖Work.BoseBoxFock.chiS ℓ w‖ ^ 2 * Work.BoseBoxFock.dirX13 ℓ p Θ₀ w) ≤ Work.BoseBoxFock.pinDirChi ℓ Θ₀ →
      Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 ℓ Θ₀ * (Work.BoseBoxFock.pinDirChi ℓ Θ₀ + Work.BoseBoxFock.pinL2 ℓ Θ₀) := by
  obtain ⟨Kg, hKg0, hKg⟩ := exists_chiS_grad_bound ℓ hℓ
  obtain ⟨Kc, hKc0, hKc⟩ := exists_chiS_bound ℓ hℓ
  refine ⟨ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2,
    mul_nonneg (by positivity) (le_max_of_le_left (add_nonneg (by linarith) (by positivity))), ?_⟩
  intro p hp Θ₀ A B cA cB hΘ₀ hcA hcB hval hder hdb hcont hsliceX hsliceY hsliceDChi
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

end Work.BoseBoxFock
