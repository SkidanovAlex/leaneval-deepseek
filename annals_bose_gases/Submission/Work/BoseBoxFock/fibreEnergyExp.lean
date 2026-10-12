import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pgc21_le_param
import Submission.Work.BoseBoxFock.pgc23_le_param
import Submission.Work.BoseBoxFock.rowSum_roots_le_chi
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

/-- **The `pairG13` χ-weighted fibre assembly with the window data as hypotheses.**

This is `Work.BoseBoxFock.pairEnergy_pairGc13_le_chi` with the constant made explicit: the
`Classical.choose`d window bounds `Kg ⊇ Σ_j‖∂_jχ_ℓ‖²` and `Kc ⊇ ‖χ_ℓ‖²` are replaced by the two
hypotheses, so the constant `ℓ^6 · max (2·Kg + ℓ⁻²·Kc) 2` is *uniform* in the box side `ℓ`
(no `Classical.choose` after `ℓ` is fixed).

The body is the body of the (private) `rowSum_roots_le_chi.pgc13_dir_uniform_chi` verbatim, with
the two `obtain`ed bounds supplied by the caller. -/
private theorem pgc13LeParam {ℓ Kg Kc : ℝ} (hℓ : 0 < ℓ) (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc) :
    ∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2),
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
        ≤ ℓ ^ 6 * max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * cA ^ 2 * cB ^ 2
            * pinL2 ℓ Θ₀ * (pinDirChi ℓ Θ₀ + pinL2 ℓ Θ₀) := by
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


/-- Fibre Dirichlet-energy bounds with the window data `Kg`, `Kc` supplied as *hypotheses*
(instead of the per-`ℓ` `Classical.choose`d constants of `exists_chiS_bound` /
`exists_chiS_grad_bound`), so that the bound is *uniform* in the box side `l`.

Proof recipe (all ingredients already proved in the workspace):
* `pairEnergy_le_of_box_bounds_chi` (`pairGChiAux.lean`) takes `Kg`, `Kc` as parameters and gives
  `pairEnergy l G ≤ (2*Kg + (l^2)⁻¹*Kc) * A + 2 * B` from pointwise bounds `‖G‖² ≤ P`,
  `Σ_j‖∂_jG‖² ≤ Q` and the integral bounds `∫∫P ≤ A`, `∫∫ χ² Q ≤ B`;
* the pointwise bounds are `pairGc13_core` / `pairGc23_core` / `pairGc21_core` (via
  `pairEnergy_congr_box` from the honest indicator fibre to the clean representative);
* `∫∫P ≤ cA²cB²ℓ⁶ pinL2²` and `∫∫χ²Q ≤ cA²cB²ℓ⁶ pinL2·pinDirChi` follow from the slice identities
  `setIntegral_memX13/memY13/memX23/memY21` and the χ²-weighted Dirichlet slice bounds of
  `pairDirChi_slices.lean` (the `pinDirChi`-form), together with `χS_sq`; for the `pairG21` branch
  replace `cA²cB²` by `cA⁴`.
* the passage to the constant `l^6 * max (2*Kg + (l^2)⁻¹*Kc) 2` is the final `nlinarith`/`ring` of
  `pgc13_dir_uniform_chi` (`rowSum_roots_le_chi.lean`), where both `2*Kg + l⁻²*Kc ≤ max … 2` and
  `2 ≤ max … 2`.

WARNING (important): do NOT use `exists_chiS_bound` / `exists_chiS_grad_bound`, nor
`pairEnergy_le_of_integral_bounds_chi` — their constants are produced by `Classical.choose` *after*
`l` and are therefore unusable for a bound uniform in `l`.  Also do not replace `pinDirChi` by
`pinDir` (the χ² weight is essential). -/
theorem fibreEnergyExp {l Kg Kc : ℝ} (hl : 0 < l) (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
      ‖fderiv ℝ (Work.BoseBoxFock.chiS l) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.chiS l w‖ ^ 2 ≤ Kc) :
    (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG13 p Θ A B)
        ≤ l ^ 6 * max (2 * Kg + (l ^ 2)⁻¹ * Kc) 2 * cA ^ 2 * cB ^ 2
            * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧ (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A B)
        ≤ l ^ 6 * max (2 * Kg + (l ^ 2)⁻¹ * Kc) 2 * cA ^ 2 * cB ^ 2
            * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧ (∀ {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
        {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A →
      (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A)
        ≤ l ^ 6 * max (2 * Kg + (l ^ 2)⁻¹ * Kc) 2 * cA ^ 4
            * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc13_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    rw [pairEnergy_congr_box hl hEq]
    exact pgc13LeParam hl hKg0 hKc0 hKg hKc p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX13 hl p hΘ₀) (setIntegral_memY13 hl p hp hΘ₀)
      (pairGchi_slice13 (pairDirChi_dirX13 hl p hΘ₀))
  · intro n p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc23_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    rw [pairEnergy_congr_box hl hEq]
    exact pgc23_le_param hl hKg0 hKc0 hKg hKc p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX23 hl p hp hΘ₀)
      (pairGchi_slice2 (D := fun z => dirX23 l p Θ₀ z.1 z.2) (pairDirChi_dirX23 hl p hp hΘ₀))
  · intro n p hp Θ Θ₀ A cA hΘ₀ hΘ hA hAb hcA
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc21_core (ℓ := l) hl p hp hΘ₀ hΘ hA hAb hcA
    rw [pairEnergy_congr_box hl hEq]
    exact pgc21_le_param hl hKg0 hKc0 hKg hKc p hp hΘ₀ hcA hval hder hdb hcont
      (setIntegral_memY21 hl p hp hΘ₀)
      (pairGchi_slice2 (D := fun z => dirY21 l p Θ₀ z.2 z.1) (pairDirChi_dirY21 hl p hp hΘ₀))

end Work.BoseBoxFock
