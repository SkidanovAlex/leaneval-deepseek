import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
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
# `Work.BoseBoxFock.integralBoundsChiParam` — the χ-weighted assembly with the window data as
# *hypotheses*

`pairGChiAux.pairEnergy_le_of_integral_bounds_chi` produces its constant by `Classical.choose` from
`exists_chiS_grad_bound` / `exists_chiS_bound` **after** the box side `ℓ` is fixed; such a constant
is unusable for a bound that must be uniform in `ℓ`.  This module is the same statement with the
window data

    `hKg : ∀ w, Σ_j ‖∂_j χ_ℓ(w)‖² ≤ Kg`,   `hKc : ∀ w, ‖χ_ℓ(w)‖² ≤ Kc`

supplied as hypotheses, so the constant is the *explicit*

    `max (2·Kg + ℓ⁻²·Kc) 2`.

The proof is the proof of `pairEnergy_le_of_integral_bounds_chi` verbatim, with the two
`Classical.choose`d bounds replaced by `Kg`, `Kc` and the final `nlinarith` unchanged (the `max`
term is the same term, only now it is `max` of the *given* data).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **Generic χ-weighted assembly with window data as hypotheses.**  If the fibre `G` is pointwise
dominated by `P` in mass and by `Q` in its Dirichlet sum, the *χ-weighted* integral of `Q` is at
most `B`, the integral of `P` is at most `A`, and the window data is bounded by `Kg`, `Kc`, then

    pairEnergy ℓ G ≤ max (2·Kg + ℓ⁻²·Kc) 2 · (A + B) . -/
theorem pairEnergy_le_of_integral_bounds_chi_param {ℓ Kg Kc : ℝ} (hℓ : 0 < ℓ)
    (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : E3,
      ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc) :
    ∀ {G : E3 → E3 → ℂ} {P Q : E3 × E3 → ℝ} {A B : ℝ},
      0 ≤ A → 0 ≤ B → (∀ z, 0 ≤ P z) → (∀ z, 0 ≤ Q z) →
      (∀ z : E3 × E3, ‖G z.1 z.2‖ ^ 2 ≤ P z) →
      (∀ z : E3 × E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Q z) →
      (∀ z : E3 × E3, DifferentiableAt ℝ (fun w' => G w' z.2) z.1) →
      Continuous (Function.uncurry G) →
      IntegrableOn P (boxL ℓ ×ˢ boxL ℓ) →
      IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * Q z) (boxL ℓ ×ˢ boxL ℓ) →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, P z) ≤ A →
      (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z) ≤ B →
      L1Tails.pairEnergy ℓ G ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 * (A + B) := by
  intro G P Q A B hA0 hB0 hP0 hQ0 hval hdb hder hcont hPint hWQint hP hQ
  have hc1 : 0 ≤ 2 * Kg + (ℓ ^ 2)⁻¹ * Kc := add_nonneg (by linarith) (by positivity)
  have hFpt : ∀ z : E3 × E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z + 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) := by
    intro z
    have h1 := LHSIntegrand_le_chi hℓ hKg hKc (hder z)
    have h2 : 2 * ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) := by
      ring
    have h3 : 2 * (‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => G w' z.2) z.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2))
        ≤ 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdb z) (by positivity)) (by norm_num)
    have h4 : (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * ‖G z.1 z.2‖ ^ 2
        ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z := mul_le_mul_of_nonneg_left (hval z) hc1
    linarith [h1, h3, h4]
  have hWQ0 : ∀ z : E3 × E3, 0 ≤ ‖chiS ℓ z.1‖ ^ 2 * Q z :=
    fun z => mul_nonneg (by positivity) (hQ0 z)
  have hSint : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hWQint ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact (((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).aestronglyMeasurable
      · exact (aesm_dirIntegrand hcont).mono_measure Measure.restrict_le_self
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => by positivity))]
      exact mul_le_mul_of_nonneg_left (hdb z) (by positivity)
  have hFpt' : ∀ z : E3 × E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2)
      ≤ (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) * P z + 2 * (‖chiS ℓ z.1‖ ^ 2 * Q z) := hFpt
  have hFint : IntegrableOn (fun z : E3 × E3 => ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => chiS ℓ w' * G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          + (ℓ ^ 2)⁻¹ * ‖chiS ℓ z.1 * G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono'
      ((hPint.const_mul (2 * Kg + (ℓ ^ 2)⁻¹ * Kc)).add (hWQint.const_mul 2))
      ((aesm_LHSIntegrand hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hFpt' z
  have hGsqint : IntegrableOn (fun z : E3 × E3 => ‖G z.1 z.2‖ ^ 2) (boxL ℓ ×ˢ boxL ℓ) := by
    refine Integrable.mono' hPint
      ((aestronglyMeasurable_fibre hcont).mono_measure Measure.restrict_le_self) ?_
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hval z
  have hmass : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖G z.1 z.2‖ ^ 2) ≤ A :=
    (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hPint
      (Eventually.of_forall fun z => hval z)).trans hP
  have hdirW : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * (∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)) ≤ B :=
    (integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => by positivity)) hWQint
      (Eventually.of_forall fun z =>
        mul_le_mul_of_nonneg_left (hdb z) (by positivity))).trans hQ
  have hmain := pairEnergy_le_of_box_bounds_chi (ℓ := ℓ) hℓ hKg0 hKc0 hA0 hB0 hKg hKc
    hFint hGsqint hSint (Eventually.of_forall fun z => hder z) hmass hdirW
  nlinarith [hmain, hA0, hB0, le_max_left (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2,
    le_max_right (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2]

end Work.BoseBoxFock
