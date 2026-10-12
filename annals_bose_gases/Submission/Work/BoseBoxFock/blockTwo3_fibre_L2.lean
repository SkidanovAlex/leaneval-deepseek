import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotPairRowsAux
import Submission.Work.BoseBoxFock.blockTwo3_bound
import Submission.Work.BoseBoxFock.fibre_kernel_two
import Submission.Work.BoseBoxFock.pinQ_kernel_expansion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

/-- The `Function.update` form of the inserted configuration is the insertion. -/
theorem update_insEq {n : ℕ} {i j : Fin n} (hij : i ≠ j) (w₀ w₁ y u : 𝔼)
    (x' : Fib n i j) :
    Function.update (Function.update (fun k => if h : k = i then w₀
        else if h' : k = j then w₁ else x' ⟨k, h, h'⟩) i y) j u
      = fun k => if h : k = i then y else if h' : k = j then u else x' ⟨k, h, h'⟩ := by
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases h1 : k = i
  · have h2 : ¬ (k = j) := fun hk => hij (h1.symm.trans hk)
    simp only [if_pos h1, if_neg h2, dif_pos h1]
  · by_cases h2 : k = j
    · simp only [if_pos h2, dif_neg h1, dif_pos h2]
    · simp only [if_neg h2, if_neg h1, dif_neg h1, dif_neg h2]

/-- The integrand of the statement is the integrand of the `splitEquiv` form. -/
theorem stepEq {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (Θ : (Fin n → 𝔼) → ℂ) (A B : 𝔼 → ℂ) (w₀ w₁ : 𝔼) :
    (∫ x' : Fib n p.1 p.2, ∫ y : 𝔼, ∫ u : 𝔼,
        ((starRingEnd ℂ) (Θ (fun k => if h : k = p.1 then w₀
              else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩))
          * (starRingEnd ℂ) (A y) * (starRingEnd ℂ) (B u)
          * Θ (Function.update (Function.update
              (fun k => if h : k = p.1 then w₀
                        else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩) p.1 y) p.2 u)))
      = (∫ x' : Fib n p.1 p.2, ∫ y : 𝔼, ∫ u : 𝔼,
          ((starRingEnd ℂ) (Θ (splitEquiv hp (x', (w₀, w₁)))) * (starRingEnd ℂ) (A y))
            * (starRingEnd ℂ) (B u) * Θ (splitEquiv hp (x', (y, u)))) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [update_insEq hp w₀ w₁ y u x', splitEquiv_apply]

theorem blockTwo3_fibre_L2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : MeasureTheory.AEStronglyMeasurable Θ)
    (hΘL : MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2))
    (hAm : MeasureTheory.AEStronglyMeasurable A)
    (hAL : MeasureTheory.Integrable (fun x => ‖A x‖ ^ 2))
    (hBm : MeasureTheory.AEStronglyMeasurable B)
    (hBL : MeasureTheory.Integrable (fun x => ‖B x‖ ^ 2)) :
    ∫ w₀ : EuclideanSpace ℝ (Fin 3), ∫ w₁ : EuclideanSpace ℝ (Fin 3),
      ‖∫ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → EuclideanSpace ℝ (Fin 3),
          ∫ y : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Θ (fun k => if h : k = p.1 then w₀
                                    else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩))
          * (starRingEnd ℂ) (A y) * (starRingEnd ℂ) (B u)
          * Θ (Function.update (Function.update
              (fun k => if h : k = p.1 then w₀
                        else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩) p.1 y) p.2 u)‖ ^ 2
      ≤ (∫ x, ‖A x‖ ^ 2) * (∫ x, ‖B x‖ ^ 2) * (∫ x, ‖Θ x‖ ^ 2) ^ 2 := by
  refine le_of_eq_of_le ?_ (fibre_L2_bound (i := p.1) (j := p.2) hp hΘm hΘL hAm hAL hBm hBL)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w₀ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w₁ => ?_)
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (stepEq p hp Θ A B w₀ w₁)

end Work.BoseBoxFock
