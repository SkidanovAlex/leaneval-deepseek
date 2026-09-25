import Mathlib
import Submission.Work.NN.Core.czB_L2_bounded
import Submission.Work.NN.Core.czB_L2_bounded_C0
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one

open scoped ENNReal
open MeasureTheory

namespace Work.NN.Core

/-- the requested statement, verbatim -/
theorem czB_L2_bounded_continuous {n : ℕ} (hn : 0 < n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Fin n → (Fin n → ℂ) → ℂ), (∀ j, Continuous (ψ j)) → (∀ j, HasCompactSupport (ψ j)) → ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential ψ) → (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z‖ ^ 2) ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖ψ j z‖ ^ 2 := by
  exact Work.NN.Core.czB_L2_bounded_C0 (n := n) hn

/-- sanity check: the smooth (C^1, compactly supported) case follows from `czB_L2_bounded` with `g = 0`. -/
example {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 (f j)) → (∀ j, HasCompactSupport (f j)) →
      (∫⁻ z : Fin n → ℂ, ∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential f) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, ∑ j : Fin n, ENNReal.ofReal ‖f j z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := czB_L2_bounded (n := n) hn
  refine ⟨C, hC, fun f hf hcs => ?_⟩
  have hzero : Work.CR.Flat.Cauchy.bmPotential (fun _ : Fin n => (0 : (Fin n → ℂ) → ℂ)) = 0 := by
    funext z
    simp [Work.CR.Flat.Cauchy.bmPotential]
  have hd : ∀ i, Work.CR.Flat.dCoord i
      (Work.CR.Flat.Cauchy.bmPotential (fun _ : Fin n => (0 : (Fin n → ℂ) → ℂ))) = 0 := by
    intro i
    rw [hzero]
    funext z
    simp [Work.CR.Flat.dCoord]
  have h := hb f (fun _ : Fin n => (0 : (Fin n → ℂ) → ℂ)) hf (fun j => contDiff_const)
    hcs (fun j => HasCompactSupport.zero)
  simpa [hd] using h

end Work.NN.Core
