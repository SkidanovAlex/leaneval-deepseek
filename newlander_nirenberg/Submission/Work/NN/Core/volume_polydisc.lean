import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core

/-- **Volume of a polydisc.** `volume` on `ℂⁿ` is the product of the (two dimensional) Lebesgue
measures (`MeasureTheory.volume_pi`), a polydisc is a product of discs, and the volume of a disc of
radius `ρ j` is `π ρ j²` (`Complex.volume_ball`). The radius is written `ENNReal.ofReal (ρ j) ^ 2`
(not `ofReal ((ρ j)^2)`) so that the identity stays correct for `ρ j ≤ 0`, where the disc is empty. -/
theorem volume_polydisc {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) :
    MeasureTheory.volume (Work.CR.Flat.polydisc c ρ)
      = ∏ j, ENNReal.ofReal (ρ j) ^ 2 * ENNReal.ofReal Real.pi := by
  -- The polydisc is the product of the open discs (of radius `ρ j`) around the `j`-th centre.
  have h : Work.CR.Flat.polydisc c ρ = Set.univ.pi (fun j => Metric.ball (c j) (ρ j)) := by
    ext z
    simp [Work.CR.Flat.polydisc, Metric.mem_ball, dist_eq_norm]
  rw [h, MeasureTheory.volume_pi_pi]
  -- Each factor is the (two dimensional) volume of a disc in `ℂ`, namely `ofReal (ρ j) ^ 2 * π`.
  simp only [Complex.volume_ball]
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

end Work.NN.Core
