import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.LatFourierDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem latPartial_eq_latBall_sum {ℓ : ℝ} (hℓ : 0 < ℓ) (W : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Λ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' n : Fin 3 → ℤ,
        if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ then
          Work.BoseBoxFock.LatFourier.latFt ℓ W n *
            Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))
        else 0)
      = ∑ n ∈ Work.BoseBoxFock.LatFourier.latBall (Λ * ℓ / (2 * Real.pi)),
          Work.BoseBoxFock.LatFourier.latFt ℓ W n *
            Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ)) := by
  -- The two frequency cut-offs agree: `‖k_n‖ ≤ Λ` iff `‖latVec n‖ ≤ Λℓ/(2π)`.
  have hmom : ∀ n : Fin 3 → ℤ,
      ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ ↔
        n ∈ Work.BoseBoxFock.LatFourier.latBall (Λ * ℓ / (2 * Real.pi)) := by
    intro n
    rw [Work.BoseBoxFock.LatFourier.mem_latBall]
    have h2 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
    have h3 : ‖Work.BoseBoxFock.kmomInt ℓ n‖
        = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ := by
      rw [Work.BoseBoxFock.LatFourier.kmomInt_eq_smul_latVec, norm_smul,
        Real.norm_of_nonneg h2.le]
    have h4 : Λ * ℓ / (2 * Real.pi) = Λ / (2 * Real.pi / ℓ) := by field_simp
    rw [h3, h4, le_div_iff₀ h2,
      mul_comm (2 * Real.pi / ℓ) ‖Work.BoseBoxFock.latVec n‖]
  -- The `tsum` of a function vanishing off the finite set `latBall` is the finite sum.
  have h : (∑' n : Fin 3 → ℤ,
        (if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ then
          Work.BoseBoxFock.LatFourier.latFt ℓ W n *
            Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))
        else 0))
      = ∑ n ∈ Work.BoseBoxFock.LatFourier.latBall (Λ * ℓ / (2 * Real.pi)),
          (if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ then
            Work.BoseBoxFock.LatFourier.latFt ℓ W n *
              Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))
          else 0) :=
    tsum_eq_sum (L := SummationFilter.unconditional (Fin 3 → ℤ))
      (s := Work.BoseBoxFock.LatFourier.latBall (Λ * ℓ / (2 * Real.pi)))
      (f := fun n : Fin 3 → ℤ => if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ Λ then
          Work.BoseBoxFock.LatFourier.latFt ℓ W n *
            Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ))
        else 0)
      (fun n hn => by
        rw [if_neg]
        intro hc
        exact hn ((hmom n).mp hc))
  rw [h]
  exact Finset.sum_congr rfl fun m hm => by rw [if_pos ((hmom m).mpr hm)]

end Work.BoseBoxFock
