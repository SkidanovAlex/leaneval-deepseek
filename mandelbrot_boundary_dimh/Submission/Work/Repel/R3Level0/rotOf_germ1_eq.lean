import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.pushdown_deriv
import Submission.Work.Repel.rotOf_pushdown_rescale

namespace Work.Repel.R3Level0

open MandelDim Complex Set Metric Filter Topology

noncomputable section

theorem rotOf_germ1_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ)
    (a₁ a₂ : ℕ) (β : ℂ) (s : ℂ) (hs : s ≠ 0)
    (hrot : MandelDim.rotOf f = MandelDim.alphaOf a₁ a₂ β)
    (ha₁ : 2 ≤ a₁) (ha₂ : 4 ≤ a₂) (hβre : 0 ≤ β.re) (hβre' : β.re < 1) :
    MandelDim.rotOf (Work.Repel.germ1 s P.R) = 1 / ((a₂ : ℂ) + β) := by
  -- The upper-end asymptotic of the lifted return map `R` gives the derivative of its pushdown.
  have hderiv : deriv (pushdown P.R) 0 =
      Complex.exp (-(2 * Real.pi * I * (1 / alphaOf a₁ a₂ β))) := by
    have hd := pushdown_deriv (E := P.R) (DR := P.DR) (y := y₁) (c := 1 / rotOf f)
      P.DR_open P.R_equiv P.R_holo (fun w hw => P.DR_sub (Or.inr hw)) P.R_upper
    rw [hd.deriv, hrot]
    simp only [piExp]
    congr 1
    ring
  have h := rotOf_pushdown_rescale a₁ a₂ β s hs hderiv ha₁ ha₂ hβre hβre'
  exact h

end

end Work.Repel.R3Level0
