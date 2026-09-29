import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.amoM_section

namespace Work.TMComp.MAnalytic

/-- The Möbius action of the transfer matrix `tmC lam w x` (viewed as a function of the
complex energy `w`) is holomorphic on the Kotani domain: it equals
`w - 2λ cos 2πx - 1/(M w x)` there, and `M w x` never vanishes because its imaginary part
is positive. -/
theorem differentiableOn_mob_tmC_M {lam a b : ℝ} {M : ℂ → ℝ → ℂ}
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (Work.TMContract.kotaniDomain a b))
    (him : ∀ z ∈ Work.TMContract.kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) (x : ℝ) :
    DifferentiableOn ℂ
      (fun w => Work.TMContract.mob (Work.TMContract.tmC lam w x) (M w x))
      (Work.TMContract.kotaniDomain a b) := by
  have hmain : DifferentiableOn ℂ
      (fun w : ℂ => w - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) - (M w x)⁻¹)
      (Work.TMContract.kotaniDomain a b) := by
    have h1 : DifferentiableOn ℂ
        (fun w : ℂ => w - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ))
        (Work.TMContract.kotaniDomain a b) :=
      differentiableOn_id.sub (differentiableOn_const _)
    have h2 : DifferentiableOn ℂ (fun w : ℂ => (M w x)⁻¹)
        (Work.TMContract.kotaniDomain a b) :=
      (hhol x).inv (fun w hw => by
        have h := him w hw x
        intro h0
        rw [h0] at h
        simp at h)
    exact h1.sub h2
  refine hmain.congr (fun w hw => ?_)
  rw [amoM_mob_tmC lam w x (by
    have h := him w hw x
    intro h0
    rw [h0] at h
    simp at h)]
  rw [one_div]

end Work.TMComp.MAnalytic
