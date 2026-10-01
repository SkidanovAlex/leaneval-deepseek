import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs

namespace Work.ZeroDensity.Ingham

/-- The patched Perron integrand `perronH K Y ρ = dslope (perronM K Y ρ) (1-ρ)` is complex
differentiable on every closed rectangle of the half plane `Re w > -1`.

`perronM K Y ρ w = Γ(w+1)·dslope (fun t => ζ₁(ρ+t)) 0 w·Y^w·M_K(ρ+w)` is a product of functions
analytic on `{w : ℂ | -1 < w.re}` (`Γ(w+1)` has its poles at `w = -1,-2,…`, and `w+1 ∉ -ℕ` for
`Re w > -1`; the divided difference of the entire function `ζ₁(ρ+·)` with base point `0` is entire
by `Complex.differentiableOn_dslope`; `Y^w` is entire for `Y ≠ 0`; and `M_K(ρ+·)` is a finite sum of
`μ(n)·n^{-(ρ+w)}`, hence entire).  By `differentiableOn_dslope_of_isOpen_mem`
(`Submission/Work/LinnikAreas/triPerron_dslope_diff.lean`) the difference quotient
`dslope (perronM K Y ρ) (1-ρ)` is then differentiable on the rectangle, because the open set
`{Re > -1}` contains the rectangle and the base point `1-ρ` (`Re(1-ρ) = 1 - Re ρ > -1`). -/
theorem perronH_differentiable (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) {p q R : ℝ}
    (hp : -1 < p) (hq : -1 < q) (hρ : ρ.re < 2) :
    DifferentiableOn ℂ (Work.ZeroDensity.Ingham.perronH K Y ρ)
      (Set.uIcc p q ×ℂ Set.uIcc (-R) R) := by
  sorry

end Work.ZeroDensity.Ingham
