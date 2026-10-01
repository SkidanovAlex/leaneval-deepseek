import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaPerronDefs

namespace Work.ZeroDensity.Ingham

/-- The two horizontal edge integrals of the patched (entire) integrand
`perronH K Y ρ = dslope (perronM K Y ρ) (1-ρ)` over the segment `p ≤ Re w ≤ q` tend to `0` as the
height `R → ∞`.  Indeed `perronM w = Γ(w+1)·dslope (ζ₁(ρ+·)) 0 w·Y^w·M_K(ρ+w)` is bounded by
`C·(1+‖w‖)^A·exp(-(π/2)|Im w|)` on the strip (`Γ` decays exponentially by
`Commons.Analysis.Complex.Gamma_vertical_norm_bounds`, `ζ₁` and the divided difference grow
polynomially by `Commons.NumberTheory.Zeta.zeta_strip_polyGrowth`, `M_K` and `Y^w` are bounded),
and dividing `perronM w - perronM (1-ρ)` by `w - (1-ρ)` costs only a factor `1/R` for large `R`.
The two edges are handled separately (no conjugation symmetry is available here).
`Commons.NumberTheory.DirichletCharacter.rect_edge_tendsto_zero`-style estimates
(`Work.LinnikAreas.Density4.rect_edge_tendsto_zero`) give the conclusion from the pointwise bound. -/
theorem perronH_horizontal (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) {p q : ℝ}
    (hpq : p ≤ q) (hp1 : -1 ≤ ρ.re + p) (hq3 : ρ.re + q ≤ 3) (hp6 : -6 ≤ p) (hq4 : q ≤ 4) :
    Filter.Tendsto (fun R : ℝ => ∫ x in p..q,
        Work.ZeroDensity.Ingham.perronH K Y ρ ((x : ℂ) + (R : ℂ) * Complex.I))
        Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun R : ℝ => ∫ x in p..q,
        Work.ZeroDensity.Ingham.perronH K Y ρ ((x : ℂ) - (R : ℂ) * Complex.I))
        Filter.atTop (nhds 0) := by
  sorry

end Work.ZeroDensity.Ingham
