import Mathlib
import Submission.Work.ZeroDensity.Ingham.residueCommonsDeps

namespace Work.ZeroDensity.Ingham

/-- Explicit Gamma-factor norm bound for `1 - ρ` on the critical strip with `|Im ρ| ≥ 1`:
this is `Commons.Analysis.Complex.gamma_upper_final` applied at `x = 1 - ρ.re` (which lies in
`[0, 1/2] ⊂ [-5,5]`) and `y = -ρ.im` (so `|y| = |ρ.im| ≥ 1`), using
`1 - ρ = (1 - ρ.re) + I·(-ρ.im)`. -/
lemma gammaOneSubNormBound (ρ : ℂ) (hβ1 : 1 / 2 ≤ ρ.re) (hβ2 : ρ.re ≤ 1) (hγ : 1 ≤ |ρ.im|) :
    ‖Complex.Gamma (1 - ρ)‖ ≤
      Commons.Analysis.Complex.K11 * Real.exp (-(Real.pi / 2) * |ρ.im|) * (1 + |ρ.im|) ^ 20 := by
  have hx : (1 - ρ.re) ∈ Set.Icc (-5) 5 := ⟨by linarith, by linarith⟩
  have hy : 1 ≤ |(-ρ.im)| := by rw [abs_neg]; exact hγ
  have h := Commons.Analysis.Complex.gamma_upper_final (1 - ρ.re) (-ρ.im) hx hy
  have harg : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) + Complex.I * ((-ρ.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [harg]
  simpa [abs_neg] using h

end Work.ZeroDensity.Ingham
