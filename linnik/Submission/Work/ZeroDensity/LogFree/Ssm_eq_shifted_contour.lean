import Mathlib
import Submission.Work.LinnikAreas.Density4.Ssm_fixed_bound
import Submission.Work.LinnikAreas.Density4.integrable_Phi_line_one
import Submission.Work.LinnikAreas.Density4.Ssm_eq_line
import Submission.Work.LinnikAreas.Density4.SsmPhiAux
import Submission.Work.LinnikAreas.Density4.diffOn_Gamma_dslope_mul_lcmF

namespace Work.ZeroDensity.LogFree

/-- **The contour shift.** For a non-principal `χ`, a zero `ρ` of `L(·,χ)` in the strip, and a
line `Re s = c₁` with `-1 < c₁ ≤ 1`, the smoothed sum `Ssm` equals `(1/2π)∫ Φ(c₁+it)dt` for the
regularised integrand `Φ s = Γ(s+1)·(L(ρ+s)-L(ρ))/s·X^s·F(ρ+s)`, provided `Φ` is integrable on the
line `Re s = c₁` and the two horizontal edge integrals over `[c₁,1] × {±R}` tend to `0`.

This is `Work.LinnikAreas.Density4.Ssm_contour_shift` with the specific shift target
`c₁ = 1 - Re ρ - 1/k` replaced by an arbitrary `c₁ ∈ (-1,1]`, and the concrete analytic inputs
(the line bound `hLbd` and the distance-to-`0` hypothesis `hdist`, which were used there only to
*verify* integrability) replaced by the integrability and edge hypotheses themselves.

Proof ingredients (all already proved in this workspace, `Work.LinnikAreas.Density4`):
`Ssm_eq_naive_line` + `Phi_eq_naive` give `Ssm = (1/2π)∫ Φ(1+it)dt`;
`integrable_Phi_line_one` gives integrability on `Re s = 1` (needs only `hU, hUV, hV, hW, hX, hχ,
hβ0, hL0`); `diffOn_Gamma_dslope_mul_lcmF` gives differentiability of `Φ` on the closed rectangle
`[c₁,1] × [-R,R]` (needs `-1 < c₁ ≤ 1`, `0 < X`, `χ ≠ 1`); then
`Commons.Analysis.Complex.vertical_contour_shift` applied to `Φ` with `p = c₁`, `q = 1`,
`hInt`, the two edge hypotheses and the derived line-one integrability yields the claim. -/
theorem Ssm_eq_shifted_contour (q : ℕ) [NeZero q] {U V W X c₁ : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) (hβ0 : 0 < ρ.re)
    (hL0 : DirichletCharacter.LFunction χ ρ = 0)
    (hc₁ : -1 < c₁) (hc₁le : c₁ ≤ 1)
    (hInt : MeasureTheory.Integrable
      (fun t : ℝ => Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((c₁ : ℂ) + (t : ℂ) * Complex.I)))
    (htop : Filter.Tendsto
      (fun R : ℝ => ∫ x : ℝ in c₁..1,
        Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto
      (fun R : ℝ => ∫ x : ℝ in c₁..1,
        Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) :
    Work.LinnikAreas.Density4.Ssm q U V W X χ ρ = (1 / (2 * Real.pi)) *
      ∫ t : ℝ, Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((c₁ : ℂ) + (t : ℂ) * Complex.I) := by
  -- Step 1: Mellin representation of `Ssm` on the naive line `Re s = 1`.
  have hA := Work.LinnikAreas.Density4.Ssm_eq_naive_line q U V W X χ ρ hU hUV
    (by linarith) hX hβ0
  -- Step 2: off `s = 0` the naive integrand coincides with the regularised one.
  have hstep2 : (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
        * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
        * DirichletCharacter.LFunction χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
        * Work.LinnikAreas.Density4.lcmF q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
      = (1 / (2 * Real.pi)) *
          ∫ t : ℝ, Work.LinnikAreas.Density4.Phi q U V W X χ ρ
            ((1 : ℂ) + (t : ℂ) * Complex.I) := by
    congr 1
    have hFG : (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
          * DirichletCharacter.LFunction χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I))
          * Work.LinnikAreas.Density4.lcmF q U V W χ (ρ + ((1 : ℂ) + (t : ℂ) * Complex.I)))
        = fun t : ℝ => Work.LinnikAreas.Density4.Phi q U V W X χ ρ
            ((1 : ℂ) + (t : ℂ) * Complex.I) := by
      funext t
      have hsne : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        simp at hre
      rw [Work.LinnikAreas.Density4.Phi_eq_naive q U V W X χ ρ
        ((1 : ℂ) + (t : ℂ) * Complex.I) hL0 hsne]
    rw [hFG]
  -- Step 3: `Φ` is differentiable on the closed rectangle `[c₁,1] × [-R,R]`.
  have hFd : ∀ R : ℝ, DifferentiableOn ℂ (Work.LinnikAreas.Density4.Phi q U V W X χ ρ)
      (Set.uIcc c₁ 1 ×ℂ Set.uIcc (-R) R) := fun R =>
    Work.LinnikAreas.Density4.diffOn_Gamma_dslope_mul_lcmF q U V W X χ hχ hX ρ c₁ 1 hc₁ hc₁le R
  -- Step 4: integrability of `Φ` on the naive line `Re s = 1`.
  have hIq := Work.LinnikAreas.Density4.integrable_Phi_line_one q hU hUV hV hW hX χ hχ ρ hβ0 hL0
  -- Step 5: the contour shift from `Re s = 1` down to `Re s = c₁`.
  have hshift := Commons.Analysis.Complex.vertical_contour_shift
    (Work.LinnikAreas.Density4.Phi q U V W X χ ρ) c₁ 1 hc₁le hFd hInt hIq htop hbot
  rw [hA, hstep2]
  exact congrArg (fun z : ℂ => (1 / (2 * Real.pi)) * z) hshift

end Work.ZeroDensity.LogFree
