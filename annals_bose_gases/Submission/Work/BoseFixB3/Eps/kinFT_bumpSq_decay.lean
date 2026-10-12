import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB3.Eps.Defs
import Submission.Work.OneBodyKin.kinFT_decay_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Eps.kinFT_bumpSq_decay`

The bump profile `bumpSqC = (χ² : ℝ³ → ℂ)` of `Work.BoseFixB3.Eps` has a `p`-convention
Fourier transform decaying faster than any polynomial:

    `∃ C ≥ 0, ∀ q, ‖kinFT bumpSqC q‖ ≤ C / (1 + ‖q‖)^N`.

This is the analytic input recorded in the header of `Work.BoseFixB3.Eps.Defs` (the whole
content of `B3EpsRoot` being that `(1−f_L)(χ_ℓ²)` is small of order `(κℓ)^{-s}`).

The mathematical content is that `χ` is `C^∞` with compact support (`chi_contDiff`,
`chi_hasCompactSupport`), so `χ²` is too, and the Fourier transform of a smooth compactly
supported function is Schwartz, hence rapidly decreasing.  The quantitative Schwartz-space
statement is already in the corpus as `Work.OneBodyKin.kinFT_decay_le` (which builds the
Schwartz map `𝓢(ℝ³,ℂ) ∋ χ ↦ 𝓕χ`, applies `SchwartzMap.one_add_le_sup_seminorm_apply` and
undoes the `(2π)⁻¹` frequency rescaling); here we only observe that `bumpSqC` falls under its
hypotheses: it is the composition of the smooth compactly supported real function `χ²` with
`Complex.ofRealCLM`.
-/

noncomputable section

open scoped Real Topology

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- `bumpSqC` is the complexification of the smooth compactly supported real profile `χ²`. -/
private lemma bumpSqC_contDiff : ContDiff ℝ (⊤ : ENat) bumpSqC :=
  Complex.ofRealCLM.contDiff.comp (chi_contDiff.pow 2)

/-- `bumpSqC` is compactly supported, its support being contained in that of `χ`. -/
private lemma bumpSqC_hasCompactSupport : HasCompactSupport bumpSqC := by
  refine chi_hasCompactSupport.mono (fun x hx => ?_)
  simp only [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [bumpSqC, h])

/-- **Polynomial decay of the bump profile `χ²`.**  For every `N` there is `C ≥ 0` with
`‖kinFT (χ²) q‖ ≤ C / (1 + ‖q‖)^N` at every momentum `q`. -/
theorem kinFT_bumpSq_decay (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.kinFT Work.BoseFixB3.Eps.bumpSqC q‖ ≤ C / (1 + ‖q‖) ^ N :=
  Work.OneBodyKin.kinFT_decay_le N bumpSqC_contDiff bumpSqC_hasCompactSupport

end Work.BoseFixB3.Eps
