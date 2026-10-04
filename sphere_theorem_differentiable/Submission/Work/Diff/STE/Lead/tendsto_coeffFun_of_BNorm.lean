import Mathlib
import Submission.Work.Diff.STE.Lead.CoeffRepr
import Submission.Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm
import Submission.Work.Diff.STE.Lead.transfer_tendsto

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Coefficientwise convergence from `H⁰` (`BNorm 0`) convergence

This file proves the *forward* direction of the equivalence between convergence of the composite
norm `D.BNorm k` and coefficientwise convergence of the localised components `D.Rper i · a b`.

The content is one estimate plus the linearity of the coefficient functional in the section:

* `fourierCoeff_le_sqrt_BNorm` (`Submission/Work/Diff/STE/Lead/fourierCoeff_le_sqrt_BNorm.lean`)
  gives, for every section `h` with smooth chart data and *every* multi-index `μ`,
  `‖ĉ_μ (D.Rper i h a b)‖ ≤ 1 · √(D.BNorm 0 h)`;
* the coefficient functional is additive in the section,
  `ĉ_μ (Rper i (X - Y) a b) = ĉ_μ (Rper i X a b) - ĉ_μ (Rper i Y a b)`
  (`Work.Diff.STE.Lead.Rper_fourierCoeff_sub`), so that the difference of two coefficients is the
  coefficient of the difference of the sections.

Hence `‖ĉ_μ (u m t) - ĉ_μ (U t)‖ ≤ √(D.BNorm 0 (u m t - U t))`, and the hypothesis
`hconv t ht 0` makes the right-hand side tend to `0`.  The squeeze lemma `squeeze_zero` applied to
the modulus of the difference, together with `tendsto_iff_norm_sub_tendsto_zero`, concludes.

Only the `k = 0` instance of `hconv` is used (which is why the statement can be read as
"`H⁰`-convergence implies coefficientwise convergence"); the `D`-dependence of the limit is only
through the linearity of the components.  The smoothness input enters twice: to *state* the bound
`fourierCoeff_le_sqrt_BNorm` and to write the coefficient of a *difference* of sections as the
difference of coefficients (both localised components must be `C^∞`); closure of
`Work.Diff.STE.D.ChartData` under subtraction is `Work.Diff.STE.Lead.ChartData_sub`.
-/

namespace Work.Diff.STE.Lead

theorem tendsto_coeffFun_of_BNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ : ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hsmU : ∀ (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hconv : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u m t - U t)) Filter.atTop (nhds 0))
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) τ₀) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (μ : Fin (Module.finrank ℝ E) → ℤ) :
    Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
      Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)) := by
  -- the universal comparison of a coefficient with the `H⁰` norm of the section
  obtain ⟨C, _hC, hbound⟩ := Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm (I := I) (M := M) D
  -- the difference of the two sections again has smooth chart data
  have hCD : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t - U t) :=
    fun m => Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) (u m t) (U t) (hsm m t) (hsmU t)
  -- additivity of the coefficient functional in the section
  have hlin : ∀ m : ℕ,
      Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
      = Work.Diff.STE.fourierCoeff (D.Rper i (u m t - U t) a b) μ := by
    intro m
    exact (Work.Diff.STE.Lead.Rper_fourierCoeff_sub D (u m t) (U t) i a b μ
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (u m t - U t) (hCD m) i a b)
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (u m t) (hsm m t) i a b)
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (U t) (hsmU t) i a b)).symm
  -- the majorant tends to `0`, by continuity of `√·` and the hypothesis `hconv`
  have hb : Filter.Tendsto (fun m : ℕ => C * Real.sqrt (D.BNorm 0 (u m t - U t)))
      Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto (fun m : ℕ => Real.sqrt (D.BNorm 0 (u m t - U t)))
        Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp (hconv t ht 0)
    have := hcomp.const_mul C
    simpa using this
  -- squeeze the modulus of the difference between `0` and the majorant
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hb
  rw [hlin m]
  exact hbound (u m t - U t) (hCD m) i a b μ

end Work.Diff.STE.Lead
