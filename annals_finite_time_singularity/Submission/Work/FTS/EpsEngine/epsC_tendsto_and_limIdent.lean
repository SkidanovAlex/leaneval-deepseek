/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/epsC_tendsto_and_limIdent.lean`

**The `epsC`-convergence and the limiting identity**, extracted from the tail of
`SORuling`'s / this directory's `smoothOpen_limFam_slice` (`LimSmoothOpen.lean`).

The two conclusions are obtained by reading the *mollified form* `hmoll` of the `(n+1)`-st Picard
iterate at a single point `(z₀, θ₀) = (3/4, 5π/16)` where the projection bump is non-zero
(`bump_eq_zero_iff`), which *determines* `epsC n τ` as an explicit ratio:

    epsC n τ = (h₀ z₀ θ₀ + J_ε (Ψ_n) z₀ θ₀ − slice (epsIter (n+1)) τ z₀ θ₀) / bump z₀ θ₀ ,

so it converges by `hJeps` at that point and `hconv` composed with `n ↦ n+1`.  The identity at every
point of the open quadrant is then uniqueness of limits (`tendsto_nhds_unique`).

**Notation note.**  The statement was requested with the bare token `π` in the two `θ ∈ Ioo 0 (π/2)`
occurrences; the file below therefore opens the `Real` scope (`open scoped Real`) so that `π` means
`Real.pi`, as in every other file of this development.  Without the scope, `π` would be
auto-bound by `autoImplicit` as a *free* implicit variable `{π : ℝ}`, which changes the meaning of
the statement (for `π ≤ Real.pi/2` it would demand the unconditional convergence of `epsC`, i.e. the
convergence of `epsC α ρ ε Φs E h₀ n τ` for completely arbitrary data).  The declaration text is
otherwise byte-for-byte the requested one.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.LimSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option linter.unusedVariables false

theorem epsC_tendsto_and_limIdent {α C₀ R Ce Cs Lw q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn} {δ : ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ =>
          Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ N) s z θ)
        Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {PsiL : Work.FTS.Galerkin.Fn}
    (hJeps : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n τ) z θ)
        Filter.atTop (nhds (Work.FTS.StrongEps.Jeps ρ ε PsiL z θ))) :
    ∃ cLim : ℝ, Filter.Tendsto (fun n : ℕ => Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n τ)
        Filter.atTop (nhds cLim) ∧
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) τ z θ
          = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ - cLim * Work.FTS.StrongEps.bump z θ := by
  -- the point where the projection bump does not vanish
  have hyz : 0 < (3 : ℝ) / 4 := by norm_num
  have hyθ : (5 * Real.pi / 16) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbumpne : bump ((3 : ℝ) / 4) (5 * Real.pi / 16) ≠ 0 := by
    intro h
    have h' := bump_eq_zero_iff.mp h
    rcases h' with h' | h' | h' | h'
    · norm_num at h'
    · norm_num at h'
    · have := Real.pi_pos; nlinarith
    · have := Real.pi_pos; nlinarith
  -- the limit coefficient, read off the mollified form at `(3/4, 5π/16)`
  set cLim : ℝ := (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
      + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
      - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))
      / bump ((3 : ℝ) / 4) (5 * Real.pi / 16) with hcLimdef
  have hClim : Filter.Tendsto (fun n : ℕ => epsC α ρ ε Φs E h₀ n τ) Filter.atTop
      (nhds cLim) := by
    have hcongr : ∀ n : ℕ, epsC α ρ ε Φs E h₀ n τ
        = (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
            + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
            - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))
          / bump ((3 : ℝ) / 4) (5 * Real.pi / 16) := by
      intro n
      have h := hmoll n τ hτ ((3 : ℝ) / 4) (5 * Real.pi / 16) hyz hyθ
      have h2 : epsC α ρ ε Φs E h₀ n τ * bump ((3 : ℝ) / 4) (5 * Real.pi / 16)
          = h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
            + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
            - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4)
                (5 * Real.pi / 16) := by
        linarith [h]
      field_simp [hbumpne]
      linarith [h2]
    have hnum : Filter.Tendsto (fun n : ℕ => h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
        + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
        - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4) (5 * Real.pi / 16)) Filter.atTop
        (nhds (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
          + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
          - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))) := by
      refine (tendsto_const_nhds.add (hJeps _ _ hyz hyθ)).sub ?_
      exact ((hconv τ hτ ((3 : ℝ) / 4) (5 * Real.pi / 16) hyz hyθ.1 hyθ.2).comp
        (tendsto_add_atTop_nat 1))
    have hdiv := hnum.div_const (bump ((3 : ℝ) / 4) (5 * Real.pi / 16))
    rw [hcLimdef]
    refine (Filter.Tendsto.congr' ?_ hdiv)
    exact Eventually.of_forall fun n => (hcongr n).symm
  refine ⟨cLim, hClim, ?_⟩
  -- the identity at every point of the open quadrant, by uniqueness of limits
  intro z θ hz hθ
  have hL : Filter.Tendsto (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ)
      Filter.atTop (nhds (slice (epsLim α ρ ε Φs E h₀) τ z θ)) :=
    (hconv τ hτ z θ hz hθ.1 hθ.2).comp (tendsto_add_atTop_nat 1)
  have hR : Filter.Tendsto (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
      - epsC α ρ ε Φs E h₀ n τ * bump z θ) Filter.atTop
      (nhds (h₀ z θ + Jeps ρ ε PsiL z θ - cLim * bump z θ)) :=
    ((tendsto_const_nhds.add (hJeps z θ hz hθ)).sub (hClim.mul_const (bump z θ)))
  have heq : (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ)
      =ᶠ[Filter.atTop] (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
        - epsC α ρ ε Φs E h₀ n τ * bump z θ) :=
    Eventually.of_forall fun n => hmoll n τ hτ z θ hz hθ
  exact tendsto_nhds_unique hL ((Filter.tendsto_congr' heq).mpr hR)

end Work.FTS.EpsEngine
