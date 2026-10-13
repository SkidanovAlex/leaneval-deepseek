/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLimCont.lean` — pointwise continuity of the limit family

Let `(G n)` be the (level-`0`) Galerkin family of the strong-`ε` chapter and `F : ℝ → Fn` its
limit family: at each *fake time* `τ ∈ Icc 0 T` the slices `slice (G n) τ` converge locally
uniformly on the open quadrant `Q0` to `F τ` (the package `ConvLev0H6`).  Assume moreover that
each *single* slice family `τ ↦ slice (G n) τ` is Lipschitz in `τ`, with one constant `C` valid
for all `n` on every compact `K ⊆ Q0` (the `hlip` hypothesis — it is what the a-priori
`∂_τ`-bound of the Galerkin scheme supplies).

Then the limit family inherits the Lipschitz property pointwise: for every `(z,θ) ∈ Qd` the
function `τ ↦ F τ z θ` is Lipschitz (hence continuous) on `Icc 0 T`, with the *same* constant
`C` — apply `hlip` to the singleton `{(z,θ)}`, use local uniform convergence at `(z,θ)` to take
the pointwise limit of `|G n z θ τ - G n z θ τ'| ≤ C|τ - τ'|`, and conclude with
`LipschitzOnWith.continuousOn`.

This is the "τ-continuity of the limit" step of the strong-`ε` extraction (module `E5` of
`FTS_STRONG_ROUTE.md`): the extracted limit `F` is a genuine continuous curve of profiles, which
is what allows the Volterra/ODE step to identify it with the solution.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongEps.ConvLev0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsLimCont {α B T : ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {F : ℝ → Work.FTS.Galerkin.Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
          ≤ C * |τ - τ'|) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => F τ z θ) (Set.Icc (0 : ℝ) T) := by
  intro z θ hQ
  -- `Qd` and `Q0` are the same set (the open quadrant `(0,∞) × (0,π/2)`).
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hQ
  have hKsub : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Set.mem_singleton_iff.mp hp ▸ hQ0
  -- the `τ`-Lipschitz constant of the scheme, valid for all `n` at the *single* point `(z,θ)`.
  obtain ⟨C, hC0, hC⟩ := hlip {(z, θ)} isCompact_singleton hKsub
  -- local uniform convergence at the singleton `{(z,θ)}` is pointwise convergence at `(z,θ)`.
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) T, Tendsto (fun n => G n z θ τ) atTop (𝓝 (F τ z θ)) := by
    intro τ hτ
    have h1 := (hconv τ hτ).conv {(z, θ)} isCompact_singleton hKsub
    have h2 := h1.tendsto_at (Set.mem_singleton _)
    simpa [Work.FTS.Galerkin.slice_apply] using h2
  refine LipschitzOnWith.continuousOn (K := ⟨C, hC0⟩) ?_
  refine LipschitzOnWith.of_dist_le_mul (K := ⟨C, hC0⟩) ?_
  intro x hx y hy
  have hxy : ∀ n, |G n z θ x - G n z θ y| ≤ C * |x - y| := by
    intro n
    have h := hC n (z, θ) (Set.mem_singleton _) x hx y hy
    simpa [Work.FTS.Galerkin.slice_apply] using h
  have hlim : Tendsto (fun n => |G n z θ x - G n z θ y|) atTop (𝓝 |F x z θ - F y z θ|) :=
    ((hpt x hx).sub (hpt y hy)).abs
  have := le_of_tendsto' hlim hxy
  rw [Real.dist_eq, Real.dist_eq]
  exact this

end Work.FTS.StrongEps
