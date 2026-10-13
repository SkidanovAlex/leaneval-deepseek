/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/limFam_EpsMem.lean`

**The Fatou metric clause of `hlimP`** (the `X = (EpsMem, EpsSq)` half of the limit slice's
membership in the `X`-ball): if every Picard iterate `slice (iter F h₀ n) τ` is a member of the
weighted space `X` with `EpsSq ≤ R`, and the iterates converge pointwise on the open quadrant to
`slice (limFam F h₀) τ`, then the limit slice is a member of `X` with the same bound `R`.

This is the closing step of the local step's limit clause (`NOTES_LimSmoothOpen.md`,
"WHAT TO DO NEXT" item 1): the three metric/structural clauses of `hlimP` are now

* `SmoothOpen`  — `LimSmoothOpenEngine.smoothOpen_limFam_slice_of_iter_bounds` (proved),
* `EpsMem`/`EpsSq` — **this file**,
* the class-`C` clause and the ball clause — blocked on the flatness statement (see the notes).

The proof is `EpsMem_and_EpsSq_le_of_ae_tendsto_mem` (the junk-free Fatou lemma for the
`ℝ≥0∞`-valued size `epsL2`) fed with

* the iterate-wise membership/bounds (hypothesis),
* the a.e.-on-`DomM` convergence, obtained from the everywhere-on-the-open-quadrant convergence by
  `EpsLocalPStar.ae_of_forall_open`.

Everything is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.EpsMem_and_EpsSq_le_of_ae_tendsto_mem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter

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
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-- **The metric clause of `hlimP`**: the limit slice of a Picard sequence which stays in the
weighted `X`-ball of radius `R` is itself in that ball. -/
theorem limFam_EpsMem {α R δ : ℝ} {F : Fn → Fn} {h₀ : Fn} (hR : 0 ≤ R)
    (hconv : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => slice (iter F h₀ N) τ z θ) Filter.atTop
        (nhds (slice (limFam F h₀) τ z θ)))
    (hP : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc 0 δ →
      EpsMem α (slice (iter F h₀ n) τ) ∧ EpsSq α (slice (iter F h₀ n) τ) ≤ R) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      EpsMem α (slice (limFam F h₀) τ) ∧ EpsSq α (slice (limFam F h₀) τ) ≤ R := by
  intro τ hτ
  refine EpsMem_and_EpsSq_le_of_ae_tendsto_mem (α := α) (B := R) hR
    (A := fun n : ℕ => slice (iter F h₀ n) τ)
    (Alim := slice (limFam F h₀) τ)
    (fun n => (hP n τ hτ).1) (fun n => (hP n τ hτ).2) ?_
  exact ae_of_forall_open (fun z hz θ hθ0 hθ1 => hconv τ hτ z θ hz hθ0 hθ1)

end Work.FTS.EpsEngine
