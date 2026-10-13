import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EllEstUnif_top_core_of_halves`: the top core from its two slot estimates

`Work.FTS.EllipticEst.remov.EllEstUnif_top_core` (the `hcore` slot of
`EllEstUnif_step_of_pieces`, hence of `EllEstUnif_step`) asks for

  `α²√(Tk α k (z²∂_zzΨ)) + √(Tk α k (∂_θθΨ)) ≤ C |F|_k`

under `EllWeakPos α k F Ψ` and the two level-`(k-1)` bounds (constant `D`).  Writing
`A := z²∂_zzΨ`, `B := ∂_θθΨ`, the exact identity

  `α² A + B = ∂_θ(tanθ·Ψ) - 6Ψ - F - α(5+α) D_z Ψ =: R̃`   (the equation `bslOp α Ψ = F`)

(the pointwise identity behind `(★★)` in `remov/NOTES_EllEstUnif_step.md`) means the two
summands can be estimated *separately*:

* the `A`-slot `α²√(Tk α k A)` — the radial estimate, delegated as `A_top_slot_bound`;
* the `B`-slot `√(Tk α k B)` — delegated as `B_top_slot_bound` (its proof uses the identity
  above together with `A_top_slot_bound` and `Rtilde_Tk_bound`).

This file performs the (elementary) combination: it takes the two slot estimates as *hypotheses*
(so that it is independent of the order in which they land, and carries no `sorry` itself) and
returns the frozen `EllEstUnif_top_core`. -/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- **The top core from its two slot estimates.**  Both slot bounds are stated with exactly the
hypotheses of `EllEstUnif_top_core` (so they are the conclusions of `A_top_slot_bound` and
`B_top_slot_bound`); their sum is the top core, with constant `C_A + C_B`. -/
theorem EllEstUnif_top_core_of_halves (D : ℝ) (hD : 0 < D)
    (hA : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          ≤ C * Work.Spaces.HkNorm α k F)
    (hB : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
        Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
          ≤ D * Work.Spaces.HkNorm α k F →
        α ^ 2 * Work.Spaces.HkNorm α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
            + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          ≤ D * Work.Spaces.HkNorm α k F →
        Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
          ≤ C * Work.Spaces.HkNorm α k F) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
          ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨CA, hCApos, hCA⟩ := hA k hk
  obtain ⟨CB, hCBpos, hCB⟩ := hB k hk
  refine ⟨CA + CB, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1 h2
  have eA := hCA α F Ψ hα hα4 hwk h1 h2
  have eB := hCB α F Ψ hα hα4 hwk h1 h2
  calc α ^ 2 * Real.sqrt (Step.Tk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + Real.sqrt (Step.Tk α k (Work.Spaces.pthIter 2 Ψ))
      ≤ CA * Work.Spaces.HkNorm α k F + CB * Work.Spaces.HkNorm α k F := add_le_add eA eB
    _ = (CA + CB) * Work.Spaces.HkNorm α k F := by ring

end Work.FTS.EllipticEst.remov
