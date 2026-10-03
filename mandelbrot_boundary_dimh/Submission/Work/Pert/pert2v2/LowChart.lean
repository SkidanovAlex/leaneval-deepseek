import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.pert2v2.RBlockCharts

/-!
# `Work.Pert.pert2v2.LowChart` — the low piece's *clause set*: definitions and continuity

The low chart of the two-piece return map (`pert2_v2`'s `Ulow`) is *defined* by the crux's clause at
its points:

  `clause w := (∀ j ≤ m, f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp' ∧
                F (invOn τ Qp' (f^[m] (φ w))) ∈ Qp'`,

together with the crux's residual `‖Φp (invOn τ Qp' (f^[m] (φ w))) - m - dlow - Ψ w‖ < δ`.

The point of defining the chart that way is that the two facts the R-block needs on it — the
`+1`-relation (`Work.Pert.RBlock4.Rlow_add_one_pointwise`, needing the clause at `w` and `w+1`) and
the estimate (`pert2v2.Rlow_close_of_res`, needing the residual at `w`) — then hold *by
construction*, with no reference to the crux's compact `Kb`.

For this to be a legitimate chart the set must be **open**, which is what the continuity lemmas here
provide: `w ↦ f^[m] (φ w)` is continuous on the clause set, hence so is
`w ↦ invOn τ Qp' (f^[m] (φ w))` (that is `pert2v2.invOn_continuousAt`, from the local inverse of
`τ` at the unique preimage), hence so are the two remaining conditions.
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric
open scoped Topology

noncomputable section

/-- The crux's clause at `w` for the pair `(φ, Qp', m, F, τ)`. -/
def Clause (f : ℂ → ℂ) (Df : Set ℂ) (F τ φ : ℂ → ℂ) (Qp' : Set ℂ) (m : ℕ) (w : ℂ) : Prop :=
  (∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp' ∧
    F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp'

/-- The low piece's residual at `w`: the crux's residual with the level shift `m` and the constant
`dlow` undone (`Ψ` is the model horn map `d.E` in the assembly). -/
def Resid (Φp Ψ τ : ℂ → ℂ) (Qp' : Set ℂ) (m : ℕ) (dlow : ℂ) (δ : ℝ) (φ : ℂ → ℂ)
    (f : ℂ → ℂ) (w : ℂ) : Prop :=
  ‖Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - dlow - Ψ w‖ < δ

variable {f F τ Φp Ψ φ : ℂ → ℂ} {Df Qp' V : Set ℂ} {m : ℕ} {dlow : ℂ} {δ : ℝ}

/-- **The walk-map is continuous at a point of the clause set**: `w ↦ f^[m] (φ w)`. -/
theorem continuousAt_iterate_phi (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V)
    (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df) {w₀ : ℂ} (hw₀ : w₀ ∈ V)
    (hwalk : ∀ j : ℕ, j ≤ m → f^[j] (φ w₀) ∈ Df) :
    ContinuousAt (fun w : ℂ => f^[m] (φ w)) w₀ := by
  have hφc : ContinuousAt φ w₀ := hφ.continuousOn.continuousAt (hV.mem_nhds hw₀)
  have hstep : ∀ j : ℕ, j ≤ m → ContinuousAt (fun w : ℂ => f^[j] (φ w)) w₀ := by
    intro j hj
    induction j with
    | zero => simpa using hφc
    | succ k ih =>
      have hk : k ≤ m := le_trans (Nat.le_succ k) hj
      have hmem : f^[k] (φ w₀) ∈ Df := hwalk k hk
      have h2 : ContinuousAt f (f^[k] (φ w₀)) :=
        hf.continuousOn.continuousAt (hDf.mem_nhds hmem)
      have h3 : ContinuousAt (fun w : ℂ => f (f^[k] (φ w))) w₀ :=
        h2.comp (g := f) (f := fun w : ℂ => f^[k] (φ w)) (ih hk)
      simpa only [Function.iterate_succ_apply'] using h3
  exact hstep m le_rfl

/-- **The `invOn`-map is continuous at a point of the clause set**:
`w ↦ invOn τ Qp' (f^[m] (φ w))` — it is the local inverse of `τ` at the unique preimage of the
landing value. -/
theorem continuousAt_invOn_iterate (hQp' : IsOpen Qp') (hτ : DifferentiableOn ℂ τ Qp')
    (hinjτ : Set.InjOn τ Qp') (hτne : ∀ z ∈ Qp', deriv τ z ≠ 0)
    (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    {w₀ : ℂ} (hw₀ : w₀ ∈ V) (hwalk : ∀ j : ℕ, j ≤ m → f^[j] (φ w₀) ∈ Df)
    (hland : f^[m] (φ w₀) ∈ τ '' Qp') :
    ContinuousAt (fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) w₀ := by
  obtain ⟨ς, hςQ, hςτ⟩ := hland
  have hseed : ContinuousAt (fun w : ℂ => f^[m] (φ w)) w₀ :=
    continuousAt_iterate_phi hV hφ hDf hf hw₀ hwalk
  have hinv : ContinuousAt (fun v : ℂ => Work.Pert.invOn τ Qp' v) (f^[m] (φ w₀)) := by
    rw [← hςτ]
    exact invOn_continuousAt hQp' hτ hinjτ hςQ (hτne ς hςQ)
  exact hinv.comp (g := fun v : ℂ => Work.Pert.invOn τ Qp' v)
    (f := fun w : ℂ => f^[m] (φ w)) hseed

end

end Work.Pert.pert2v2
