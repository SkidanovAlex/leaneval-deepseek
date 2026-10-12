import ChallengeDeps
import Submission.Work.BoseFixGlue.EΛBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Ports.Small` — the small ports of the proved BoseBox chapter

The proved BoseBox chapter (`Work.BoseBox.Nodes`, `Work.BoseBox.B2Reduction`) contains two
glue statements whose statements mention the old (false/vacuous) `CSBox` vocabulary but whose
*proofs* are pure arithmetic/order bookkeeping, so they port verbatim to the frozen vocabulary of
`Work.BoseBoxFix.Defs`:

* `nodeB0B_dichotomy` — FS `eq:aprioriPsi`'s dichotomy (port of `Work.BoseBox.nodeB0_dichotomy`):
  every box state is either *low* at `J`, or already satisfies the box bound at `(η₀, C)`.  Uses
  only `Λ ≤ Θ` (`Work.UBB.theta_ge_lambda`).
* `B2AprioriWindowB_of_NodeB1B` — the §5→§6 glue (port of
  `Work.BoseBox.B2AprioriWindow_of_NodeB1`): the second conjunct of `NodeB1B` is the only §5 input
  of §6.

Both are used by `Work.BoseFixGlue.Ports.LHYBoxB_of_grading` (the port of the BoseBox assembly
`boxBound_of_grading` + `LHYBox_of_grading`) and by the §6 reduction
`Work.BoseFixGlue.Ports.nodeB2gB_of_data`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The low/non-low dichotomy -/

/-- **`B0` in the frozen vocabulary**: every box state is either low at `J` (FS
`eq:aprioriPsi`), or already satisfies the box bound `ℓ³Λ(a, C, η₀, μ)‖Φ‖² ≤ wordB Φ`.

Proved from the a-priori threshold comparison `Λ ≤ Θ` (`Work.UBB.theta_ge_lambda`) and linear
order; port of `Work.BoseBox.nodeB0_dichotomy`. -/
theorem nodeB0B_dichotomy {v : ℝ³ → ℝ} {h : ScatSol v} {J η₀ C μ : ℝ}
    (hJ : lhyC ≤ J) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hμ : 0 < μ) (hav : 0 < a v) {n : ℕ}
    (Φ : BoxState n (ℓB v μ)) :
    IsLowB v h J μ n Φ ∨ BoxBoundB v h η₀ C μ n Φ := by
  by_cases hlow : IsLowB v h J μ n Φ
  · exact Or.inl hlow
  · refine Or.inr ?_
    have hΘ : Lambda (a v) C η₀ μ ≤ Theta (a v) J μ :=
      theta_ge_lambda (A := a v) (K := C) (J := J) (η₀ := η₀) (ρ := μ)
        hav.le hμ.le hC hJ
    have hnn : 0 ≤ normB v μ n Φ := normB_nonneg v μ n Φ
    have hℓpos : 0 < ℓB v μ := sideB_pos hμ hav
    have hℓ3 : 0 < (ℓB v μ) ^ 3 := pow_pos hℓpos 3
    have hkey : (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ * normB v μ n Φ
        ≤ (ℓB v μ) ^ 3 * Theta (a v) J μ * normB v μ n Φ := by
      have h1 := mul_le_mul_of_nonneg_left hΘ hℓ3.le
      exact mul_le_mul_of_nonneg_right h1 hnn
    exact le_trans hkey (le_of_lt (not_le.mp hlow))

/-! ## 2. The §5 → §6 glue -/

/-- **The only §5 input of §6** (port of `Work.BoseBox.B2AprioriWindow_of_NodeB1`): the second
conjunct of `NodeB1B` — the a-priori `n₊`-window `cnPlus ℓ Φ ≤ C nPlusWindow‖Φ‖²` — *is* the
datum `B2AprioriWindowB` that the §6 reduction `nodeB2gB_of_data` consumes, at the same constant
and the same smallness threshold.  (In the frozen statements `NodeB1B` and `B2AprioriWindowB`
share the shape `C·nPlusWindow·‖Φ‖²`, so no `+1` bookkeeping is needed; this is the port of the
old chapter's `B2AprioriWindow_of_NodeB1`.) -/
lemma B2AprioriWindowB_of_NodeB1B {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    (hav : 0 < a v) (h1 : NodeB1B v h J) : B2AprioriWindowB v h J := by
  obtain ⟨C₁, C₂, ε₀, hC₁, hC₂, hε₀, hN1⟩ := h1
  exact ⟨C₂, ε₀, hC₂, hε₀,
    fun μ hμ hKB n Φ hnorm hlow => (hN1 μ hμ hKB n Φ hnorm hlow).2⟩

end Work.BoseFixGlue
