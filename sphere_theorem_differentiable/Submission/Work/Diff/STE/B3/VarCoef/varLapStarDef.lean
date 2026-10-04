import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The formal adjoint of `varLap A B`, and its `k`-th power

`varLap A B g = -(Σ_{a b} A a b · ∂_a ∂_b g + Σ_a B a · ∂_a g)` (`VarCoef/Defs.lean`).  Its formal
adjoint for the flat pairing `∫ f · g` on the torus is obtained by two integrations by parts:

  `varLapStar A B h = -(Σ_{a b} ∂_a ∂_b (A a b · h) + Σ_a ∂_a (B a · h))`.

This file only *defines* `varLapStar`, its `k`-th power and the associated composite `POpStar`
(the adjoint of `POp c c' (varLapOp A B) k`), because these are the objects the adjoint-side
estimates of `ENormB_pair_J_commutator_v2` are stated with.  The two facts that make them useful —

* `varLapStar A B` **is** the `L2re`-adjoint of `varLap A B` on smooth `1`-periodic functions
  (integration by parts, `pd` being skew-adjoint), and
* `varLapStar A B = varLap A B + (an operator of order ≤ 1)`

(the second is the Leibniz expansion `∂_a∂_b(A·h) = A ∂_a∂_b h + 2(∂_aA)∂_b h + h ∂_a∂_bA` etc.) —
are proved in the delegated modules `varLapStar_adjoint` and `POp_star_sub_isOrd`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The formal adjoint of `varLap A B` for the flat pairing (no complex conjugation: all the
coefficients are real). -/
noncomputable def varLapStar (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  -((∑ a, ∑ b, Work.Diff.STE.pd a (Work.Diff.STE.pd b (fun x => ((A a b x : ℝ) : ℂ) * g x)))
    + ∑ a, Work.Diff.STE.pd a (fun x => ((B a x : ℝ) : ℂ) * g x))

/-- `varLapStar A B` as an operator. -/
noncomputable def varLapStarOp (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) : Op ι :=
  fun g => varLapStar A B g

/-- The `k`-th power of `varLapStar A B`. -/
noncomputable def varLapStarPow (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) :
    ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ) :=
  (varLapStar A B)^[k]

/-- The composite `M_c ∘ (D^*)^k ∘ M_{c'}` — the formal adjoint of `POp c c' (varLapOp A B) k`. -/
noncomputable def POpStar (c c' : (ι → ℝ) → ℝ)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (k : ℕ) : Op ι :=
  compOp (compOp (mulOp c) ((varLapStarOp A B)^[k])) (mulOp c')

/-- `varLapStarPow k A B` is the `k`-fold iterate of `varLapStarOp A B` (the form in which the
order calculus composes it). -/
theorem varLapStarPow_apply (k : ℕ) (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (g : (ι → ℝ) → ℂ) :
    varLapStarPow k A B g = ((varLapStarOp A B)^[k]) g := rfl

end Work.Diff.STE.B3.VarCoef
