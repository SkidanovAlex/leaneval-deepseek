import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.n0SpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0ExclFunOp` — the slot-`i`-**excluded** spectral functional calculus

For `Aᵢ := Σ_{j≠i} Pⱼ = n₀ − Pᵢ` (the number of *other* condensed particles) the operator `g(Aᵢ)`
is the explicit finite sum over the subset idempotents `Proj_S = n0ProjOp volA A S`

    (g(Aᵢ) Ψ)(x) = Σ_S  g (|S| − 1_{i∈S}) · (Proj_S Ψ)(x) .

This is the object the `√`-completion of squares of FS `lm:appinteractionestimate` needs, in the
form that **avoids the fibre-commutator loss**: the fibre `fib(xᵢ)` does *not* commute with `n₀`
(`n0OpSlotComm`), but it *does* commute with every `Pⱼ`, `j ≠ i`, hence with every polynomial in
`Aᵢ` — and, modulo the identification of the polynomial and the spectral calculus on the box, with
`g(Aᵢ)`.  See `LEDGER_IK_session1.md` §1.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The slot-`i`-excluded functional calculus `g(Aᵢ) = g(n₀ − Pᵢ)`, as an explicit spectral sum
over the subset idempotents. -/
def exclFunOp {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (g : ℝ → ℝ)
    (Ψ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ S : Finset (Fin N),
    g ((S.card : ℝ) - (if i ∈ S then 1 else 0)) * ((n0ProjOp volA A S) Ψ x)

/- The basic algebraic properties of `exclFunOp` (linearity, multiplicativity, self-adjointness,
commutation with the fibre `fib(xᵢ)` for `i ≠ j`, and its action on the subset idempotents) are
*not* definitional: `n0ProjOp` is a composition of slot projections, so linearity needs the
integrability side conditions.  They are requested as `Work.BoseFixB1S.exclFunOpPropsB1`. -/

end Work.BoseFixB1S
