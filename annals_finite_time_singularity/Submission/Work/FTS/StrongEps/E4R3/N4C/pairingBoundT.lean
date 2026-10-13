/-
# `E4R3/N4C/pairingBoundT` — the honest §8 pairing bound from the honest row table

The deliverable of this task: from the honest (`HQo`-based) `IP`-interface `N4C.N4ExtraH` and the
honest row table `N4C.RowsT`, the pairing of N4's right-hand side satisfies

  `|rhsPair IP α g (Φ_* + Φ_g)| ≤ CcN · Pbd α (Xn α g)`

for all `α` in a range `(0, α₄]`, `α₄ ≤ α₂`, and all class-`C` data.

The proof is `PairingT.pairing_bound_of_rowsT` (`PairingT/Assembly.lean`), which assembles the
four blocks `gRHS = -μ̄·AK + N₀ + N + N_*` out of the honest per-piece table
`PairingT.RowInputsTO` (built from `RowsT` by `PairingT.rowInputsTO_of_rows`, using the two
piece-smoothness bundles `PairingT.smoothOpen_pieces_N0` / `…_N`) and the four block estimates
`PairingT.AKTerm_boundT`, `…N0Term_boundT`, `…NTerm_boundT`, `…NsTerm_boundT`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem pairingBoundT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ct Ce Cs : ℝ} (hCs : 0 < Cs) (hCe : 0 < Ce)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct)
    (hR : Work.FTS.StrongEps.E4R3.N4C.RowsT IP α₂ Ce Cs) :
    ∃ CcN α₄ : ℝ, 0 < CcN ∧ 0 < α₄ ∧ α₄ ≤ α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₄, ∀ {g Φs Φg : Work.FTS.Galerkin.Fn},
        Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
        Work.FTS.Nonlin.Xn α g ≤ α ^ (7 / 4 : ℝ) →
        |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
          ≤ CcN * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g) :=
  pairing_bound_of_rowsT IP hCs hCe hE hR

end Work.FTS.StrongEps.E4R3.N4C
