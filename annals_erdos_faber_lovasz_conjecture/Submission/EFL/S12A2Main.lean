import Submission.EFL.S12MainA2
import Submission.EFL.OptColOdd

/-!
# §12: the Type A₂ branch (cone-switch note)

This module used to hold `s12_A2_main`, the threshold form of `s12_branch_A2` with the
constants of `S12ANum` pinned to a single master constant `σ` (`ρ = σ/2`, `ε = σ³/10⁴²`) and
with the Colouring input read off the *linear* GKO statement.

**Removed 2026-09-23 by the CONE SWITCH.**  The pinned architecture needs one `σ` with
`σ/2 = ρ ≥ 4p*` and simultaneously `σ³/10⁴² ≤ ε₀(p*)`, `σ/10¹⁴ ≤ ε₀(p*)`,
`22σ³/10⁴² ≤ η₀(p*)`, where `ε₀(p), η₀(p)` are the existential thresholds of the faithful
Corollary 10.13 — a fixed-point condition in unknown functions, unsolvable in general (take
`ε₀(p) = exp(-exp(1/p))`).  The branch is now *parametric in `(ρ, ε)`*: the colouring input is
taken freely below the thresholds by
`ErdosFaberLovaszConjecture.s12_branch_A2_faithful` (`Submission/Work/S12Faithful/Branch.lean`),
and §12 is driven by `Work.ConeSwitch.eflStatement_of_deep_faithful`
(`Submission/Work/ConeSwitch/Assembly.lean`), which chooses `ρ := σ/2` first and then `ε` below
`ε₀(ρ/4)`.

The (unused) imports are kept so that the module stays in the cone's import graph; the
conditional linear lemmas remain available as
`ErdosFaberLovaszConjecture.optcol_corollary_{core,even,odd}` from
`ErdosFaberLovaszConjecture.GKOStatementLinear`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

end

end ErdosFaberLovaszConjecture
