import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local chart-transfer layer (definitions)

This module holds the definition of the **local chart transfer** `perTransfer` (and the three
SESSION-19 auxiliary definitions `localPairOp`, `clippedInv`, `stripFun`) that used to live in
`Submission/Work/Diff/STE/B3/ENormB_pair_J_commutator_v2.lean`.

They were moved here (SESSION 22) because the low-level files of the `SymCalcStep8` layer
(`pdTransferKit`, `perTransfer_csq_le_of_support`) need `perTransfer`, and importing the target
module `ENormB_pair_J_commutator_v2` from them created a **build cycle**: the target must import
the `VarCoef` layer (`varLapPow_cut_comm_pairing`, `R_Qk_chartExpr`, `mat_csq_le_components`,
`POp_swap_sub_star_isOrd`), which imports `VarCoef/Assembly`, which imports `SymCalcStep8`.

Since `perTransferDef` imports only the `SymCalc*` layer and Mathlib, it is safe to import from
below.  The fully qualified names are unchanged (`Work.Diff.STE.B3.perTransfer` etc.), so every
existing user of the definitions still sees them (the target module imports this one).

`perTransfer c τ W` is the **periodisation** of `c · (W ∘ τ)`: for `W` `1`-periodic and `c` smooth,
compactly supported, this is the component-level chart transfer `L_{il} W` with `c` the transfer
coefficient and `τ` the transition map — and it is a *well-defined* periodic (smooth) function,
unlike `compMap τ W`. -/

namespace Work.Diff.STE.B3

/-- The **local chart transfer**: the periodisation of `c · (W ∘ τ)` (`W` `1`-periodic). -/
noncomputable def perTransfer {ι : Type*} [Fintype ι] (c : (ι → ℝ) → ℂ)
    (τ : (ι → ℝ) → (ι → ℝ)) (W : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun z => ∑' m : ι → ℤ, c (z + Work.Diff.STE.iVec m) * W (τ (z + Work.Diff.STE.iVec m))

/-- ⚠ **A DANGEROUS MODEL — not the cross pair.**  `a·(Λ(b·T_γ(S g)) − S(b·T_γ(Λ g))) +
c·(Λ(b·T_{γ'}(S g)) − S(b·T_{γ'}(Λ g)))` with `T = perTransfer`, `Λ = lapPow k`, `S = flatCut ρ ε`:
the two groups of `ϑ_{il} = Λ L_{il} S − S L_{il} Λ` and `ϑ_{li} = Λ L_{li} S − S L_{li} Λ` acting on
the *same* periodic function `g`.  Its principal symbol is
`abγ[λ^kρ(εB^Tξ) − ρ(εξ)λ(B^Tξ)^k] + cdγ'[λ^kρ(εB'^Tξ) − ρ(εξ)λ(B'^Tξ)^k]` (`B = Dτ`, `B' = Dτ'`),
which does **not** vanish — so `localPairOp` is a single-chart model of the pair and any bound of
its pairing of the requested shape is FALSE.  It is kept as a named warning (header SESSION 19 (5))
of that temptation. -/
noncomputable def localPairOp {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (τ τ' : (ι → ℝ) → (ι → ℝ))
    (γ γ' : (ι → ℝ) → ℂ) (a b c d : (ι → ℝ) → ℂ) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun x => a x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun z => b z * perTransfer γ τ (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) z) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun z => b z * perTransfer γ τ (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) z) x)
    + c x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun z => d z * perTransfer γ' τ' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) z) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun z => d z * perTransfer γ' τ' (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) z) x)

/-- The **clipped normalising inverse** of a transfer weight `γ`: `χ / perγ`, with `χ` the clipping
function (`1` on the region where the normalisation is imposed, `0` where `perγ` is too small). -/
noncomputable def clippedInv {ι : Type*} [Fintype ι] (χ : (ι → ℝ) → ℝ) (γ : (ι → ℝ) → ℝ) :
    (ι → ℝ) → ℝ :=
  fun y => χ y / (∑' m : ι → ℤ, γ (y + Work.Diff.STE.iVec m))

/-- The **boundary-strip multiplier** `1 − γinv·(γ∘σ)` of the transfer pair `(γ, γinv)`. -/
noncomputable def stripFun {ι : Type*} (γ γinv : (ι → ℝ) → ℝ)
    (σ : (ι → ℝ) → (ι → ℝ)) : (ι → ℝ) → ℝ :=
  fun z => 1 - γinv z * γ (σ z)

end Work.Diff.STE.B3
