import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.remov.AeChainDefs
import Submission.Work.FTS.EllipticEst.AeS1.Assembly
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.AeS1.sigFirstOrderD
import Submission.Work.FTS.EllipticEst.AeS1.sigmaUpD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

/-
Step 1 of Elgindi's `prop:H2` (Annals 194 (2021), tex 849–870) in the almost-everywhere class
`H2W.Ae.AeData` (`Submission/Work/FTS/EllipticEst/H2W/Ae/Defs.lean`), i.e. the missing
inhabitant of the `Prop` `remov.AeStep1Full` (already defined in `remov/AeChainDefs.lean`):
`u`, `z ∂_z u` and `u/cos θ` are honest in `ℋ⁰` and

  `‖u‖_ρ ≤ C‖G‖_ρ`, `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`,
  `‖u/cos θ‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`,

with `‖g‖_ρ = H2W.Ae.nrm α g = √(HkSq α 0 g)` and `ρ = w²σ`, `σ = sin(2θ)^{-η}`.

PROOF (this file is the assembly; the analytic content is in the `AeS1` modules).

`Work.FTS.EllipticEst.AeS1.aeStep1Full_of_bar` reduces the target to four inputs:

* `hE` — the unweighted (`w²`-only) first-order energy inequality
  `α²‖z∂_zu‖²_{w²} + ‖∂_θu‖²_{w²} ≤ C‖G‖²_ρ` together with the two `L2Mem` honesty conjuncts;
  supplied by `Work.FTS.EllipticEst.AeS1.unwEnergyD`;
* `hU` — the σ-Poincaré upgrade `HkSq α 0 u ≤ C·L2Sq (∂_θu·w)`;
  supplied by `Work.FTS.EllipticEst.AeS1.sigmaUpD`;
* `hD` — the σ-weighted radial inequality `α²‖z∂_zu‖²_ρ ≤ C(‖G‖²_ρ + ‖u‖²_ρ)` and
  `hBar` — `HkSq α 0 (u/cos θ) ≤ C(‖G‖²_ρ + ‖u‖²_ρ)`: both are the conjuncts of
  `Work.FTS.EllipticEst.AeS1.sigFirstOrderD` (the σ-weighted *first-order* energy inequality,
  obtained by pairing `bslOp α u = G` with `u·w²σ` — the `sec²θ`-slot of that pairing gives the
  `u/cos θ` bound, so Step 2 is not needed).

The four conjuncts `HkMem α 0 u`, `HkMem α 0 (z∂_zu)`, `‖u‖_ρ ≤ C‖G‖_ρ`, `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`
are produced inside `AeS1.aeStep1Full_of_bar` (inlined `step1_of`), the honesty of `u/cos θ` by
the axiom-clean `H2W.AeProof.BarAux.hkMemBar`, and the `u/cos θ` norm by
`sigFirstOrderD`.  All ingredients are `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
theorem AeStep1FullHolds : Work.FTS.EllipticEst.remov.AeStep1Full := by
  obtain ⟨C₂, hC₂, hsig⟩ := Work.FTS.EllipticEst.AeS1.sigFirstOrderD
  exact Work.FTS.EllipticEst.AeS1.aeStep1Full_of_bar
    Work.FTS.EllipticEst.AeS1.unwEnergyD
    Work.FTS.EllipticEst.AeS1.sigmaUpD
    ⟨C₂, hC₂, fun α u G hA => ⟨(hsig α u G hA).1, (hsig α u G hA).2.1⟩⟩
    ⟨C₂, hC₂, fun α u G hA => (hsig α u G hA).2.2⟩

end Work.FTS.EllipticEst.remov
