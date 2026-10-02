/-
# The modulus form of the Böttcher equation: `‖φ_c (T_c z)‖ = ‖φ_c z‖²`

On `CritDomain c` the (branch-free) modulus half of the Böttcher equation holds
for the product formula: `‖φ_c (T_c z)‖ = ‖φ_c z‖ ^ 2`.  Equivalently, the defect
`ζ(z) = φ_c(T_c z) / conj (φ_c z)^2` of the product formula is always unimodular;
what can fail off the far region is only its argument (a root of unity), see
`Work.Bottcher.Core.ProductFormulaTelescoping` and `NOTES.md` §4.
-/
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar)

theorem norm_bottcher_Tantibar (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    ‖Work.Bottcher.bottcher c (Tantibar c z)‖ = ‖Work.Bottcher.bottcher c z‖ ^ 2 := by
  rw [norm_bottcher_domain c _ (Critical.CritDomain_Tantibar_mem c z hz),
    norm_bottcher_domain c z hz, Green.green_comm]
  rw [two_mul, Real.exp_add, sq]

end Work.Bottcher.Core
