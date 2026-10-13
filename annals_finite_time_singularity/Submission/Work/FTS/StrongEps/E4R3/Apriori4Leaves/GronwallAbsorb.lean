import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/GronwallAbsorb.lean` — LEAF L-C (**PROVED**, session 23)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 L-C).  Grönwall with an
`ε`-absorbed quadratic defect (continuous induction on the bound `2(1+E0)e^{2(Λ+1)T}`).

**Status: proved.**  The statement is byte-identical to the delegated sibling
`Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof`
(`Submission/Work/FTS/StrongEps/E4R3/Apriori4Proofs/gronwall_absorb_proof.lean`), which this file
now re-exports; the proof is the barrier/first-crossing argument, with its two auxiliary
real-analysis lemmas (`grAux_gronwall_le_exp`, `grAux_no_cross_up`) in the sibling module.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

set_option autoImplicit false

/-- **LEAF (L-C), proved** `e' ≤ Λ(1+e) + εC₁(1+e)²`, `ε` small ⟹ `1+e ≤ (1+E0)e^{2(Λ+1)T}`. -/
theorem gronwall_absorb {e : ℝ → ℝ} {T Λ C₁ ε E0 : ℝ} (hT : 0 < T) (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hε : 0 ≤ ε) (hE0 : 0 ≤ E0)
    (hcont : ContinuousOn e (Icc 0 T))
    (hd : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧
      e' ≤ Λ * (1 + e τ) + ε * C₁ * (1 + e τ) ^ 2)
    (he0 : e 0 ≤ E0)
    (hsmall : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) ≤ Λ + 1) :
    ∀ τ ∈ Icc 0 T, 1 + e τ ≤ (1 + E0) * Real.exp (2 * (Λ + 1) * T) :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.gronwall_absorb_proof hT hΛ hC₁ hε hE0 hcont hd he0 hsmall

end Work.FTS.StrongEps.EpsE4Thr.E4R4
