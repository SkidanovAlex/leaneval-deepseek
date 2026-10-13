/-
# `Work.FTS.StrongPersist.L3RhsPriced` — the `ℋ³`-estimate for the right-hand side (S6)

The target is the `rhs` clause of the level-three operator package `L3Data` of the
strong-solution route (`FTS/FTS_STRONG_ROUTE.md` §3, node S6), in the *priced* form of
`Clauses.lean`: for `α ∈ (0, α₂]`, a star constant `Cs`, an elliptic perturbation constant `Ce`,
a linear elliptic operator `E`, stream functions `Φs`, `Φ`, a profile `f` and modulation data
`μ`, `lam`, `M` with

* `Ell6Ctx α Ce Cs E Φs f Φ` (the star package `StarPkgo2`, the perturbation package
  `EllPkgK α 6 Ce f (E f)` and the decomposition `Φ = Φs + E f`),
* `H6Adm α f` (honest `ℋ⁶` + angular vanishing + axis vanishing + `L₁₂(f)(0) = 0`),
* `Xn α f ≤ M`, `|μ| ≤ 1/2`, `|lam| ≤ 1`,

the nonlinear right-hand side `rhsOf α μ lam (Ftot α f) Φ f` of the modulated `g`-equation lies
in `ℋ³` with

  `|rhsOf …|_{ℋ³} ≤ C3 (1+|Ce|+|Cs|)⁴ α^{-Cpow} (1+M)⁴ (1+|f|_{ℋ⁶})²`.

## Route (and where the pieces live)

`gRHS = -mubar(N₀,N)·AK α + N₀ + N + Nstar`, and `N₀`, `N` are split into the paper's rows
(`L3Rhs.L3RhsSum`):

* the `N₀`-split is `L3Rhs.Assembly.N0split`, the four-way split of `N` is
  `NonlinRows.Rl1.splitOpen` (with `L₁₂`/`FK`-additivity from `L3Rhs.L3RhsL12add` /
  `L3Rhs.L3RhsFKadd` and the differentiability of `z ↦ L₁₂(f)(z)` from
  `L3Rhs.Assembly.L12_differentiableAt`);
* the nine blocks are estimated by the delegated lemmas `L3Rhs.L3Rhs*` of this directory;
* the summands are added with `L3Rhs.Pricing.HkNorm_add_le2`;
* the modulation constant is priced by `L3Rhs.L3RhsL12zero` through `L3Rhs.Assembly.muAK_mem`;
* `AK α` is `ℋ⁴`-honest (`NonlinRows.NAux3.HkMem_AK`) with a universal norm bound
  (`Nonlinear.Pieces.rak_bound`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.Pricing
import Submission.Work.FTS.StrongPersist.L3Rhs.Sum
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0FixBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0gBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNssBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNsgBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNgsBound
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNggBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNfkBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12zero
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12add
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem L3RhsPriced : ∃ α₂ C3 Cpow : ℝ, 0 < α₂ ∧ 0 < C3 ∧ 0 ≤ Cpow ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce Cs : ℝ) (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn)
      (Φs Φ f : Work.FTS.Galerkin.Fn) (μ lam M : ℝ),
      Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Φ →
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      Work.Spaces.HkMem α 3
          (Work.FTS.StrongPersist.rhsOf α μ lam (Work.Construction.Ftot α f) Φ f) ∧
      Work.Spaces.HkNorm α 3
          (Work.FTS.StrongPersist.rhsOf α μ lam (Work.Construction.Ftot α f) Φ f)
        ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4
            * (1 + Work.Spaces.HkNorm α 6 f) ^ 2 := by
  obtain ⟨CN, hCN, hNstar⟩ := L3Rhs.L3RhsNstarBlock
  obtain ⟨C0, hC0, hN0fix⟩ := L3Rhs.L3RhsN0FixBlock
  obtain ⟨Cg, Cpg, a2g, hCg, hCpg, ha2g, hN0g⟩ := L3Rhs.L3RhsN0gBlock
  obtain ⟨Cs1, Cps1, a2s1, hCs1, hCps1, ha2s1, hNss⟩ := L3Rhs.L3RhsNssBlock
  obtain ⟨Cs2, Cps2, a2s2, hCs2, hCps2, ha2s2, hNsg⟩ := L3Rhs.L3RhsNsgBlock
  obtain ⟨Ce1, Cpe1, a2e1, hCe1, hCpe1, ha2e1, hNgs⟩ := L3Rhs.L3RhsNgsBound
  obtain ⟨Ce2, Cpe2, a2e2, hCe2, hCpe2, ha2e2, hNgg⟩ := L3Rhs.L3RhsNggBlock
  obtain ⟨Cf, Cpf, a2f, hCf, hCpf, ha2f, hNfk⟩ := L3Rhs.L3RhsNfkBlock
  obtain ⟨CL, hCL, hL12z⟩ := L3Rhs.L3RhsL12zero
  obtain ⟨KAK, hKAK, hAKb⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  exact L3Rhs.L3RhsSum CN hCN hNstar C0 hC0 hN0fix Cg Cpg a2g hCg hCpg ha2g hN0g
    Cs1 Cps1 a2s1 hCs1 hCps1 ha2s1 hNss
    Cs2 Cps2 a2s2 hCs2 hCps2 ha2s2 hNsg
    Ce1 Cpe1 a2e1 hCe1 hCpe1 ha2e1 hNgs
    Ce2 Cpe2 a2e2 hCe2 hCpe2 ha2e2 hNgg
    Cf Cpf a2f hCf hCpf ha2f hNfk CL hCL hL12z
    (fun α hαIoc => L3Rhs.L3RhsL12add α hαIoc)
    (fun α hαIoc => L3Rhs.L3RhsFKadd α hαIoc)
    KAK hKAK (fun α hαIoc => hAKb (α := α) hαIoc.1 hαIoc.2)

end Work.FTS.StrongPersist
