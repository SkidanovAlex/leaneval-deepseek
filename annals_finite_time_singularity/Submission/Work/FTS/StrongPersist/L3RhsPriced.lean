import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0gBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNfkBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNsgBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNssBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.FTS.StrongPersist.L3Rhs.Sum
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongEps.HkMem_Jeps_ten_of_eight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/- **`J_ε : ℋ⁸ → ℋ¹⁰`** for every `ε > 0`: the two-order gain of the log-coordinate mollifier.

This is the `m = 2`, `k = 8` instance of the *scale-free* gain
`Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos`
(`Submission/Work/FTS/StrongEps/TenOfEight/GainAll.lean`), which removes the restriction
`ε ≤ 1` of `EpsE4Thr.HkMem_Jeps_gain` by replacing the routed density
`LamFull ρ ε c M` (whose domination of the routed kernel derivatives needs `ε⁻¹^{a+b} ≤ ε⁻¹^M`,
i.e. `ε ≤ 1`) by the scale-free density `LamAll ρ ε c M` with the kernel factor
`max 1 (ε⁻¹^M)`.  The boundary-vanishing hypothesis of that theorem is never used
(`J_ε f` only reads `f` on the open quadrant, and the gain is a pointwise estimate on
`(0,∞) × (0,π/2)`), so it is not needed here. -/
theorem HkMem_Jeps_ten_of_eight {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α 8 f) :
    Work.Spaces.HkMem α 10 (Jeps ρ ε f) :=
  Work.FTS.StrongEps.TenOfEight.HkMem_Jeps_gain_pos hρ α hα.1 hα.2 8 2 (by norm_num) ε hε f
    hsm hmem

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3RhsPriced =====
section

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
end
end
