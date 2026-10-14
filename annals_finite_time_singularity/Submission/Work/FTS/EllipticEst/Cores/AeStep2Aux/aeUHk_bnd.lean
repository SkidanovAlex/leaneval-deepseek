import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.Prop.cutEnergyProof
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.step1Ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology

set_option autoImplicit false



/-- **`HkMem α 0 (grad u)` for an `AeData` datum**, taken from the proved module
`Work.FTS.EllipticEst.Dispatch.hkMem_gradUD` (the same statement as
`Work.FTS.EllipticEst.H2W.Ae.hkMem_gradU`, on a self-contained import cone; it is the honesty
clause of the radial Agmon–Nirenberg interpolation, which needs only `HkMem α 0 u` and
`HkMem α 0 (z²∂_zz u)` — no norm bound, and no `z`-integration by parts). -/
theorem hkMem_grad_of {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
  Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h


end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

/-- **The `ρ`-bound of `u` (the `u`-half of Step 1 of `prop:H2`) in the a.e. class.**

For every datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic
estimate (equation `bslOp α u = G` on the *open* quadrant, Dirichlet data as values, `C^∞` on
the open quadrant, the two a.e. moment conditions, and `HkMem α 0` of `G`, `z²∂_zz u`, `∂_θθ u`
only), the `ρ = w²σ`-norm of `u` is dominated by that of the source `G`:

  `nrm α u ≤ C * nrm α G`,  `nrm α f = √(HkSq α 0 f)`,  `σ θ = sin(2θ)^{-η}`.

The `HkMem α 0 u` hypothesis is redundant (it is derivable from `AeData` alone, see
`Cores.AeStep2Aux.aeUHk_mem`, the a.e. slicewise weighted second-order Poincaré inequality
`∫_θ u²σ ≤ C ∫_θ (∂_θθu)²σ`); it is kept because that is how the lemma was requested.

The mathematics is the team's proved Step 1 in the a.e. class
(`AngAWeak.aeUHk`): the truncated `w²`-energy inequality `α²A + B ≤ K·M + ½‖G‖²_ρ`
with `K = 13/2 + 3α² + (3/2)α(5+α) < 9`, the constrained slice gap `9∫_θ u² ≤ ∫_θ (∂_θu)²`
which absorbs the `K·M` term (`K/9 < 1`, giving `B ≤ 15‖G‖²_ρ`), and the `σ`-Poincaré
upgrade `‖u‖²_ρ ≤ C_σ·B`; the norm bound follows by monotonicity of `Real.sqrt`. -/
theorem aeUHk_bnd : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u →
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨C, hC, h⟩ := Work.FTS.EllipticEst.AngAWeak.aeUHk
  exact ⟨C, hC, fun α u G hA _ => (h α u G hA).2⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
