import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemU

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

/-- **The level-`0` `ℋ`-honesty of the solution in the a.e. class.**  For every `AeData α u G`,
i.e. for every `u` solving `bslOp α u = G` on the open quadrant with the two a.e. moment
conditions (plus `HkMem` of `G`, of `z²∂_zz u` and of `∂_θθ u`), one has `HkMem α 0 u`.

The mathematics is the a.e. slicewise second-order Poincaré inequality
`∫_θ u(z,θ)²σ θ ≤ C ∫_θ (∂_θθ u)(z,θ)²σ θ` (`σ = sin(2θ)^{-η}`), valid for a.e. `z > 0`: the
two moment conditions kill the affine mode invisible to `∂_θθ`, and the endpoint behaviour of
the slices at `θ → π/2` removes the rest.  That slice bound is `H2W.Ae.aesliceU_of`, fed with
the two-derivative weighted Hardy inequality `H2W.Ae.ZeroHardy.sliceZeroLimitHardy` and
`H2W.Ae.AeSliceRightTendsto`; it is then integrated in `z` against `HkMem`-honesty of `u`'s
slices.

The proof is the one of `Work.FTS.EllipticEst.H2W.Ae.hkMem_u`; we cite the definitionally
identical, self-contained clean-cone copy `Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_u`
(module `H2W/AngBW/Step3/HkMemU.lean`), whose import cone avoids
`Honest.firstOrderHonest` — the one module of the canonical `H2W/Ae/hkMem_u.lean` cone that is
currently unbuildable (its environment carries the declaration
`Work.FTS.EllipticEst.Honest.contDiffOn_slice` from both `Honest.HonDifQuotBound` and
`Honest.HonSliceRightTendsto`). -/
theorem aeUHk_mem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u :=
  fun α u G h => Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_u α u G h

end Work.FTS.EllipticEst.Cores.AeStep2Aux
