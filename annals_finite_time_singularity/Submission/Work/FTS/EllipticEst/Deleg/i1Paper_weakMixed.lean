/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg.i1Paper_weakMixed` — the paper-shaped `I₁` lower bound, weak mixed honesty

Target (byte-for-byte the requested statement): for the almost-everywhere class
`H2W.Ae.AeData` with `HkMem α 0 (grad u)`, the a.e. slicewise mixed honesty `(H1)` and the
unweighted outer finiteness `(H2)` of `V = z∂_z∂_θu`,

```
κ·α²·HkSq α 0 (∂_θ(grad u)) − C·α²·(⟨U,U⟩ + √⟨U,U⟩·√⟨B,B⟩) ≤ α²·⟨z²∂_zzu, B⟩
```

(`U = grad u = z∂_zu`, `B = ∂_θθu`, `κ = (1-η)/(1+η)`, `⟨f,g⟩ = AngSecond.IP f g`).

## Route

The cut-off chain of `Submission/Work/FTS/EllipticEst/AeColl/`:

* `Deleg.mixedCollarBound` — the 1-D collar bound `CollarBound Cw` (the `ψ_δ''`-moment of a
  slice `f` of `U` bounded by `Cw·K` times the two collar `σ`-energies of `f'`, using the
  endpoint rate);
* `Deleg.mixedTruncPairLe` — the per-`(χ_n, ψ_δ)` inequality `TruncPairLe Cw`
  (`κ·P_χψ ≤ D_χψ + Tr_χψ − 2η·A_χψ + Cw·K·Col_χδ`), from the proved 2-D cut-off identities
  `I1Wk.truncZIbp2` and `I1Wk.truncThetaIbpSep_split`;
* `Deleg.mixedPairLimit` — the `ψ_δ ↓ 0` limit at fixed `n` (`PairLimit Cw`);
* `mixedLimitBound` (below) — the `χ_n ↑ 1` limit, with the band term of
  `∂_z(χ_n w² z²)/z` controlled by `chiDerivLimit` and the Cauchy–Schwarz bound `IP_cw_le`
  on the transfer term;
* the final assembly (below), using `AeI1Fts.HkSq_pth_grad` and `I1Wk.aeGradTrace0` to produce
  the rate constant `K`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.SlotA.crossThetaIbp
import Submission.Work.FTS.EllipticEst.H2W.SlotA.I1_z_ibp_open
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedAux
import Submission.Work.FTS.EllipticEst.Deleg.mixedCollarBound
import Submission.Work.FTS.EllipticEst.Deleg.mixedTruncPairLe
import Submission.Work.FTS.EllipticEst.Deleg.mixedPairLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem i1Paper_weakMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  obtain ⟨Cw, hCw, hC⟩ := mixedCollarBound
  exact i1Paper_weakMixed_of ⟨Cw, hCw, hC⟩
    (fun Cw hCw hc => mixedTruncPairLe Cw hCw hc)
    (fun Cw hCw => mixedPairLimit Cw hCw)

end

end Work.FTS.EllipticEst.Deleg
