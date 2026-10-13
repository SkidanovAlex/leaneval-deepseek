import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.step1Ae
import Submission.Work.FTS.EllipticEst.Cores.step2Ae_fts
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI4_open
import Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.i1Paper_weakMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Dispatch/step2AeD` — Step 2 of `prop:H2` in the a.e. class `AeData` (the Dispatch node)

Target:

```
∃ C > 0, ∀ α u G, AeData α u G →
  nrm α (ang2 u) ≤ C * (nrm α G + α * nrm α (grad u))
```

i.e. `‖∂_θθu‖_ρ ≤ C (‖G‖_ρ + α ‖z∂_zu‖_ρ)` with `‖g‖_ρ = H2W.Ae.nrm α g = √(HkSq α 0 g)`,
`AeData` the almost-everywhere class of `H2W/Ae/Defs.lean` (`bslOp α u = G` on the open
quadrant, the Dirichlet data as values, `C^∞` on the open quadrant, `HkMem α 0` of `G`,
`z²∂_zzu` and `∂_θθu`, and the two solvability conditions `F_*u = F_*G = 0` only for a.e.
`z > 0`).

## The assembly

This file is the *assembly*; the analytic content lives in the sibling nodes it imports.  The
assembly used is `Cores.step2Ae_core` (`Cores/step2Ae_fts.lean`, **proved**): pairing the
equation against `∂_θθu` in the weight `ρ = w²σ` — the identity
`AngAWeak.I_identity_weak` (**proved**) —

  `α²⟨Q,B⟩ + α(5+α)⟨U,B⟩ + ⟨B,B⟩ − ⟨∂_θ(tan θ·u),B⟩ + 6⟨u,B⟩ = −⟨G,B⟩`

with `B = ∂_θθu`, `Q = z²∂_zzu`, `U = z∂_zu`, `⟨f,g⟩ = AngSecond.IP f g`, then Cauchy–Schwarz
and the quadratic solve.  Its five inputs are

1. `HkMem α 0 u` — `Cores.AeStep2Aux.aeUHk_mem` (**proved**);
2. `HkMem α 0 (z∂_zu)` from `HkMem α 0 u` — `AngAWeak.hkMem_grad_of` (**proved**, the radial
   Agmon–Nirenberg interpolation `Dispatch.hkMem_gradUD`);
3. `‖u‖_ρ ≤ C‖G‖_ρ` — `Cores.AeStep2Aux.aeUHk_bnd` (**proved**, the paper's `w²`-energy
   identity, the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` and the `σ`-upgrade);
4. the `I₄`-open bound `⟨∂_θ(tan θ·u),B⟩ ≤ ⟨u,B⟩ + C⟨u,u⟩` — `Cores.AeStep2Aux.aeI4_open`
   (**proved**, `H2W.I4Open` in the `AeData` class).  Note that this *open* form deliberately
   avoids the `‖u/cos θ‖_ρ` shape of `AngAWeak.AeI4`: that shape needs the `Ψ̄ = u/cos θ`
   first-order estimate, which in this tree is obtainable only from the strong form of Step 2
   itself (a cycle);
5. the **`I₁` coercivity** `AngAWeak.AeI1`
   (`−C α²(⟨U,U⟩ + √⟨U,U⟩·√⟨B,B⟩) ≤ α²⟨Q,B⟩`) — the one genuinely open input, recorded here as
   `step2AeI1_holds`.  It is supplied by either of

   * the *bare* form (`AngAWeak.AeI1`) once a prover lands it, or
   * the *paper-shaped* form `remov.AeI1Paper` — which keeps the positive term
     `((1-η)/(1+η))·α²‖∂_θ(z∂_zu)‖²_ρ` produced by the sharp same-weight Hardy inequality and
     carries `⟨U,U⟩`-errors — via the bridge `aeI1_of_paper` below (the positive term is
     nonnegative, so it may be dropped).

The point of keeping the bridge is that both shapes of the coercivity close the same target.
-/

namespace Work.FTS.EllipticEst.Dispatch

open Work.FTS.EllipticEst

/-- **The paper-shaped `I₁` bound implies the bare one** (`remov.AeI1Paper → AngAWeak.AeI1`):
the positive term `((1-η)/(1+η))·α²·‖∂_θ(z∂_zu)‖²_ρ` is nonnegative (`0 < η < 1`, `α² ≥ 0`,
`HkSq ≥ 0`), so it may be dropped. -/
theorem aeI1_of_paper (h : Work.FTS.EllipticEst.remov.AeI1Paper) :
    Work.FTS.EllipticEst.AngAWeak.AeI1 := by
  obtain ⟨C, hC, h'⟩ := h
  refine ⟨C, hC, ?_⟩
  intro α u G hA hU
  have hmain := h' α u G hA hU
  have hpp : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (α ^ 2 * Work.Spaces.HkSq α 0
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))) := by
    refine mul_nonneg (div_nonneg (by linarith [Work.Spaces.eta_lt_one]) (by
      linarith [Work.Spaces.eta_nonneg])) ?_
    exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg α 0 _)
  change -C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
        (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
      + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
    ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
  linarith [hmain, hpp]

/-- **The `I₁` coercivity of Step 2 in the class `AeData`.**

The paper's `I₁` computation (the two radial integrations by parts, the angular integration by
parts of the cross term, the sharp `cos²`-weighted Hardy inequality and Cauchy–Schwarz; the
compact case is `Dispatch.aeI1ChainCompact`, proved) is available in the tree in its *honest*
form `Cores.AeStep2Aux.i1Paper_weakMixed`, which carries the mixed honesty
`HkMem α 0 (z ∂_z∂_θ u)` — equivalently `HkSq α 0 (∂_θ(z ∂_z u)) < ∞` — as an explicit
hypothesis.  That hypothesis is *not* free in the class `AeData`; it is however **derivable**:
`Cores.AeStep2Aux.aeMixedAe_mem` produces exactly the two a.e./integrated integrability clauses
of `(z ∂_z∂_θu)²·σ` for every `AeData` datum.

So this theorem is the honest assembly: feed the two clauses of `aeMixedAe_mem` into
`i1Paper_weakMixed` and drop the nonnegative positive term
`((1-η)/(1+η))·α²·HkSq α 0 (∂_θ(z∂_zu))` — exactly the arithmetic of the proved
`aeI1_of_paper` above.  The only remaining inputs of the whole node are therefore the two
`Cores/AeStep2Aux` lemmas, and not this file. -/
theorem step2AeI1_holds : Work.FTS.EllipticEst.AngAWeak.AeI1 := by
  obtain ⟨C, hC, hI1⟩ := Work.FTS.EllipticEst.Cores.AeStep2Aux.i1Paper_weakMixed
  refine ⟨C, hC, ?_⟩
  intro α u G hA hU
  obtain ⟨hsl, hint⟩ := Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem α u G hA hU
  have hmain := hI1 α u G hA hU hsl hint
  have hpp : 0 ≤ ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
      * (α ^ 2 * Work.Spaces.HkSq α 0
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))) := by
    refine mul_nonneg (div_nonneg (by linarith [Work.Spaces.eta_lt_one]) (by
      linarith [Work.Spaces.eta_nonneg])) ?_
    exact mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg α 0 _)
  change -C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
        (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
      + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
    ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
  linarith [hmain, hpp]

theorem step2AeD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) :=
  Work.FTS.EllipticEst.Cores.step2Ae_core
    (fun α u G h => Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem α u G h)
    (fun α u G h _ => Work.FTS.EllipticEst.AngAWeak.hkMem_grad_of h)
    Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
    step2AeI1_holds
    Work.FTS.EllipticEst.Cores.AeStep2Aux.aeI4_open

end Work.FTS.EllipticEst.Dispatch
