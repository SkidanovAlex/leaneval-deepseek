/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Dispatch/step3AeD` — Step 3 of `prop:H2` in the a.e. class `AeData` (the Dispatch node)

Target:

```
∃ C > 0, ∀ α u G, AeData α u G →
  nrm α (fun z θ => α² (z² ∂_zz u z θ)) ≤ C (nrm α G + α nrm α (z∂_z u) + nrm α (∂_θθ u) + nrm α u)
```

with `‖g‖_ρ = H2W.Ae.nrm α g = √(HkSq α 0 g)` and `AeData` the almost-everywhere class of
`H2W/Ae/Defs.lean` (`bslOp α u = G` on the open quadrant, the Dirichlet data as values, `C^∞`
on the open quadrant, `HkMem α 0` of `G`, `z²∂_zzu` and `∂_θθu`, and the two solvability
conditions `F_*u = F_*G = 0` for a.e. `z > 0`).

This is the paper's Step 3 of Proposition `prop:H2`: on the open quadrant the equation
`bslOp α u = G` rearranges to

  `α² z²∂_zz u = -G - α(5+α)(z∂_z u) - ∂_θθ u + ∂_θ(tan θ·u) - 6u`,

so `α²‖z²∂_zzu‖_ρ` is controlled by the five terms of the right-hand side once each of them is
*honest* (`HkMem α 0`) and once the `I₄`-estimate
`‖∂_θ(tan θ·u)‖_ρ ≤ C(‖u‖_ρ + ‖∂_θθu‖_ρ)` is available.  The three `HkMem` inputs `u`,
`z∂_zu`, `∂_θ(tan θ·u)` and the `I₄`-estimate are the only analytic content; the rest is the
five-term Cauchy–Schwarz domination of the level-`0` integrands, the honest integration step
and the square-root arithmetic.

## The Dispatch wiring (what this file consumes)

* `Dispatch.hkMem_uM` — `HkMem α 0 u` (the `u`-mass half of Step 1, Dispatch cone);
* `Dispatch.hkMem_gradUD` — `HkMem α 0 (z∂_zu)` (the radial half of Step 1, Dispatch cone);
* `H2W.Ae.hkMem_ang1` — `HkMem α 0 (∂_θ(tan θ·u))` from the two above (its cone avoids the
  currently unbuildable `TanTheta.slice_hypotheses`);
* `H2W.AngBW.S3.ang1_bound` — the `I₄`-estimate, with the same clean cone.

The arithmetic assembly `H2W.AngBW.S3.step3Ae_of_pieces` (a general reduction, proved on top
of the five-term Cauchy–Schwarz and the integration step) is instantiated with these four
inputs: `step3AeD_of_pieces` below is that instantiation interface, mirroring the pattern of
`Dispatch/step2AeD.lean`, and `step3AeD` is its instantiation with the available pieces.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AngBW.aeStep3
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

/-- **The reduction of Step 3 to its four inputs.**  From

* `hu` — `HkMem α 0 u`,
* `hd` — `HkMem α 0 (z∂_zu)`,
* `ha` — `HkMem α 0 (∂_θ(tan θ·u))`,
* `hb` — the `I₄`-estimate `‖∂_θ(tan θ·u)‖_ρ ≤ CU(‖u‖_ρ + ‖∂_θθu‖_ρ)`,

one obtains the target estimate with the explicit constant `√5 (11 + CU)`.  This is the
Dispatch-cone form of the assembly: the analytic inputs are exactly the four lemmas listed in
the module docstring. -/
theorem step3AeD_of_pieces (CU : ℝ) (hCU : 0 < CU)
    (hu : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u)
    (hd : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (ha : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
    (hb : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
        ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang2 u)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.FTS.EllipticEst.H2W.Ae.nrm α
            (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
            + Work.FTS.EllipticEst.H2W.Ae.nrm α u) :=
  Work.FTS.EllipticEst.H2W.AngBW.S3.step3Ae_of_pieces CU hCU hu hd ha hb

/-- **The `HkMem` honesty of `∂_θ(tan θ·u)` in the Dispatch cone**: from the honesty of `u` and
of `z∂_zu` (which are the two Dispatch inputs `Dispatch.hkMem_uM` and
`Dispatch.hkMem_gradUD`), the rearrangement of the equation and the five-term Cauchy–Schwarz
domination give `HkMem α 0 (ang1 u)`. -/
theorem hkMem_ang1D (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) :=
  Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 α u G h (hkMem_uM α u G h) (hkMem_gradUD α u G h)

/-- **The `I₄`-estimate in the Dispatch cone**: with the honesty inputs supplied by
`hkMem_uM`, `AeData.memAng2` and `hkMem_ang1D`, the `I₄`-estimate of `H2W.AngBW.S3.ang1_bound`
applies to every `AeData` datum. -/
theorem ang1_boundD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang2 u))) := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.EllipticEst.H2W.AngBW.S3.ang1_bound
  exact ⟨C, hC, fun α u G h => hCb α u (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h) (Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h)
    (hkMem_uM α u G h) (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 h) (hkMem_ang1D α u G h)⟩

theorem step3AeD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α u) := by
  obtain ⟨CU, hCU, hCUb⟩ := ang1_boundD
  refine step3AeD_of_pieces CU hCU
    (fun α u G h => hkMem_uM α u G h)
    (fun α u G h => hkMem_gradUD α u G h)
    (fun α u G h => hkMem_ang1D α u G h) ?_
  intro α u G h
  exact hCUb α u G h

end Work.FTS.EllipticEst.Dispatch
