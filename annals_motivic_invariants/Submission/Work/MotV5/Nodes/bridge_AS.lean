import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.tp_as
import Submission.Work.MotV5.base_preserved_AS
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.RigAS.bridge_twist
import Submission.Work.MotV5.RigAS.placeData_e1

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

/-- **Node BR_AS (the Artin–Schreier bridge)**, restricted to the two classes of the link after a
prover refused the unrestricted-`g` version.  For `g = fAS 𝕜 = t³ + t` or `g = 2 • fAS 𝕜`, at
every valuation `v` of the corrected twist field `F = asTwistFieldTrue D g τ σS` which is trivial
on `𝕜` and at which `t = RatFunc.X` has a pole (`1 < v t`; values in `ℤᵐ⁰`, `1 < ·` = a pole), the
class of `g` is *unramified*: `g ≡ u ^ 5 - u` modulo the valuation ring for some `u ∈ F`.

The restriction to the two classes is necessary (and sufficient for the branch): for general
`g ∈ K` the statement also forces the leading coefficients of `g` at the poles of `t` to be fifth
powers in the residue fields, which holds for `g ∈ {fAS, 2•fAS}` because their coefficients lie in
the prime field `𝔽₅` (`x⁵ = x` on `𝔽₅`).  The hypotheses are bundled in
`Work.MotV5.ASTwistData`: `τ` is the coefficient action of `σ` and fixes `K(E)`,
`σ (asRoot g) = asRoot g + 1`, `σS` is a genuine projective fifth-torsion shift, and `σ' = τ ∘ σS`
has order `5`, is nontrivial and preserves `L(E)`.

**The case distinction to settle first.**  Let `P` be a place of `F` over the pole `∞` of `t`,
`m := e(P/∞)`, and `Q` a place of `L(E) = F(W)` (`W = asRoot g`, `℘(W) = g`) over `P`.  Since
`L(E)/L` is a constant base change (unramified at `∞`) while `L/K = K(W)/K` is totally ramified of
degree `5` at `∞`, multiplicativity of ramification indices gives `m · e(Q/P) · #{places over P}
= 5`; so either (i) `m = 5`, `e(Q/P) = f(Q/P) = 1`, five places over `P`, or (ii) `m = 1`,
`e(Q/P) = 5`, one place over `P`.  In case (i) `v_P(g) = (v_P t)³` has pole order `15`, divisible
by `5`, and `W` lies in the completion `F_P` (the place splits); density of `F` in `F_P` and
`℘u - ℘u_P = (u - u_P)⁵ - (u - u_P)` in characteristic `5` then give `v (g - ℘u) ≤ 1`.  In case
(ii) the pole order is `3` and the statement is false.  The evidence for (i) is that
`Γ = ⟨σ'⟩` acts on the places of `L(E)` above `∞` through the translation by the fifth-torsion
point on the reduction `E`, and a nonzero translation of an elliptic curve has no fixed closed
point, so the decomposition group above `P` is trivial and `e = f = 1`.

**How it is proved (2026-10-05, `STATUS.md` §10).**  The local analysis (i)/(ii) above is settled in
favour of (i), and the argument is the *tower* `𝕜(t) ⊆ K(E) ⊆ L(E)` rather than a monogenic
computation at `P`.  The proved value-level node `Nodes/fifthPowAtPoles_AS` gives `5 ∣ e(P/∞)` for
`P` over the pole `∞` of `t`; the étaleness of the Klein translation quotient
(`RigAS/kleinQuotient_etale`) gives `e(R/P') = 5` for the place of `L(E)` over the place `P'` of
`K(E)`; multiplicativity then forces `e(P/∞) = 5`, `e(R/P) = 1`.  With `e = 1` the polar part of
`W` in the expansion at `P` is `σ'`-fixed, hence a series in a uniformiser of `P`, hence in `F_P`,
and the density of `F` in `F_P` produces `u ∈ F` with `v (g - ℘u) ≤ 1`.  This is exactly the
`IsPlaceData` input consumed by the proved `Work.MotV5.RigAS.bridge_twist_of_placeData`, with
`IsPlaceExtension` supplied by `RigAS/placeExtension_e1` and `IsResidueLift` by
`RigAS/residueLift_e1`; the assembly is `Work.MotV5.RigAS.placeData_e1`. -/
theorem bridge_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotV5.ASUnramified 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) :=
  -- The bridge, from the local place datum at every pole of `t`:
  -- `placeData_e1` supplies `IsPlaceData` (place extension with `e = 1` + trivial inertia) and
  -- `bridge_twist_of_placeData` performs the polar-part descent along `σ'`.
  Work.MotV5.RigAS.bridge_twist_of_placeData 𝕜 D hD g hg τ σS σ h
    (Work.MotV5.RigAS.placeData_e1 𝕜 D hD g hg τ σS σ h)

end Work.MotV5.Nodes
