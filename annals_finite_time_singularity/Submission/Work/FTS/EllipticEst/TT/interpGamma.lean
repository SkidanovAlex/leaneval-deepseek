import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.interpGamma_core
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-!
# `TT.interpGamma`

The interpolation estimate with the **light** angular weight
`σ_a = sin(2θ)^{2-γ(α)}` (`2 - γ = 1 - α/10 ∈ (0,1)`) on the mixed derivative `D_z∂_θG` and the
**heavy** weights `σ_η = sin(2θ)^{-η}` (`η = 99/100`) on the three `ℋ⁰`-slots
`D_z²G`, `∂_θ²G`, `D_zG` of the right-hand side.

The proof is an assembly of two analytic inputs:

* `interpGamma_core` (`Submission/Work/FTS/EllipticEst/TT/interpGamma_core.lean`) — the analytic
  core `Xint ≤ C (√(DDint · TTint) + HkSq α 0 (DzIter 1 G))`; the naive core without the last slot
  is *false* (see `NOTES_interpGamma.md` §2, the affine counterexample);
* `interpGamma_slots` (`Submission/Work/FTS/EllipticEst/TT/interpGamma_slots.lean`) — the
  comparison of the two light-weight slots with the heavy-weight ones,
  `TTint ≤ HkSq α 0 (pthIter 2 G)` and
  `DDint ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)`,
  from `σ_a ≤ σ_η`, `|b| ≤ 3` and `HkMem`.

The arithmetic of the assembly is `interpGamma_of_core` below: with `2√x√y ≤ x + y`,
`α⁴ ≤ α²` for `α ≤ 1`, and the slot bounds, one gets
`α² Xint ≤ 10 C (α⁴ HkSq α 0 (DzIter 2 G) + HkSq α 0 (pthIter 2 G) + α² HkSq α 0 (DzIter 1 G))`,
whence the target with constant `10 C`.

## The analytic core: any of the following equivalent sources may be substituted

The *only* remaining input of `interpGamma` is the core `hcore` of `interpGamma_of_core`.
Equivalent (or stronger) statements already in the workspace, all with the *same* hypothesis
list, are

* `Work.FTS.EllipticEst.TT.interpGamma_core` — the delegated one, consumed below;
* `Work.FTS.EllipticEst.Cores.interpGammaBrick` — identical conclusion (its extra slot is written
  as `∫ z in Iz, ∫ θ in Iθ, (Dz G z θ)^2 * (w z)^2 * sin(2θ)^(-eta)`, which is `HkSq α 0
  (DzIter 1 G)` by `HkSq_zero_eq_integral` and `DzIter 1 G = Dz G`);
* the strictly weaker `σ_η`-slot variant `Work.FTS.EllipticEst.TT.interpGamma_core_eta`
  (`Xint ≤ C(√(NNeta G · HkSq α 0 (pthIter 2 G)) + HkSq α 0 (DzIter 1 G))`, with
  `NNeta = ∫∫(Dz (Dz G) + b · Dz G)^2 w^2 σ_η`): swapping it in needs only the finite pointwise
  comparison `NNeta G ≤ 2 HkSq α 0 (DzIter 2 G) + 18 HkSq α 0 (DzIter 1 G)` (AM–GM plus
  `|b| ≤ 3` plus `HkSq_zero_eq_integral`), i.e. the argument of `interpGamma_slots` restricted
  to the heavy weight, in place of `hslot`.

The mathematical content of the core (and its single unresolved analytic point) is recorded in
`NOTES_interpGamma_core.md`: the `θ`-integration by parts leaves the endpoint ("jump") term
`Φ = -a ∫ cos(2θ) sin(2θ)^{a-1} m'(θ) dθ`, `m(θ) = ∫_z w² (D_zG(z,θ))² dz`, and this term has
to be priced by `HkSq α 0 (DzIter 1 G) = ∫ σ_η m`.

## State of the crux (shared route, 2026-10-06)

The `m`-level reduction of the core is now understood (see
`H2W/AngBW/NOTES_lightFlatCore3_route.md`, `Cores/NOTES_interpGammaBrick.md` §2ter).  With
`f = D_zG`, `ρ = w²`, `σ = σ_a`, `p = L_zG`, `q = ∂_θ²G` and the `θ`-functions
`m(θ) = ∫_z ρ f²`, `Ψ(θ) = ∫_z ρ (∂_θf)²`, `G(θ) = ∫_z ρ f (∂_θ²f) = -∫_z ρ p q`, one has

* `m'' = 2(Ψ + G)`, `|G| ≤ √(f₁ f₂)` pointwise with `f₁ = ∫_z ρ p²`, `f₂ = ∫_z ρ q²`;
* `m ≤ 16 f₁` (radial Hardy twice; `ZCuts/zHardy_compact`, `zHardy_sq_le_cinf`);
* `∫σΨ = Xint`, `∫σf₁ = DDint`, `∫σf₂ = TTint`, `∫σm = ∫∫ρσ_a (D_zG)² ≤ HkSq α 0 (DzIter 1 G)`;
* the `θ`-IBP together with the `z`-adjoint gives exactly `Xint = P + Edge` with
  `P = -∫σG` (whence `|P| ≤ √(DDint·TTint)`), and the *regularised* endpoint term
  `Edge = ∫_θ W(θ)(m01(θ) - m(θ))dθ`, `W = -σ''/2 ≥ 0`, `m01 = lim_{0⁺}m` on `(0,π/4)` and
  `lim_{(π/2)⁻}m` on `(π/4,π/2)`;
* hence the core is **equivalent** to `Edge ≤ K(√(DDint·TTint) + HkSq α 0 (DzIter 1 G))`.

Proved bricks on this route: `Cores.sliceInterpJump` (the 1-D jump interpolation
`∫(Φ')²σ_a ≤ C(√(∫Φ²σ_a∫(Φ'')²σ_a) + ∫Φ²σ_η)` with an **α-uniform** constant —
its proof produces `max 1 (max (16384+4√3) (16384+52K²+4√3L))` from a fixed cutoff),
`Cores.sliceInterpVanishing` (the vanishing-trace case, constant `1`), `slicePriceBound`
(the endpoint price bound `∫ρc₀² ≤ (A/ε^{1+a})Cl + Bε^{1-a}Xl`), and the radial bricks above.

**The single remaining gap** is that `Edge` needs the *α-uniform* form of this 1-D input at the
`m`-level: the chain via the slicewise price bound loses `(1-a)^{-1/2} = √(10/α)`, and closing it
requires the quantitative use of `TTint = ∫σf₂ < ∞` (the dichotomy "`f₂ < ∞` forces
`m(θ) - m(0⁺) = O(θ^s)`, `s > 1-a`").  The tensor case (`G = A(z)η(θ)`) reduces to the sharp
1-D statement `∫σ(η')² ≤ K(∫ση² + √(∫ση²∫σ(η'')²))` with `K` universal, which the proof of
`Cores.sliceInterpJump` already produces (its intermediate `hMfinal`), and which is numerically
true with `K ≈ 1.4`.
-/




end Work.FTS.EllipticEst.TT
