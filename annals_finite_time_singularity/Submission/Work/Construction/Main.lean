/-
# The CONSTRUCTION area of the Elgindi finite-time-singularity project: entry point

Import this single module to get the whole `Submission/Work/Construction/` chapter — §Modulation
of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

(`Papers/elgindi/Classical_Euler_arXiv_2.tex`, tex lines 1317--1578):

* `Work.Construction.*` in `Defs.lean` — the self-similar ansatz, the stationary equations, the
  profile `F_*`, the singular part `Θ`, the nonlinear terms `N₀, N, N_*`, the modulation
  constants `μ, λ, μ̄`, the `g`-equation `IsGSol` and the fake-time equation `IsTimeGSol`;
* `Basic.lean`, `L12_Fstar_eq.lean`, `GammaN0.lean` — the calculus of `F_*`, `Θ` and `Γ`
  (`L₁₂(F_*) = 2α/(1+z)`, `F_* + z∂_zF_* - (1/α)L₁₂(F_*)F_* = 0`, the `Γ`-identity and the
  collapse of the first two summands of `N₀`);
* `Equation.lean` — the derivation of the `g`-equation `\eqref{gEquationFinal}`
  (`UVR_sub`, `MainLHS_explicit`, `MainLHS_eq_N`, `intermediate_geqn`, `gEquationFinal`);
* `Terms.lean` — the individual summands of `N₀, N, N_*` and their sum identities;
* `Apriori.lean` — the a-priori estimate: `N0Estimate`, `NEstimate`, `NstarEstimate`,
  `innerproductestimate`, `apriori_corollary`, from the per-summand input structures
  `N0Inputs`, `NInputs`, `NstarInputs`;
* `gronwall_exp_bound.lean`, `le_of_deriv_le_of_cubic.lean` — the two scalar comparison lemmas;
* `hasDerivAt_zvar.lean`, `hasDerivAt_OmegaAns.lean` — the chain rule for the self-similar
  ansatz (`∂_t` of the self-similar variable and of `Ω`);
* `Ansatz.lean` — `vorticity_reduces`: the self-similar vorticity equation for the ansatz
  reduces to the stationary equation `StatEqF` (tex 1330-1332);
* `H4N_GammaTerm_le.lean` — the `ℋ⁴`-bound of the explicit function of the `Γ`-identity
  (`|8α²c2m(θ)z²Γ/(c(1+z)⁴)|_{ℋ⁴} ≤ Cα²`, the remaining content of the input `N0Inputs.h12`);
* `FixedPoint.lean` — the fake-time argument: `EnergyIneq`, `TimeDerivIneq`,
  `uniform_bound_of_energy`, `timeDeriv_decay`, the compactness input `CompactnessInput` and
  the existence theorem `stationary_exists`.

See `NOTES.md` in this directory for the exact interfaces, the residual inputs and the three
places where the LaTeX source's displays differ from the definitions (and how they are
resolved here).
-/
import Mathlib.Tactic.MinImports
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Construction.GammaN0
import Submission.Work.Construction.Equation
import Submission.Work.Construction.Terms
import Submission.Work.Construction.Apriori
import Submission.Work.Construction.gronwall_exp_bound
import Submission.Work.Construction.le_of_deriv_le_of_cubic
import Submission.Work.Construction.FixedPoint
import Submission.Work.Construction.Ansatz
import Submission.Work.Construction.hasDerivAt_zvar
import Submission.Work.Construction.hasDerivAt_OmegaAns
import Submission.Work.Construction.H4N_GammaTerm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
