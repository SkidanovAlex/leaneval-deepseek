/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds`

**The buildable twin of `Submission/Work/FTS_RegExport/RXR5L/aux/Tlim_bounds.lean`** (same
namespace `Work.FTS_RegExport.RXR5L.aux`, same declaration `Tlim_bounds`, same text of the proof).
The assigned file lies in a directory named `aux`, a module-name component Lean 4.34 refuses
*(before* elaboration) because `AUX` is a reserved file name on some OS
(`checkModuleNamePortability`, `Lean/Elab/Import.lean`): neither
`lake build Submission.Work.FTS_RegExport.RXR5L.aux.Tlim_bounds` nor
`import Submission.Work.FTS_RegExport.RXR5L.aux.Tlim_bounds` is possible, and no option disables
the check. This twin is the module to **import**.

## The statement

**The transport zero-mode of the strong-solution family**: the quantity
`L₁₂(3·D_θ(slice g τ)/(1+z))(0)` (`L₁₂^K` of the datum `F_g(z,θ) = 3·D_θ g(z,θ)/(1+z)`, the
transport term of `2αμ`) is

* uniformly bounded on the horizon `[0,S]`, and
* Lipschitz in the *fake time* `τ` with a constant `M` independent of `τ, τ' ∈ [0,S]`,

for every family `g` produced by the strong route (`DynOK'`).

## Proof

`D_θ = mixed 0 1` is the angular slot `(b,a) = (0,1)`, so the two standing estimates for
`LimApprox` families apply verbatim:

* `RXR5L.Auxiliary.Dth_slice_bounds`: a constant `C₁ ≥ 0` with
  `|D_θ(slice g τ) z θ| ≤ C₁·Rwt z` and
  `|D_θ(slice g τ) z θ - D_θ(slice g τ') z θ| ≤ C₁·Rwt z·|τ-τ'|` on `z > 0`, `θ ∈ Iθ`, where
  `Rwt z = z^{3/2}/(1+z)²`; it is `RXA2w.lim_mixed_weighted_proved` +
  `RXR5.Pieces.mixed_slice_tau_modulus` at that slot;
* `RXR5L.Auxiliary.abs_L12_zero_le_of_pointwise`: for *any* `f` with `|f z θ| ≤ M·Rwt z` on
  `(0,∞) × Iθ`, `|L₁₂ f (0)| ≤ 3·(π/2)·M·2` — no regularity of `f` is needed (both integrals of
  the definition are estimated by the pointwise mean inequality);
* `RXR5L.Auxiliary.L12_sub_of_bdd`: `L₁₂` is linear in its profile on continuous data dominated by
  a multiple of `Rwt·(1+·)⁻¹` (`L12_sub_of_integrable` with the four integrability certificates
  supplied by continuity on the open quadrant and the majorant).

The two claims then use the *same* constant `M = 3π·(3C₁)`: the first applies the mean inequality
to `3·D_θ(slice g τ)/(1+z)` itself, the second to the *difference*
`3·D_θ(slice g τ)/(1+z) - 3·D_θ(slice g τ')/(1+z)`, whose `L₁₂` is the difference of the two
`L₁₂`-values by the linearity clause. The assembly is
`RXR5L.Auxiliary.Tlim_bounds_from_aux`.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_sub_aux
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L.aux

theorem Tlim_bounds {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0| ≤ M) ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
          ≤ M * |τ - τ'|) :=
  Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds_from_aux (hOK := hOK)
    (hsub := Work.FTS_RegExport.RXR5L.Auxiliary.L12_sub_of_bdd_proved)
    (hbnd := Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds hα hα13 hOK.2 hS)

end Work.FTS_RegExport.RXR5L.aux
