import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.LocCantor.locCantor_of_D_BJ_dioph
import Submission.Work.TMComp.RedC7T.dbj_dioph_final
import Submission.Work.TMComp.C7Aux.Fresh.RTLv3

/-!
# C17 (`P_LocCantor`): localisation implies Cantor spectrum (AJ Thm 5.1)

The frozen statement is

`P_LocCantor`: for irrational `α` that is Diophantine with some constant `b₀`, coupling `λ ≥ 1`,
and a.e. Anderson localisation, the spectrum `Σ_{λ,α}` contains no nondegenerate interval.

## The argument (AJ §5, `Submission/Work/TMPlan/ROUTE_LEAD.md` §4)

Assume `J = (a,b) ⊆ Σ_{λ,α}`.

* Aubry duality (`P_Duality`, `prove_Duality`) puts `J/λ ⊆ Σ_{λ⁻¹,α}`.
* For a.e. phase `θ`, Schnol's theorem (`P_Schnol`, `prove_Schnol`) supplies a generalised
  eigenvalue `E ∈ J` of `H_{λ,α,θ}`; a.e. localisation (`hloc`) makes its eigenfunction
  exponentially decaying, and the Bloch-wave analysis (`LocCantor/Reducible.lean`,
  `bloch_reduction`) then puts `E/λ` in the reducible set `Λ_{λ⁻¹,α}` with the rotation-number
  identity `N_{λ⁻¹,α}(E/λ) = ±(2θ - 1)/2 + kα - j`.
* Hence the full-measure set of "good" phases is contained in a countable union of affine images
  of `N_{λ⁻¹,α}(Λ_{λ⁻¹,α} ∩ J/λ)`, which is null: `P_Reducibility` (Kotani's theorem, C11) makes
  `Λ ∩ J/λ` null and `P_Puig` (exclusion of Cantor spectrum, C12) rules out the degenerate
  alternative, while the analyticity of `N` on the spectral interval makes its image null.
* A full-measure set contained in a null set is a contradiction.

The assembly of that argument is `Work.TMComp.LocCantor.locCantor_of_components_dioph`
(the fork of the original `locCantor_of_components` with C9 and C11 restricted to Diophantine
frequencies, which is what `P_LocCantor`'s own hypothesis `DiophBelow α b₀` supplies).  It is
exposed as `Work.LocCantor.locCantor_of_D_BJ_dioph`, which rests on exactly one non-elementary
input: the **Diophantine case of Bourgain--Jitomirskaya**, `D_BJ_dioph`
(`L(E) = max 0 (log |λ|)` on the spectrum for `α` Diophantine).

## Where the Diophantine case comes from here

`Work.TMComp.RedC7T.D_BJ_dioph` assembles `D_BJ_dioph` from the three elementary components
(`prove_OpBasics`, `prove_LEBasics`, `prove_Schnol`) and a single input,

`RedC7T.RatTowerLower` — **S1** of the C7 design (`TMC7Core/C7_INPUTS_LEAD.md` §3): the finite
avalanche tower at a rational frequency, closed by the polynomial excess rate
`Scale.rat_excess_rate_explicit`.  That input is supplied below
(`my_RatTowerLower`) from `Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3`, whose proof is the
schedule argument of `C7Aux/rtlSchedule` together with the *finite* tower telescoping
`Work.TMComp.C7Aux.TowerV3.finite_tower_bound_v3`.

The original, component-based C17 assembly (with the full `P_BJ` in place of its Diophantine
case) is preserved verbatim in `Submission/Work/TMComp/LocCantor/C17_general_route.lean`.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

/-- **The finite rational tower (S1)**, as an instance of `RedC7T.RatTowerLower`.

This is the statement of S1 of `TMC7Core/C7_INPUTS_LEAD.md` §3: for a rational frequency,
a chain of approximants with slowly growing denominators, a frozen base scale `N₀` carrying the
level `200κ < L_{N₀}` and the pairing `(9/10)L_{N₀} < L_{2N₀}`, the two-scale defect is bounded
by `B e^{-cκQ₀/8}`.  See `Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3`. -/
theorem my_RatTowerLower : RedC7T.RatTowerLower := fun lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1 b hb =>
  Work.TMComp.C7Aux.TowerV3.rat_tower_lower_v3 lam K c C C₀ hLDT hLEB hc1 κ hκ hκ1 b hb

/-- **C17**: AJ Thm 5.1 — localisation (for a.e. phase) plus `DiophBelow` and `λ ≥ 1`
imply that the spectrum `Σ_{λ,α}` contains no interval. -/
theorem prove_LocCantor : Work.TMContract.P_LocCantor :=
  Work.LocCantor.locCantor_of_D_BJ_dioph (RedC7T.D_BJ_dioph my_RatTowerLower)

end Work.TMComp
