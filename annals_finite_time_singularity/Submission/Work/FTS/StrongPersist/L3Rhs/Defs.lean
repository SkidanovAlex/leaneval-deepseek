/-
# `Work.FTS.StrongPersist.L3Rhs.Defs` — the block decomposition of the right-hand side

The target `Work.FTS.StrongPersist.L3RhsPriced` bounds the `ℋ³`-norm of the nonlinear
right-hand side

  `rhsOf α μ lam (Ftot α f) Φ f = gRHS α μ lam (F_* + f) Φ f`
    `= -mubar(N₀, N)·AK α + N₀ α (F_*+f) f + N α (F_*+f) Φ + Nstar μ lam f`

of the modulated `g`-equation (`Work.Construction.gRHS`), for data satisfying
`H6Adm α f` and the split elliptic context `Ell6Ctx α Ce Cs E Φs f Φ` (which provides the
star package `StarPkgo2 α Cs Φs`, the perturbation package `EllPkgK α 6 Ce f (E f)` and the
decomposition `Φ = Φs + E f`).

This module only *names* the blocks into which the summands `N₀`, `N` are split (following
`Work.FTS.Nonlin`, whose `N0fix, N03g, …, N06F` and `N1gg, …, N5ss` are the paper's rows), so
that each block can be estimated independently.  Nothing here is a proof obligation; the blocks
are `def`s.

The split of `N` is the one of `Work.FTS.Nonlin`:

* `N_i = N_i^{gg} + N_i^{gs} + N_i^{sg} + N_i^{ss}`, the first index recording which elliptic
  residual (`Φ̃_g` for `G`, `Φ̃_*` for `S`) and the second which profile (`f` for `g`, `F_*` for
  `s`) occurs;
* `N₄`, `N₅` carry the angular moment `FK F = FK F_* + FK f` and split accordingly.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (N0fix N03g N04aF N04bF N05aF N05bF N06F
  N1gg N1gs N1sg N1ss N2gg N2gs N2sg N2ss N3gg N3gs N3sg N3ss
  N4gg N4gs N4sg N4ss N5gg N5gs N5sg N5ss MuAK)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The blocks of `N₀` -/

/-- The `g`-dependent block of `N₀`: rows 2--7 of the paper's table, at the profile `F = F_*+f`. -/
def N0gSum (α : ℝ) (f : Fn) : Fn := fun z θ =>
  N03g α f z θ + N04aF α f z θ + N04bF α f z θ
    + N05aF α f z θ + N05bF α f z θ + N06F α f z θ

/-! ## The blocks of `N` -/

/-- The pure-star block of `N`: `N₁^{ss} + N₂^{ss} + N₃^{ss} + N₄^{ss} + N₅^{ss}`
(the terms in which the elliptic residual and the transported profile are both the star ones).
`N₄^{ss}`, `N₅^{ss}` depend on `α` only. -/
def NSsSum (α : ℝ) (Φs : Fn) : Fn := fun z θ =>
  N1ss α Φs z θ + N2ss α Φs z θ + N3ss α Φs z θ + N4ss α z θ + N5ss α z θ

/-- The block of `N` in which the *star* elliptic residual is transported by the modulation:
`N₁^{sg} + N₂^{sg} + N₃^{sg}`. -/
def NSgSum (α : ℝ) (Φs f : Fn) : Fn := fun z θ =>
  N1sg α Φs f z θ + N2sg α Φs f z θ + N3sg α Φs f z θ

/-- The block of `N` in which the *perturbation* elliptic residual multiplies `F_*`:
`N₁^{gs} + N₂^{gs} + N₃^{gs}`. -/
def NGsSum (α : ℝ) (f Φg : Fn) : Fn := fun z θ =>
  N1gs α f Φg z θ + N2gs α f Φg z θ + N3gs α f Φg z θ

/-- The block of `N` in which the *perturbation* elliptic residual is transported by the
modulation: `N₁^{gg} + N₂^{gg} + N₃^{gg}`. -/
def NGgSum (α : ℝ) (f Φg : Fn) : Fn := fun z θ =>
  N1gg α f Φg z θ + N2gg α f Φg z θ + N3gg α f Φg z θ

/-- The angular-moment block of `N`: the six terms in which the factor `FK F = FK F_* + FK f`
occurs (`N₄^{gg}, N₅^{gg}, N₄^{gs}, N₅^{gs}, N₄^{sg}, N₅^{sg}`). -/
def NFkSum (α : ℝ) (f : Fn) : Fn := fun z θ =>
  N4gg α f z θ + N5gg f z θ + N4gs α f z θ + N5gs α f z θ + N4sg α f z θ + N5sg α f z θ

/-- The `μ̄·AK` term of the right-hand side, with `Φ = Φs + Φg`. -/
def MuAKTerm (α : ℝ) (Φs Φg : Fn) (f : Fn) : Fn :=
  MuAK α f Φs Φg

end Work.FTS.StrongPersist.L3Rhs
