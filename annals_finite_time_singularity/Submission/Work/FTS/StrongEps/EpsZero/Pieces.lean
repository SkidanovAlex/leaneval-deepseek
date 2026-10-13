/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsZero/Pieces.lean`

Vocabulary for the `L₁₂` zero-mode chapter of the `ε`-scheme (`Work.FTS.StrongEps.EpsZeroMode`):
the five summands of the pre-mollified right-hand side `epsWP` of the projected scheme, as
suggested by the paper's `gEquationFinal`

  `𝓛_Γ^T(g) = μ̄ (Γ/c) 2z²/(1+z)³ + N₀ + N + N_*`,

i.e. `dynLin = -𝓛_Γ^T f` and `dynRHS = gRHS = -μ̄·AK + N₀ + N + N_*`.

These are only *abbreviations* (all `rfl`-equal to the corresponding explicit expressions), so that
the statements of the auxiliary lemmas of this area can be written without repeating the arguments
`F = F_* + f`, `Φ = Φ_s + E f` a dozen times.

Everything here is `sorry`-free (it is pure vocabulary).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false

/-- The linear piece `-𝓛_Γ^T f` of the scheme's right-hand side. -/
abbrev PLin (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  fun z θ => -(Work.Coercivity.LGammaT α f z θ)

/-- The term `N₀` of the `g`-equation at the full profile `F = F_* + f` and the perturbation `f`. -/
abbrev PN0 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f

/-- The term `N` of the `g`-equation at `F = F_* + f` and the stream function `Ψ`. -/
abbrev PN (α : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ

/-- The term `N_*` of the `g`-equation. -/
abbrev PNs (μ lam : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.Nstar μ lam f

/-- The `μ̄`-term `-μ̄·AK α` of the `g`-equation, at the modulation constant `mbar`. -/
abbrev PK (mbar : ℝ) (α : ℝ) : Work.FTS.Galerkin.Fn :=
  fun z θ => -mbar * Work.Construction.AK α z θ

/-- The `mubar`-constant of the `g`-equation at `F = F_* + f` and the stream function `Ψ`. -/
abbrev Pmubar (α : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : ℝ :=
  Work.Construction.mubar (PN0 α f) (PN α f Ψ)

/-- The right-hand side `gRHS α μ lam (F_*+f) Ψ f` of the `g`-equation. -/
abbrev PgRHS (α μ lam : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.gRHS α μ lam (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ f

/-- The stream function of the scheme at the profile `f`: `Φ_s + E f`. -/
abbrev PPsi (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn)
    (Φs f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  fun z θ => Φs z θ + E f z θ

end Work.FTS.StrongEps.EpsZero
