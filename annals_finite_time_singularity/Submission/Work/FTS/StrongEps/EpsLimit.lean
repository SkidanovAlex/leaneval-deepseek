/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLimit.lean` — **E5**: the `ε`-limit of the scheme

The *vocabulary* of E5 (`rhsFun`, `EpsLimPkg`, `ExistsLimH`, `EllLimOK`, `MuLamOK`) lives in
`Submission/Work/FTS/StrongEps/EpsLimitDefs.lean`, so that the E5 chapters can be imported here.
This module carries the theorem **`exists_limH`** (E5), whose proof is the clause-by-clause
assembly of

* `E5Clauses` / `E5Clamp` — `init`, `vanish`, `c4`, `bd6`, `cont`, `bd4`, `mem4`;
* `E5Law` — `law`;
* `EpsLimVolterraP` + `EpsHlim` + `E5Mu` — `eqT`;
* `E5Aux.c1_of_locUnif_slots_lip` — `c1`;
* `EpsGdotThirdHP` — `dbd`;
* `E5LimApprox` — `limApprox`;
* the uniqueness clause.

**Status.**  `exists_limH` is the one remaining analytic input of the whole `ε`-route; the
chapters above are being landed one by one (`NOTES_session15.md` §3 has the clause table).

**Read `Submission/Work/FTS/StrongEps/notes/NOTES_session15.md` first.**
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsLimitDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false

/-- **E5 (ruling v2)**: `Cd` after `T`; the threshold `α₂` is that of `L3Data_exists`; the
hypotheses are the sources of every input of the `dbd` route (computed at the mollified slices
`J_ε g_ε ∈ ClassC`, where `Ell6Ctx`/`H6Adm`/`L3Data` apply, then lower semicontinuity). -/
theorem exists_limH : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK α E → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K → ExistsLimH α C₀ K Φs E g₀ := by
  sorry

end Work.FTS.StrongEps
