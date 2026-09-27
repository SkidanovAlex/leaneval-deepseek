import Submission.Work.EngulfForms.Prelude
import Submission.Work.EngulfForms.Shell
import Submission.Work.EngulfForms.SdFull
import Submission.Work.EngulfForms.JoinPrism
import Submission.Work.EngulfForms.Approx
import Submission.Work.EngulfForms.Approx.plApproxFrozenForm

/-!
# `Submission/Work/EngulfForms`: the four forms, and `Tools` with all fields filled

The four `Prop`-valued forms that `Work.Engulf.engulf_of_forms` takes as hypotheses, plus the two
E4-repair fields `plApproxAt`/`full` of `Work.Engulf.Tools`, are proved from the delivered areas:

* `shellForm N : SubdivShellForm N`                         — A4 (`Work.PL.Shell.shell_form`);
* `plApproxFrozenForm (S : SubdivTools N) : PlApproxFrozenForm S n` — A5
  (`Work.PL.Approx.Frozen.pl_approx_frozen_faces` plus the A9 carrier lemma);
* `plApproxFrozenAtForm (S : SubdivTools N) : PlApproxFrozenAtForm S n` — A5, at a prescribed level;
* `sdFullForm (shell : SubdivShellForm N) : SdFullForm (subdivTools shell)` — A2
  (`Work.PL.SubdivFull.sdIter_full`);
* `joinPrismForm N : JoinPrismForm N`                       — A1
  (`Work.Geo.Prism.join_simplex_prism`).

Consequently `Work.Engulf.Tools N n` is inhabited **unconditionally**:

* `Work.EngulfForms.tools (N n) : Work.Engulf.Tools N n`;
* `Work.EngulfForms.toolsAll (n) : Work.Engulf.ToolsAll n`.

The remaining gap between `Work.Engulf.ToolsAll n` and Newman's engulfing theorem
`Work.Cells.Connell.EngulfForm n` is entirely inside area A9 (the E4/E5 repair: the chain
`Work.Engulf.engulf : ToolsAll n → EngulfForm n` of `Submission/Work/Engulf/All.lean`); once that
builds, the final step is the term
`Work.Engulf.engulf n (Work.EngulfForms.toolsAll n)`.
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

universe u

/-- **A5**: frozen PL approximation with the level produced by the mesh argument, frozen on the
faces of the coarse complex `K` that lie in the union of faces `L` (same statement as
`Work.EngulfForms.Approx.plApproxFrozenForm`, exported under the area's uniform naming). -/
theorem plApproxFrozenForm {N n : ℕ} (S : SubdivTools N) : PlApproxFrozenForm S n :=
  Approx.plApproxFrozenForm S

/-- The shelling form for every ambient dimension. -/
theorem shellForm_all : ∀ N : ℕ, SubdivShellForm N := shellForm

/-- The frozen PL-approximation form (level produced by the mesh argument), for every ambient
dimension.  Its type is exactly the second hypothesis of `Work.Engulf.engulf_of_forms`. -/
theorem plApproxFrozenForm_all (n : ℕ) :
    ∀ N : ℕ, PlApproxFrozenForm (subdivTools (shellForm N)) n :=
  fun N => Approx.plApproxFrozenForm (subdivTools (shellForm N))

/-- The fullness form (E4 repair), for every ambient dimension. -/
theorem sdFullForm_all : ∀ N : ℕ, SdFullForm (subdivTools (shellForm N)) :=
  fun N => sdFullForm (shellForm N)

/-- The join-prism form, for every ambient dimension. -/
theorem joinPrismForm_all : ∀ N : ℕ, JoinPrismForm N := joinPrismForm

/-- **All twelve fields of `Work.Engulf.Tools`, with no hypotheses left.** -/
noncomputable def tools (N n : ℕ) : Work.Engulf.Tools N n :=
  Work.Engulf.tools (shellForm N) (Approx.plApproxFrozenForm (subdivTools (shellForm N)))
    (sdFullForm (shellForm N)) (joinPrismForm N)

/-- **All twelve fields of `Work.Engulf.Tools`, uniformly in the ambient dimension.** -/
noncomputable def toolsAll (n : ℕ) : Work.Engulf.ToolsAll.{u} n :=
  fun N => tools N n

/-- **The bundle for an arbitrary shelling family.**  If the Engulf owner supplies their own
`SubdivShellForm` for every `N` (rather than using `Work.EngulfForms.shellForm`), the other three
forms still fill every field of `Tools`. -/
noncomputable def toolsAll_of_shell (shell : ∀ N : ℕ, SubdivShellForm N) (n : ℕ) :
    Work.Engulf.ToolsAll.{u} n :=
  fun N => Work.Engulf.tools (shell N) (Approx.plApproxFrozenForm (subdivTools (shell N)))
    (sdFullForm (shell N)) (joinPrismForm N)

/-- `Work.EngulfForms.toolsAll_instance`: the bundle under the name the Engulf owner wires in. -/
noncomputable def toolsAll_instance (n : ℕ) : Work.Engulf.ToolsAll.{u} n := toolsAll n

/-- `Work.EngulfForms.tools_instance`: the bundle at a fixed ambient dimension. -/
noncomputable def tools_instance (N n : ℕ) : Work.Engulf.Tools N n := tools N n

/-- `toolsAll` evaluated at `N` is `tools N n` (definitional). -/
theorem toolsAll_apply (n N : ℕ) : toolsAll.{u} n N = tools N n := rfl

/-- The `subdiv` field of `toolsAll n` is `Work.Engulf.subdivTools` of the shelling form. -/
theorem toolsAll_subdiv (n N : ℕ) :
    (toolsAll.{u} n N).subdiv = subdivTools (shellForm N) := rfl

end Work.EngulfForms
