import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.ToolsInstance
import Submission.Work.PL.Shell.Main
import Submission.Work.PL.SubdivFull.All
import Submission.Work.PL.Approx.All
import Submission.Work.Geo.Prism.Aliases

/-!
# `Submission/Work/EngulfForms`: discharging the four "Form" hypotheses of `Work.Engulf.engulf_of_forms`

Area A9 (`Submission/Work/Engulf`) proves

  `Work.Engulf.engulf_of_forms : (∀ N, SubdivShellForm N) → (∀ N, PlApproxFrozenForm (subdivTools ·) n) →
      (∀ N, SdFullForm (subdivTools ·)) → (∀ N, JoinPrismForm N) → EngulfForm n`

leaving four `Prop`-valued *forms* to be replaced by the real theorems of the areas that own them
(and the two E4-repair fields `plApproxAt`, `full` of `Tools`).  This area produces those
instances from the **delivered** areas:

* `Work.EngulfForms.shellForm`            — `SubdivShellForm N`, from A4 `Work.PL.Shell.shell_form`
  (which itself is `Work.PL.Shell.sd_iter_shelling_strong` plus the bridge from the single-simplex
  subdivision `Shell.shellOrd` to the complex-level subdivision `Work.PL.Subdiv.sdIter`);
* `Work.EngulfForms.plApproxFrozenForm`   — `PlApproxFrozenForm S n`, from A5
  `Work.PL.Approx.Frozen.pl_approx_frozen_faces` and the carrier lemma
  `Work.Engulf.exists_coarse_face_of_simp_subset` (A9) turning the *set* `L` into coarse faces;
* `Work.EngulfForms.plApproxFrozenAtForm` — `PlApproxFrozenAtForm S n` (the E4-repair form), from
  the same A5 result at an *input* level `r`;
* `Work.EngulfForms.sdFullForm`           — `SdFullForm S`, from `Work.PL.SubdivFull.sdIter_full`;
* `Work.EngulfForms.joinPrismForm`        — `JoinPrismForm N`, from A1
  `Work.Geo.Prism.join_simplex_prism` (an immediate weakening);
* `Work.EngulfForms.toolsAll`             — the assembled `Work.Engulf.ToolsAll n`, with **all**
  twelve fields, using `Work.Engulf.toolsAll`.

## What a caller imports

`import Submission.Work.EngulfForms.All`, then uses the names above.  The instances are stated
*exactly* as the fields of `Work.Engulf.Tools` (`Submission/Work/Engulf/Tools.lean`) and
`Work.Engulf.SubdivShellForm` (`Submission/Work/Engulf/ToolsInstance.lean`), so they slot into
`Work.Engulf.tools`/`Work.Engulf.toolsAll` with no further plumbing.
-/

open Set Metric PL
open Work.Engulf

namespace Work.EngulfForms

variable {N : ℕ}

/-! ## The prefix-union bridge

`Work.PL.Shell.preUnion ord i` (the union of the simplices of the first `i` members of `ord`) is
the union written in the Form with an explicit index and its bound.  The two presentations differ
only in that `preUnion` reads out of range entries as `∅`. -/

/-- The `i`-th member of a list, as a `Finset`, is `get`. -/
theorem getElem_eq_get {α : Type*} (l : List α) (i : ℕ) (h : i < l.length) :
    l[i] = l.get ⟨i, h⟩ := rfl

/-- `Work.PL.Shell.preUnion` written with an explicit bounded index. -/
theorem preUnion_eq_iUnion_get (ord : List (Finset (PL.E N))) (i : ℕ) :
    Work.PL.Shell.preUnion ord i =
      ⋃ j ∈ Finset.range i, ⋃ (_hj : j < ord.length), PL.simp (ord[j]) := by
  have hstep : ∀ j : ℕ, PL.simp (ord.getD j ∅) =
      ⋃ (_hj : j < ord.length), PL.simp (ord[j]) := by
    intro j
    by_cases hj : j < ord.length
    · rw [List.getD_eq_getElem ord ∅ hj]
      refine le_antisymm ?_ ?_
      · intro x hx
        exact Set.mem_iUnion.mpr ⟨hj, hx⟩
      · intro x hx
        obtain ⟨hj', hx'⟩ := Set.mem_iUnion.mp hx
        rwa [getElem_eq_get ord j hj'] at hx'
    · have hd : ord.getD j ∅ = (∅ : Finset (PL.E N)) :=
        List.getD_eq_default ord (∅ : Finset (PL.E N)) (n := j) (by omega)
      have hemp : (⋃ (_hj : j < ord.length), PL.simp (ord[j])) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
        obtain ⟨hj', -⟩ := Set.mem_iUnion.mp hx
        exact hj hj'
      rw [hd, PL.simp_empty, hemp]
  rw [Work.PL.Shell.preUnion]
  simp only [hstep]

end Work.EngulfForms
