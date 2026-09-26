import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Homotopy
import Submission.Work.InnermostDisk.isEssential_iff_hasWinding
import Submission.Work.InnermostDisk.homotopic_iff_homotopicClosed
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# Essentiality is an invariant of the homotopy class

`Work.CoreTopology.IsEssential P γ` says that the closed curve `γ` of the surface
`F = P.carrier` of the parametrised torus `P` has nonzero winding vector, i.e. that it is not
null-homotopic in `F`.  Being a homotopy invariant, it only depends on the homotopy class of
`γ` through closed curves of `F`, which is the content of

`Work.InnermostDisk.isEssential_iff_of_homotopic`:
if `α` and `β` are homotopic through closed curves of `F`, then `α` is essential if and only
if `β` is.

The work is done by the winding vector.  A closed curve of `F` lifts to the parameter plane
(`Work.TorusCover.ParamTorus_exists_liftOf`), the winding vector read off from any lift is
independent of the lift (`Work.CoreTopology.LiftOf.winding_eq`), and homotopic closed curves
have the same winding vector
(`Work.SurgeryInvariance.WindingOf.hasWinding_eq_of_homotopicClosed_param`, the `ParamTorus`
version of `Work.TorusCover.HomotopicClosed.hasWinding_eq`): the homotopy lifts through the
covering map `Work.TorusCover.isCoveringMap_psiMapToRange_param`, and the displacement of the
lifted homotopy over one period is a continuous lattice-valued function of the homotopy
parameter, hence constant.  Since `Work.InnermostDisk.homotopic_iff_homotopicClosed`
identifies the two encodings of "homotopy of closed curves of `F`", the criterion transfers
verbatim.

A homotopy is symmetric (`Work.InnermostDisk.homotopic_symm`), so it is enough to prove that
homotopy carries essential curves to essential curves.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- **Homotopy of closed curves of `F` is symmetric.**  If `H` joins `α` to `β` through closed
curves of `F`, then the reversed family `(s, t) ↦ H (1 - s) t` joins `β` to `α` through closed
curves of `F`. -/
theorem homotopic_symm {P : ParamTorus} {α β : ClosedCurve P} (h : Homotopic P α β) :
    Homotopic P β α := by
  obtain ⟨H, hcont, hmem, h0, h1, hper⟩ := h
  refine ⟨fun s t => H (1 - s) t, ?_, fun s t => hmem (1 - s) t, fun t => ?_, fun t => ?_,
    fun s t => hper (1 - s) t⟩
  · have : Function.uncurry (fun s t : ℝ => H (1 - s) t)
        = fun p : ℝ × ℝ => Function.uncurry H (1 - p.1, p.2) := rfl
    rw [this]
    exact hcont.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  · simpa using h1 t
  · simpa using h0 t

/-- **Homotopy carries essential closed curves to essential closed curves.**

Let `α`, `β` be homotopic closed curves of `F = P.carrier` and let `L` be a lift of `α` with
nonzero winding vector.  Lifting the homotopy through the covering `ℝ² → F` produces a lift of
`β` whose period displacement is the same `periodShift L.winding`; by the homotopy invariance of
the winding vector (`Work.SurgeryInvariance.WindingOf.hasWinding_eq_of_homotopicClosed_param`)
any lift of `β` therefore has winding vector `L.winding ≠ 0` as well, so `β` is essential. -/
theorem isEssential_of_homotopic_of_isEssential {P : ParamTorus} {α β : ClosedCurve P}
    (h : Homotopic P α β) (hα : IsEssential P α) : IsEssential P β := by
  obtain ⟨Lα, hLα⟩ := hα
  obtain ⟨Lβ⟩ := Work.TorusCover.ParamTorus_exists_liftOf P β
  have hclosed : Work.TorusCover.HomotopicClosed P.psi α.γ β.γ :=
    (homotopic_iff_homotopicClosed P α β).mp h
  have hEq : Lα.winding = Lβ.winding :=
    Work.SurgeryInvariance.WindingOf.hasWinding_eq_of_homotopicClosed_param P hclosed
      (Work.SurgeryInvariance.WindingOf.hasWinding_of_liftOf Lα)
      (Work.SurgeryInvariance.WindingOf.hasWinding_of_liftOf Lβ)
  exact ⟨Lβ, by rw [← hEq]; exact hLα⟩

/-- **Essentiality is an invariant of the homotopy class of a closed curve of the torus.**  Two
closed curves of `F = P.carrier` which are homotopic through closed curves of `F` are essential
together: being essential is equivalent to having nonzero winding vector, and the winding vector
is a homotopy invariant. -/
theorem isEssential_iff_of_homotopic {P : Work.CoreTopology.ParamTorus}
    {α β : Work.CoreTopology.ClosedCurve P} (h : Work.CoreTopology.Homotopic P α β) :
    Work.CoreTopology.IsEssential P α ↔ Work.CoreTopology.IsEssential P β :=
  ⟨fun hα => isEssential_of_homotopic_of_isEssential h hα,
    fun hβ => isEssential_of_homotopic_of_isEssential (homotopic_symm h) hβ⟩

end

end Work.InnermostDisk
