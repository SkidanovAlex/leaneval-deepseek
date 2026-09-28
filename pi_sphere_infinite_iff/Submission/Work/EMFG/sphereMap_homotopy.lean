import Mathlib
import Submission.Work.Serre.CWModel.Descent

/-!
# A sphere map with trivial class at its base point is freely null-homotopic

`Work.Stems.collapseMap` identifies the boundary of the cube `I^n` with the base point of the
sphere `S^n`; pulling a map `f : S^n → X` back along it gives a based cube `q` representing `f`,
and `Work.Stems.cubeLift` inverts this correspondence.  If the homotopy group of `X` at the base
value of `f` is a subsingleton then `q` is homotopic (relative to the boundary) to the constant
cube, and descending that homotopy along the collapse
(`Work.Serre.CWModel.cubeLift_homotopic`) is the required *free* homotopy from `f` to a constant.

This is the "based ⇒ free" half of the cube/sphere dictionary, used to turn the vanishing of a
homotopy group of the target into the extension of a map over a cell
(`Work.EMFG.killCellsExtend`).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.EMFG

noncomputable section

/-- **A sphere map whose class at its own base point is trivial is freely null-homotopic.** -/
theorem sphereMap_homotopic_const_of_subsingleton {X : Type} [TopologicalSpace X] (n : ℕ) (hn : 1 ≤ n)
    (f : C(Work.Stems.sphere n, X))
    (h : Subsingleton (HomotopyGroup (Fin n) X (f (Work.Stems.collapseMap n hn 0)))) :
    f.Homotopic (ContinuousMap.const (Work.Stems.sphere n) (f (Work.Stems.collapseMap n hn 0))) := by
  set q : GenLoop (Fin n) X (f (Work.Stems.collapseMap n hn 0)) :=
    ⟨f.comp (Work.Stems.collapseMap n hn), fun w hw => by
      simp only [ContinuousMap.comp_apply]
      rw [Work.Stems.collapseMap_boundary n hn hw]⟩ with hq_def
  have hlift : Work.Stems.cubeLift n hn q = f := by
    ext z
    obtain ⟨w, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
    exact congrFun (congrArg (fun k : C(Work.Stems.CubeI n, X) => ⇑k)
      (Work.Stems.cubeLift_comp n hn q)) w
  have hq : GenLoop.Homotopic q
      (GenLoop.const (N := Fin n) (X := X) (x := f (Work.Stems.collapseMap n hn 0))) :=
    Quotient.exact (h.elim (Quotient.mk _ q)
      (Quotient.mk _ (GenLoop.const (N := Fin n) (X := X) (x := f (Work.Stems.collapseMap n hn 0)))))
  have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hq
  simp only [Work.Serre.CWModel.cubeLift_const] at h2
  rwa [hlift] at h2

end

end Work.EMFG
