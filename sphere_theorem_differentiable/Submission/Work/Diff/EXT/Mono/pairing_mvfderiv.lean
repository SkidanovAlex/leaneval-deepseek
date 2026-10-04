import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.Mono

theorem pairing_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (P : Work.Diff.EXT.TField (I := I) (M := M))
    (hP : Work.Diff.GE.SmoothFieldT (I := I) (M := M) P)
    (X : Work.Diff.EXT.TField (I := I) (M := M))
    (hX : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X)
    (i : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun z => g.inner z (e i z) (P z)) y (X y)
      = g.inner y (e i y) (Work.Diff.EXT.dirF g P X y) := by
  rw [Work.Diff.GE.kato_mvfderiv_inner_lc (I := I) (M := M) g y (X y) (he i) hP,
    show Submission.Diff.lcOf g (e i) y (X y) = 0 from by
      rw [hgeo i, ContinuousLinearMap.zero_apply]]
  simp only [Work.Diff.EXT.dirF, map_zero, ContinuousLinearMap.zero_apply, zero_add]

end Work.Diff.EXT.Mono
