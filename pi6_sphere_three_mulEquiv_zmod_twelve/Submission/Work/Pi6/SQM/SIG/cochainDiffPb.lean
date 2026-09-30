import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM.SIG

/-- **Naturality of the coboundary under pullback.**  Pulling a cochain back along a map of
simplicial sets commutes with the coboundary `cochainDiff`, because `pb` is the transpose of the
chain map `SSet.chainComplexMap f` and `cochainDiff` is the transpose of the boundary: the two
composites are the two sides of the commutation `comm` of the induced chain map. -/
theorem cochainDiffPb {X Y : SSet} (f : X ⟶ Y) (n : ℕ)
    (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 Y n) :
    Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X (Work.Pi6.SQM.SIG.pb f u) =
      Work.Pi6.SQM.SIG.pb f (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 Y u) := by
  apply LinearMap.ext
  intro x
  have hc := congrArg ModuleCat.Hom.hom
    ((SSet.chainComplexMap f (ModuleCat.of Work.Pi6.SQ.F2 Work.Pi6.SQ.F2)).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hc' := LinearMap.congr_fun hc x
  simp only [LinearMap.comp_apply] at hc'
  simp only [Work.Cohomology.cochainDiff, Work.Pi6.SQM.SIG.pb, LinearMap.comp_apply,
    LinearMap.dualMap_apply]
  rw [hc']

end Work.Pi6.SQM.SIG
