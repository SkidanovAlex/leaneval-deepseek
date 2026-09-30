import Mathlib
import Submission.Work.Pi6.SQM.SIG.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000

/-!
# `clsPb` — the pullback on the class of a cocycle

`Work.Cohomology.singularCohomologyMap_classOf` says that `f*` of the class of a cocycle `α` is the
class of the cochain pullback of `α`.  In this file that statement is restated in the vocabulary of
area SQ (`Work.Pi6.SQM.cls`, `Work.Pi6.cmap`, `Work.Pi6.SQM.SIG.pb`), so that later files can use
it without unfolding `Work.Pi6.SQM.SIG.pb` (which is what makes the raw statement hard to `rw`
with, since `rw` matches at `reducible` transparency while the identification of the two cochain
complexes `SSetCochainComplex R (TopCat.toSSet.obj X)` and `singularCochainComplex R X` needs
`default` transparency).
-/

namespace Work.Pi6.SQM.SIG

/-- This is a thin restatement of the existing lemma
`Work.Cohomology.singularCohomologyMap_classOf` (in `Submission/Work/Cohomology/cupNaturalH.lean`),
using that `Work.Pi6.SQM.SIG.pb_continuous` holds by `rfl`. -/
theorem clsPb {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (φ : C(P, Q)) (n : ℕ)
    (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX Q) n)
    (hu : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX Q) u = 0)
    (h : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX P)
      (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (TopCat.ofHom φ)) u) = 0) :
    Work.Pi6.SQM.cls (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (TopCat.ofHom φ)) u) h =
      Work.Pi6.cmap Work.Pi6.SQ.F2 φ n (Work.Pi6.SQM.cls u hu) := by
  change Work.Cohomology.cohomologyClassOf Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX P)
      (Work.Pi6.SQM.SIG.pb (TopCat.toSSet.map (TopCat.ofHom φ)) u) h =
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2 (TopCat.of P) (TopCat.of Q)
        (TopCat.ofHom φ)) n))
      (Work.Cohomology.cohomologyClassOf Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX Q) u hu)
  rw [show (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2 (TopCat.of P) (TopCat.of Q)
          (TopCat.ofHom φ)) n))
        (Work.Cohomology.cohomologyClassOf Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX Q) u hu)
      = _ from
      Work.Cohomology.singularCohomologyMap_classOf Work.Pi6.SQ.F2 (TopCat.ofHom φ) u hu]
  exact Work.Cohomology.cohomologyClassOf_congr Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX P) rfl h _

end Work.Pi6.SQM.SIG
