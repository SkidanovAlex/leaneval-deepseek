import Mathlib
import Submission.Work.Pi6.SQM.SIG.cupCobAux
import Submission.Work.Pi6.SQM.SIG.ClsAux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 2000000

namespace Work.Pi6.SQM.SIG

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

noncomputable section

/-- The coboundary of the mixed cochain `A ∪₁ s + s ⌣ s` with `A := pb (evSSet K k₀) ã.1` and
`δs = A` is `A ∪₁ A = pb (evSSet K k₀) (ã.1 ∪₁ ã.1)`: the first conjunct of `cupCobAux` gives
`δ(A∪₁s + s⌣s) = A∪₁A`, and naturality of `∪₁` under `pb` identifies `A ∪₁ A` with the pullback
along `evSSet` of `ã.1 ∪₁ ã.1` (`A = pb evSSet ã.1`).  `δA = 0` follows from `δã.1 = 0` and
naturality of the coboundary under pullback. -/
theorem deltaMixed (h1 : Work.Pi6.SQM.Cup1Cob) (h2 : Work.Pi6.SQM.Cup2Cob)
    (h3 : Work.Pi6.SQM.Cup3Cob) (hN : Work.Pi6.SQM.CupINatural)
    (K : Type) [TopologicalSpace K] (k₀ : K)
    (ã : Work.Cohomology.relKern Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K) 3)
    (hã : Work.Cohomology.relDiffLM Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K) 3 ã = 0)
    (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2
      (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) 2)
    (hs : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2
      (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) s
      = Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã.1) :
    Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀))
        (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) 3 2
            (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã.1) s
          + Work.Cohomology.cup Work.Pi6.SQ.F2
              (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) s s) =
      Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀)
        (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX K) 3 3 ã.1 ã.1) := by
  -- `ã.1` is an absolute cocycle on `K`, hence so is its pullback `A = pb evSSet ã.1`.
  have hdã : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX K) ã.1 = 0 :=
    Work.Pi6.SQM.SIG.relDiffLM_zero_cochainDiff ã hã
  have hA : Work.Cohomology.cochainDiff Work.Pi6.SQ.F2
      (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀))
      (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã.1) = 0 := by
    rw [Work.Pi6.SQM.SIG.cochainDiffPb (Work.Pi6.SQM.SIG.evSSet K k₀) 3 ã.1, hdã,
      Work.Pi6.SQM.SIG.pb_zero (Work.Pi6.SQM.SIG.evSSet K k₀)]
  -- the `i = 1` conjunct of `cupCobAux`.
  have hcob := (Work.Pi6.SQM.SIG.cupCobAux h1 h2 h3).1
    (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀))
    (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã.1) s hA hs
  rw [hcob]
  exact (Work.Pi6.SQM.SIG.pb_cup1m hN (Work.Pi6.SQM.SIG.evSSet K k₀) 3 3 ã.1 ã.1).symm

end

end Work.Pi6.SQM.SIG
