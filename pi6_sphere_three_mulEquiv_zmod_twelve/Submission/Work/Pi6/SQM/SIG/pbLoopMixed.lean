import Mathlib
import Submission.Work.Pi6.SQM.SIG.ClsAux
import Submission.Work.Pi6.SQM.SIG.cup1mZeroLeft
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM.SIG

/-- The pushforward of the mixed cochain `A ∪₁ s + s ⌣ s` (where `A` is the pullback of the
relative cocycle `ã` along `evSSet : PK → K`) to the loop space is a cup square: naturality of `∪₁`
and of `⌣` under `pb`, together with `pb (loopSSet) A = 0` (the relative cocycle `ã` vanishes on
the fibre of `evSSet`). -/
theorem pbLoopMixed (hN : Work.Pi6.SQM.CupINatural)
    (K : Type) [TopologicalSpace K] (k₀ : K)
    (ã : Work.Cohomology.relKern Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K) 3)
    (s : Work.Cohomology.Cochain Work.Pi6.SQ.F2
      (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) 2) :
    Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.loopSSet K k₀)
        (Work.Pi6.SQ.cup1m (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) 3 2
            (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã.1) s
          + Work.Cohomology.cup Work.Pi6.SQ.F2
              (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) s s) =
      Work.Cohomology.cup Work.Pi6.SQ.F2 (Work.Pi6.SQM.SX (Path k₀ k₀))
        (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.loopSSet K k₀) s)
        (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.loopSSet K k₀) s) := by
  rw [pb_add, pb_cup1m hN, pb_cup, pb_loop_ev_relKern,
    cup1mZeroLeft (Work.Pi6.SQM.SX (Path k₀ k₀)) 3 2, zero_add]

end Work.Pi6.SQM.SIG
