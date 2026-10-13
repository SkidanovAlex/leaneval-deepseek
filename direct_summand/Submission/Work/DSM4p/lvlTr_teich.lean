import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl

universe a

namespace Work.DSM4p

theorem lvlTr_teich {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (N : ℕ) (r : Work.DSM4p.lvlP Q hgr (N + 1)) :
    Work.DSM4p.lvlTr Q hgr N
        (Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr (N + 1)))
          (WittVector.teichmuller p r)) =
      Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p (Work.DSM4p.chartTr (gr := Work.DSM4p.tiltTower gr hgr)
          (Work.DSM4p.tiltTower_isRootSystem gr hgr)
          (Work.DSM4p.tiltTower Q.ϖ Q.root) N r)) := by
  rw [lvlTr_apply, WittVector.map_teichmuller]
  rfl

end Work.DSM4p
