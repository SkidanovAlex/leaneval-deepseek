import Mathlib
import Submission.Work.DSM4p.Plan

namespace Work.DSM4p

universe a

theorem lvl_mk_teich_tiltTower {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr) (n : ℕ)
    {r : ℕ → B} (hr : Work.DSM4p.IsRootSystem p r) (k : ℕ) :
    Work.DSM5c.untiltOf.mk (p := p) (W := B) (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n))
      (WittVector.teichmuller p (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n)
        (Work.DSM4p.tiltTower r hr k)))
    = algebraMap B (Work.DSM4p.lvl Q hgr n) (r k) := by
  rw [Work.DSM5c.Eta.U.teich_algebraMap (p := p) (W := B)
      (Work.DSM4p.surjective_fontaineTheta Q)
      (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n))
      (Work.DSM4p.tiltTower r hr k),
    Work.DSM4p.untilt_tiltTower r hr k]
  rfl

end Work.DSM4p
