import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.polyRegion_eq_iInter_pairSideNear
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.TopJordan.Jordan
import Submission.Work.ELAssembly.Q_adm_of

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

theorem Qmem_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) (hne : ∀ n : ℕ, (N.Qp n).y ≠ d.z₁) {L : ℝ} (hL : 1 < L) (n : ℕ) : Work.EL.polyRegion [Work.ELAssembly.alphaPairOf d, N.Qp n] (Work.ELNest.Qlev L n) = Work.EL.pairSideNear (Work.ELAssembly.alphaPairOf d) ∩ Work.EL.pairSideNear (N.Qp n) ∩ {z : ℂ | Work.EL.pot d.hN z < Real.log (Work.ELNest.Qlev L n)} := by
  have hA : Work.EL.PolyAdmissible [Work.ELAssembly.alphaPairOf d, N.Qp n] :=
    Q_adm_of d N hne n
  have hR : (1 : ℝ) < Work.ELNest.Qlev L n := (Work.ELNest.Qlev_facts hL n).1
  have hC : Work.Top.IsJordanCurve (Work.EL.polyCurve [Work.ELAssembly.alphaPairOf d, N.Qp n]
      (Work.ELNest.Qlev L n)) :=
    Work.ELTop.polyCurve_isJordan d.hN [Work.ELAssembly.alphaPairOf d, N.Qp n] hA hR
  exact Work.ELTop.polyRegion_pair_eq_pairSideNear_inter d.hN Work.TopJordan.jordanForm
    (Work.ELAssembly.alphaPairOf d) (N.Qp n) hA hR hC

end Work.ELAssembly
