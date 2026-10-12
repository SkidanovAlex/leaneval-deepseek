import ChallengeDeps
import Submission.Work.BoseBoxFock.NH_eq_dGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

theorem H2ndHon_eq_H2ndF_dGamma (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∃ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
      Work.BoseBoxFock.H2ndHon v h fc fu HM μ
        = Work.BoseBoxFock.H2ndF (HM μ).f (HM μ).g (Work.BoseB4.dGamma (HM μ).m T_NH)
            ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) := by
  obtain ⟨T, hT⟩ := Work.BoseBoxFock.NH_eq_dGamma v h fc fu HM μ
  refine ⟨T, ?_⟩
  rw [Work.BoseBoxFock.H2ndHon, hT]

end Work.MB
