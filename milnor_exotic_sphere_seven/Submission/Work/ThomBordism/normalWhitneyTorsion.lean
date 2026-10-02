import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Thom.manifoldP1
import Submission.Work.Whitney.Hypotheses
import Submission.Work.ThomBordism.nwtAux
import Submission.Work.ThomBordism.nwtChain
import Submission.Work.ThomBordism.nwtCast

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom
open Work.ThomBordism.Grassmann

noncomputable section

theorem normalWhitneyTorsion {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    [Fintype (Work.ThomBordism.PontryaginThom.CoverIdx V k)] :
    (∃ N : ℕ, 0 < N ∧ (N : ℤ) •
        ((Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND) : Work.Thom.Coh ℤ 4 V.pt)
          + (show Work.Thom.Coh ℤ 4 V.pt from V.p1)) = 0) ∧
    (∃ N : ℕ, 0 < N ∧ (N : ℤ) •
        (((by norm_num : 4 * 2 = 8) ▸ Work.Thom.pontryaginClass 2 (Work.Tubular.normalBundle E ND)
            : Work.Thom.Coh ℤ 8 V.pt)
          + (show Work.Thom.Coh ℤ 8 V.pt from
              (by norm_num : 4 + 4 = 8) ▸
                Work.Cohomology.cupH' ℤ (Work.ThomBordism.PontryaginThom.ssetOf V.pt) 4 4
                  (show (Work.Cohomology.cochainC ℤ
                      (Work.ThomBordism.PontryaginThom.ssetOf V.pt)).homology 4
                    from Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND))
                  (show (Work.Cohomology.cochainC ℤ
                      (Work.ThomBordism.PontryaginThom.ssetOf V.pt)).homology 4 from V.p1))
          + (show Work.Thom.Coh ℤ 8 V.pt from V.p2)) = 0) := by
  have hp1 : (show Work.Thom.Coh ℤ 4 V.pt from V.p1) = Work.Thom.pontryagin1 (Zt0 V) := by
    rw [show (show Work.Thom.Coh ℤ 4 V.pt from V.p1)
        = Work.Thom.pontryagin1 (Zt1 V) from rfl]
    exact pontryagin1_Zt1_eq_Zt0 V
  have hC1 : (show (Work.Cohomology.cochainC ℤ (ssetOf V.pt)).homology 4 from V.p1)
      = (show (Work.Cohomology.cochainC ℤ (ssetOf V.pt)).homology 4
          from Work.Thom.pontryagin1 (Zt0 V)) := by
    rw [show (show (Work.Cohomology.cochainC ℤ (ssetOf V.pt)).homology 4 from V.p1)
        = (show (Work.Cohomology.cochainC ℤ (ssetOf V.pt)).homology 4
            from Work.Thom.pontryagin1 (Zt1 V)) from rfl]
    exact pontryagin1_Zt1_eq_Zt0 V
  have hA : (show Work.Thom.Coh ℤ 8 V.pt from V.p2)
      = (show Work.Thom.Coh ℤ 8 V.pt from Work.Thom.pontryaginClass 2 (Zt0 V)) := by
    rw [show (show Work.Thom.Coh ℤ 8 V.pt from V.p2)
        = Work.Thom.chernClass (Module.finrank ℝ (Euc 8)) 4
            (Work.Thom.complexificationCore (Zt1 V)) from rfl,
      chernClass_Zt1_eq_Zt0, ← Work.Whitney.pontryaginClass_two_eq]
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    have h1 := two_smul_pontryagin1_eq_zero_of_sum_trivial (Zt0 V)
      (Work.Tubular.normalBundle E ND) (nonempty_bundleIso_whitneySumR_Zt0_trivial V E ND)
    rw [hp1, add_comm]
    exact h1
  · refine ⟨2, by norm_num, ?_⟩
    have h2 := two_smul_pontryagin2_eq_zero_of_sum_trivial (Zt0 V)
      (Work.Tubular.normalBundle E ND) (nonempty_bundleIso_whitneySumR_Zt0_trivial V E ND)
    rw [eqRec_four_two (by norm_num : 4 * 2 = 8) (Work.Thom.pontryaginClass 2 (Work.Tubular.normalBundle E ND)),
      cupH'_cast_eq_cupChern_swap (by norm_num : 4 + 4 = 8) _ _, hC1, hA]
    rw [show (Work.Thom.pontryaginClass 2 (Work.Tubular.normalBundle E ND)
          + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 (Zt0 V))
              (Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND))
          + (show Work.Thom.Coh ℤ 8 V.pt from Work.Thom.pontryaginClass 2 (Zt0 V)))
        = (Work.Thom.pontryaginClass 2 (Zt0 V)
          + Work.Whitney.cupChern 2 2 (Work.Thom.pontryagin1 (Zt0 V))
              (Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND))
          + Work.Thom.pontryaginClass 2 (Work.Tubular.normalBundle E ND)) from by abel]
    exact h2

end

end Work.ThomBordism
