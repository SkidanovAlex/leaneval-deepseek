/-
# `N0Aux.B4` — the level-`4` energy bound for `blkN0`

Assembling the split identity (`N0_split_open`), the `HkSq`-sub-additivity of the nested
seven-fold sum (`hkSq_sum7_le` at level `4`) and the level-`4` bounds of the seven pieces
(`NA1_HkSq4_le`, `NP3_HkSq4_le`, `NP4b_HkSq4_le`, `NP4a_HkSq4_le`, `NP5a_HkSq4_le`,
`NP5b_NP6_HkSq4`) gives

  `HkSq α 4 (blkN0 α w) ≤ K (1 + HkSq α 5 w)`

for `ClassC α w` with `Xn α w ≤ C₀ α²`, with `K = K(C₀)` uniform in `α ∈ (0,1]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Split
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4NA1
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4P1
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4P2
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq4
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem N0_HkSq4_le : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  intro C₀
  obtain ⟨K1, hK1pos, hNA1⟩ := NA1_HkSq4_le C₀
  obtain ⟨K3, hK3pos, hNP3⟩ := NP3_HkSq4_le C₀
  obtain ⟨K4a, hK4apos, hNP4a⟩ := NP4a_HkSq4_le C₀
  obtain ⟨K4b, hK4bpos, hNP4b⟩ := NP4b_HkSq4_le C₀
  obtain ⟨K5a, hK5apos, hNP5a⟩ := NP5a_HkSq4_le C₀
  obtain ⟨K56, hK56pos, hNP56⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq4 C₀
  refine ⟨64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1,
    by have h : 0 ≤ K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))) :=
         add_nonneg hK1pos.le (add_nonneg hK3pos.le (add_nonneg hK4apos.le
           (add_nonneg hK4bpos.le (add_nonneg hK5apos.le (add_nonneg hK56pos.le hK56pos.le)))))
       nlinarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hFstar : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (NA1 α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (NP3 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP3 hsmw hL
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (NP4a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4a hsmw hL
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (NP4b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP4b hsmw hL
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (NP5a α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5a hsmw hL
  have hs6 : Work.FTS.EllipticEst.SmoothOpen (NP5b α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP5b hsmw hL
  have hs7 : Work.FTS.EllipticEst.SmoothOpen (NP6 α w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NP6 hsmw hL
  obtain ⟨_K12, _hK12, hNA1six⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hNA1mem6, _hNA1bd⟩ := hNA1six α hα hα1
  have hm1 : Work.Spaces.HkMem α 4 (NA1 α) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs1 4 (by norm_num) hNA1mem6
  obtain ⟨hP3, hP4a, hP4b, hP5a, hP5b, hP6⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  have hm2 : Work.Spaces.HkMem α 4 (NP3 α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs2 4 (by norm_num) hP3
  have hm3 : Work.Spaces.HkMem α 4 (NP4a α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs3 4 (by norm_num) hP4a
  have hm4 : Work.Spaces.HkMem α 4 (NP4b α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs4 4 (by norm_num) hP4b
  have hm5 : Work.Spaces.HkMem α 4 (NP5a α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs5 4 (by norm_num) hP5a
  have hm6p : Work.Spaces.HkMem α 4 (NP5b α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs6 4 (by norm_num) hP5b
  have hm7p : Work.Spaces.HkMem α 4 (NP6 α w) :=
    Work.FTS.OpenPkg.HkMem_mono_open hs7 4 (by norm_num) hP6
  -- the split identity
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
    intro z θ hz hθ0 hθ1
    exact N0_split_open α hFstar hsmw z θ ⟨hz, hθ0, hθ1⟩
  have hsum := hkSq_sum7_le (α := α) (k := 4) hα hs1 hs2 hs3 hs4 hs5 hs6 hs7
    hm1 hm2 hm3 hm4 hm5 hm6p hm7p
  have hcongr : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hid
  -- the individual level-`4` bounds
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hb1 : Work.Spaces.HkSq α 4 (NA1 α) ≤ K1 * (1 + Work.Spaces.HkSq α 5 w) :=
    hNA1 α hαIoc w hw hXw
  have hb2 : Work.Spaces.HkSq α 4 (NP3 α w) ≤ K3 * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP3 α hαIoc w hw hXw
  have hb3 : Work.Spaces.HkSq α 4 (NP4a α w) ≤ K4a * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP4a α hαIoc w hw hXw
  have hb4 : Work.Spaces.HkSq α 4 (NP4b α w) ≤ K4b * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP4b α hαIoc w hw hXw
  have hb5 : Work.Spaces.HkSq α 4 (NP5a α w) ≤ K5a * (1 + Work.Spaces.HkSq α 5 w) :=
    hNP5a α hαIoc w hw hXw
  have hb6 : Work.Spaces.HkSq α 4 (NP5b α w) ≤ K56 * (1 + Work.Spaces.HkSq α 5 w) :=
    (hNP56 α hαIoc w hw hXw).1
  have hb7 : Work.Spaces.HkSq α 4 (NP6 α w) ≤ K56 * (1 + Work.Spaces.HkSq α 5 w) :=
    (hNP56 α hαIoc w hw hXw).2
  have hsum2 : Work.Spaces.HkSq α 4 (NA1 α) + Work.Spaces.HkSq α 4 (NP3 α w)
      + Work.Spaces.HkSq α 4 (NP4a α w) + Work.Spaces.HkSq α 4 (NP4b α w)
      + Work.Spaces.HkSq α 4 (NP5a α w) + Work.Spaces.HkSq α 4 (NP5b α w)
      + Work.Spaces.HkSq α 4 (NP6 α w)
      ≤ (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) * (1 + Work.Spaces.HkSq α 5 w) := by
    nlinarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, h5w]
  have hKnn : (0 : ℝ) ≤ K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))) :=
    add_nonneg hK1pos.le (add_nonneg hK3pos.le (add_nonneg hK4apos.le
      (add_nonneg hK4bpos.le (add_nonneg hK5apos.le (add_nonneg hK56pos.le hK56pos.le)))))
  have htot : Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
        + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))))
      ≤ 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
          * (1 + Work.Spaces.HkSq α 5 w)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hsum2 (by norm_num))
  have hfin : 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
        * (1 + Work.Spaces.HkSq α 5 w))
      ≤ (64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1)
        * (1 + Work.Spaces.HkSq α 5 w) := by
    nlinarith [h5w, hKnn]
  calc Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 4 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) := hcongr
    _ ≤ 64 * ((K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56))))))
          * (1 + Work.Spaces.HkSq α 5 w)) := htot
    _ ≤ (64 * (K1 + (K3 + (K4a + (K4b + (K5a + (K56 + K56)))))) + 1)
        * (1 + Work.Spaces.HkSq α 5 w) := hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
