/-
# `N0Aux.B6` — the level-`6` energy bound for `blkN0`

Assembling the split identity (`N0_split_open`), the `HkSq`-sub-additivity of the nested
seven-fold sum (`hkSq_sum7_le`) and the level-`6` bounds of the seven pieces
(`FstarI12H6` for `NA1` and the three delegated blocks `NP3_NP4b_HkSq6`,
`NP5b_NP6_HkSq6`, `N04aN05a_HkSq6`) gives

  `HkSq α 6 (blkN0 α w) ≤ K (1 + HkSq α 7 w) + K (1 + HkSq α 6 w)²`

for `ClassC α w` with `Xn α w ≤ C₀ α²`, with `K = K(C₀)` uniform in `α ∈ (0,1]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Split
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP3_NP4b_HkSq6
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq6
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_HkSq6
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

theorem N0_HkSq6_le : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
  intro C₀
  obtain ⟨K12, hK12pos, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨Ka, hKapos, hb34⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP3_NP4b_HkSq6 C₀
  obtain ⟨Kb, hKbpos, hb56⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq6 C₀
  obtain ⟨Kc, hKcpos, hb45a⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_HkSq6 C₀
  refine ⟨64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1, by positivity, ?_⟩
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
  obtain ⟨hNA1mem, hNA1bd⟩ := hNA1 α hα hα1
  have hm1 : Work.Spaces.HkMem α 6 (NA1 α) := hNA1mem
  obtain ⟨hP3, hP4a, hP4b, hP5a, hP5b, hP6⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  -- the split identity
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
    intro z θ hz hθ0 hθ1
    exact N0_split_open α hFstar hsmw z θ ⟨hz, hθ0, hθ1⟩
  have hsum := hkSq_sum7_le (α := α) (k := 6) hα hs1 hs2 hs3 hs4 hs5 hs6 hs7
    hm1 hP3 hP4a hP4b hP5a hP5b hP6
  have hcongr : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 6 hid
  -- the individual level-`6` bounds, all in terms of `1 + HkSq α 7 w`
  have h6w : (0 : ℝ) ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
  have h7w : (0 : ℝ) ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hm7
  have honenn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
  have hb1 : Work.Spaces.HkSq α 6 (NA1 α) ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := by
    have h2 : Work.Spaces.HkSq α 6 (NA1 α) = (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (NA1 α))]
    have h3 : (Work.Spaces.HkNorm α 6 (NA1 α)) ^ 2 ≤ (K12 * α ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 (NA1 α)) hNA1bd 2
    have h4 : (K12 * α ^ 2) ^ 2 ≤ K12 ^ 2 := by
      have h5 : (K12 * α ^ 2) ^ 2 = K12 ^ 2 * (α ^ 2) ^ 2 := by ring
      rw [h5]
      have h6 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
      have h7 : (α ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α ^ 2), h6]
      calc K12 ^ 2 * (α ^ 2) ^ 2 ≤ K12 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg K12)
        _ = K12 ^ 2 := by ring
    calc Work.Spaces.HkSq α 6 (NA1 α) ≤ K12 ^ 2 := by rw [h2]; exact le_trans h3 h4
      _ = K12 ^ 2 * 1 := by ring
      _ ≤ K12 ^ 2 * (1 + Work.Spaces.HkSq α 7 w) :=
          mul_le_mul_of_nonneg_left hone (sq_nonneg K12)
  have hb3' : Work.Spaces.HkSq α 6 (NP3 α w) ≤ Ka * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (hb34 α hαIoc w hw hXw).1
      (mul_le_mul_of_nonneg_left (by linarith [h67]) hKapos.le)
  have hb4' : Work.Spaces.HkSq α 6 (NP4b α w) ≤ Ka * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb34 α hαIoc w hw hXw).2
  have hb5' : Work.Spaces.HkSq α 6 (NP5b α w) ≤ Kb * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb56 α hαIoc w hw hXw).1
  have hb6' : Work.Spaces.HkSq α 6 (NP6 α w) ≤ Kb * (1 + Work.Spaces.HkSq α 7 w) :=
    (hb56 α hαIoc w hw hXw).2
  have hb4a' : Work.Spaces.HkSq α 6 (NP4a α w) ≤ Kc * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (le_trans (hb45a α hαIoc w hw hXw).1
        (mul_le_mul_of_nonneg_left (by linarith [h67]) hKcpos.le))
      (le_of_eq (by ring : Kc * (1 + Work.Spaces.HkSq α 7 w)
        = Kc * (1 + Work.Spaces.HkSq α 7 w)))
  have hb5a' : Work.Spaces.HkSq α 6 (NP5a α w) ≤ Kc * (1 + Work.Spaces.HkSq α 7 w) :=
    le_trans (le_trans (hb45a α hαIoc w hw hXw).2
        (mul_le_mul_of_nonneg_left (by linarith [h67]) hKcpos.le))
      (le_of_eq (by ring : Kc * (1 + Work.Spaces.HkSq α 7 w)
        = Kc * (1 + Work.Spaces.HkSq α 7 w)))
  -- the total
  have hsum2 : Work.Spaces.HkSq α 6 (NA1 α) + Work.Spaces.HkSq α 6 (NP3 α w)
      + Work.Spaces.HkSq α 6 (NP4a α w) + Work.Spaces.HkSq α 6 (NP4b α w)
      + Work.Spaces.HkSq α 6 (NP5a α w) + Work.Spaces.HkSq α 6 (NP5b α w)
      + Work.Spaces.HkSq α 6 (NP6 α w)
      ≤ (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w) := by
    linarith [hb1, hb3', hb4a', hb5a', hb4', hb5', hb6']
  have htot : Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
        + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))))
      ≤ 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hsum2 (by norm_num))
  have hfin : 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w))
      ≤ (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by
    have h2 : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
    nlinarith [h7w, h6w, h2]
  calc Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w)
      = Work.Spaces.HkSq α 6 (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ
          + (NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) := hcongr
    _ ≤ 64 * ((K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) * (1 + Work.Spaces.HkSq α 7 w)) := htot
    _ ≤ (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 7 w)
        + (64 * (K12 ^ 2 + (Ka + Ka + Kb + Kb + Kc + Kc)) + 1) * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
