/-
# `blocks.N0_BData` — the `BData` package for the `N₀`-block `blkN0 α w`

`BData α w K (blkN0 α w)` bundles the open-quadrant smoothness, the `ℋ⁶`-honesty and the two
semi-tame size bounds of the block `blkN0 α w = N0 α (F_* + w) w`:

* `HkSq α 4 (blkN0 α w) ≤ K (1 + HkSq α 5 w)` — `N0Aux.N0_HkSq4_le` (the level-`4` assembly
  `N0Aux.B4` over the seven pieces of the `N₀`-row);
* `HkSq α 6 (blkN0 α w) ≤ K (1 + HkSq α 7 w) + K (1 + HkSq α 6 w)²` — `N0Aux.N0_HkSq6_le`
  (the level-`6` assembly `N0Aux.B6`).

`K = max K₄ K₆` with both constants depending only on `C₀`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Split
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.hkmem_pieces_own
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

/-- The `N₀`-block is `C^∞` on the open quadrant (this is `H6Pair6Aux.SmoothN0`, spelled with
the `blkN0`-vocabulary). -/
theorem smoothOpen_blkN0 {α : ℝ} (hα : 0 < α) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.EllipticEst.SmoothOpen w)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z)) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) :=
  Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw hL

/-- The `N₀`-block is `ℋ⁶`-honest: combine the `ℋ⁶`-memberships of the seven pieces of the
split `N0_split_open`. -/
theorem hkMem6_blkN0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) := by
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
  obtain ⟨_K12, _hK12, hNA1⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨hm1, _⟩ := hNA1 α hα hα1
  obtain ⟨hm2, hm3, hm4, hm5, hm6p, hm7p⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.hkmem_N0pieces_own hα hα1 hsmw hL hw.l12 hm6 hm7
  have h67 : Work.Spaces.HkMem α 6 (fun z θ => NP5b α w z θ + NP6 α w z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs6 hs7 hm6p hm7p
  have hs67 := hs6.add hs7
  have h567 : Work.Spaces.HkMem α 6
      (fun z θ => NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs5 hs67 hm5 h67
  have hs567 := hs5.add hs67
  have h4567 : Work.Spaces.HkMem α 6
      (fun z θ => NP4b α w z θ + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs4 hs567 hm4 h567
  have hs4567 := hs4.add hs567
  have h34567 : Work.Spaces.HkMem α 6
      (fun z θ => NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs3 hs4567 hm3 h4567
  have hs34567 := hs3.add hs4567
  have h234567 : Work.Spaces.HkMem α 6
      (fun z θ => NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs2 hs34567 hm2 h34567
  have hs234567 := hs2.add hs34567
  have h1234567 : Work.Spaces.HkMem α 6
      (fun z θ => NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
        + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ)))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α 6 hs1 hs234567 hm1 h234567
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 h1234567 ?_
  intro z hz θ hθ
  exact (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_split_open α hFstar
    hsmw z θ ⟨hz, hθ.1, hθ.2⟩).symm

theorem N0_BData : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ w : ℝ → ℝ → ℝ,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) →
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w) := by
  intro C₀
  obtain ⟨K4, hK4pos, h4⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_HkSq4_le C₀
  obtain ⟨K6, hK6pos, h6⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.N0_HkSq6_le C₀
  refine ⟨max K4 K6, lt_max_of_lt_left hK4pos, ?_⟩
  intro α hαIoc w hw hXw _hz
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have h5w : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by
    have h := Work.Spaces.HkSq_nonneg α 5 w
    linarith
  have h6w : (0 : ℝ) ≤ (1 + Work.Spaces.HkSq α 6 w) ^ 2 := sq_nonneg _
  have h7w : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by
    have h := Work.Spaces.HkSq_nonneg α 7 w
    linarith
  refine ⟨smoothOpen_blkN0 hα hw.reg hL, hkMem6_blkN0 hα hα1 hw, ?_, ?_⟩
  · exact le_trans (h4 α hαIoc w hw hXw)
      (mul_le_mul_of_nonneg_right (le_max_left K4 K6) h5w)
  · have h := h6 α hαIoc w hw hXw
    have h1 : K6 * (1 + Work.Spaces.HkSq α 7 w)
        ≤ max K4 K6 * (1 + Work.Spaces.HkSq α 7 w) :=
      mul_le_mul_of_nonneg_right (le_max_right K4 K6) h7w
    have h2 : K6 * (1 + Work.Spaces.HkSq α 6 w) ^ 2
        ≤ max K4 K6 * (1 + Work.Spaces.HkSq α 6 w) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right K4 K6) h6w
    linarith

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks
