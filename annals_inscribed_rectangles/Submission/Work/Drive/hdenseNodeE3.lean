import Mathlib
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.sum_CntAt_products_eq_one_of_htop
import Submission.Work.Drive.guardedParity

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- (E3) of the project lead's `NOTES_LEAD_hdense.md`: the `hdense` functional identity at a pair
`(a, c') ∈ Ω`, from the one-parameter design data at a small `t`.  This is the wiring of §4:
`htop` from `Work.Drive.odd_sum_topBdryMeet_sweepChartFam`, `hblock` from `BlockT6AtN` (the transport
wrapper (E1), H4's lane), the `CntAt` identity from `Work.Drive.sum_CntAt_products_eq_one_of_htop`, the
six conversions via `Work.Drive.CntAt_cast_eq_sideGerm_of_level_lt_guarded` (germ data `GermDataAtN`),
then `Work.Drive.sideGerm_identity_of_CntAt_products`. -/
theorem hdense_identity_of_designTripleAtN {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    {a c' : UnitAddCircle} (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    {ε : ℝ} (hε : 0 < ε)
    (hGerm : Work.Drive.GermDataAtN Q c ![c / 2, c / 3, c / 4] ![0, a, a + c'] ε)
    (hgen : ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
      Work.Drive.DesignTripleAtN Q c ![c / 2, c / 3, c / 4] ![0, a, a + c'] t ∧
      Work.Drive.BlockT6AtN Q c ![c / 2, c / 3, c / 4] ![0, a, a + c'] t) :
    Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c a
        * Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c (a + c')
      + Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c (-a)
        * Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c c'
      + Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c (-(a + c'))
        * Work.Drive.sideGerm (fun s p => Work.Drive.chartPert s p) Q c (-c') = 1 := by
  classical
  -- ### Step 0: the concrete chart perturbation is a `ChartPert`
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  -- ### Step 1: a uniform level band for small perturbations
  obtain ⟨εl, hεl, hlvl⟩ :=
    exists_eps_level_lt_pertChart hQ (fun s p => chartPert s p) hΞ c hcbot
  -- ### Step 2: pick the design parameter
  obtain ⟨t, ht, hdes, hblk⟩ := hgen (min ε εl) (lt_min hε hεl) (min_le_left ε εl)
  have htε : ‖t‖ < ε := lt_of_lt_of_le ht (min_le_left ε εl)
  have htel : ‖t‖ < εl := lt_of_lt_of_le ht (min_le_right ε εl)
  have hdg : DesignGoodData Q c ![c / 2, c / 3, c / 4] ![0, a, a + c'] t := hdes.1
  have hodd : Odd (classTripleSet
      (fun k z => chartPert ((blk k) t) (rotPresentation Q (![0, a, a + c'] k) z))).ncard := hdes.2.1
  -- ### Step 3: the three block levels
  have e0 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 = c / 2 := rfl
  have e1 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1 = c / 3 := rfl
  have e2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
  have hcpos0 : (0 : ℝ) < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by rw [e0]; linarith
  have hcpos1 : (0 : ℝ) < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1 := by rw [e1]; linarith
  have hcpos2 : (0 : ℝ) < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 := by rw [e2]; linarith
  have hcpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := by
    intro k
    fin_cases k
    · exact hcpos0
    · exact hcpos1
    · exact hcpos2
  have hc1 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1
      < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
    rw [e1, e0]; linarith
  have hc2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2
      < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
    rw [e2, e0]; linarith
  -- ### Step 4: the level band of the perturbed plane presentations
  have hhlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
        < levelOf ((fun z => chartPert ((blk k) t)
            (rotPresentation Q (![0, a, a + c'] k) z)) y) := by
    intro k y
    have hmem : Q (sqDisk (foldBox y)) ∈ chartDisk Q :=
      ⟨sqDisk (foldBox y), by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_sqDisk_le_one _ (foldBox_mem_unitBox y), rfl⟩
    have h1 : c < levelOf (chartPert ((blk k) t) (Q (sqDisk (foldBox y)))) :=
      hlvl ((blk k) t) (lt_of_le_of_lt (norm_blk_le k t) htel) _ hmem
    obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : UnitAddCircle) = ![0, a, a + c'] k :=
      ⟨Quotient.out _, Quotient.out_eq _⟩
    have h3 : (fun z => chartPert ((blk k) t) (rotPresentation Q (![0, a, a + c'] k) z)) y
        = rotCapping (![0, a, a + c'] k)
            (chartPert ((blk k) t) (Q (sqDisk (foldBox y)))) := by
      show chartPert ((blk k) t) (rotPresentation Q (![0, a, a + c'] k) y) = _
      simp only [rotPresentation, diskPlane]
      rw [← hx]
      exact chartPert_rotCapping_comm x ((blk k) t) (Q (sqDisk (foldBox y)))
    rw [h3, levelOf_rotCapping, e0]
    linarith
  -- ### Step 5: the engine's output `htop`
  have htop := odd_sum_topBdryMeet_sweepChartFam (fun j => rotPresentation Q (![0, a, a + c'] j))
    (fun s p => chartPert s p) (![c / 2, c / 3, c / 4]) t hcpos hc1 hc2 hhlev hdg.1 hodd
  -- ### Step 6: the transport's per-block conclusion `hblock`
  have hblk' : ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace (designSweep (fun s p => chartPert s p) Q ![0, a, a + c']
          (fun j => (blk j) t) ![c / 2, c / 3, c / 4]) k).ncard) ↔
        (Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q ![0, a, a + c']
              (fun j => (blk j) t) k) ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) (k + 1))
              (blockPlane (fun s p => chartPert s p) Q ![0, a, a + c']
                (fun j => (blk j) t) (k + 1)))
          ∧ Odd (coreSideCount (blockChart (fun s p => chartPert s p) Q ![0, a, a + c']
              (fun j => (blk j) t) k) ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) (k + 2))
              (blockPlane (fun s p => chartPert s p) Q ![0, a, a + c']
                (fun j => (blk j) t) (k + 2)))) := by
    simpa only [BlockT6AtN] using hblk
  -- ### Step 7: the commutation of `chartPert` with the rotations
  have hcomm : ∀ (s : EuclideanSpace ℝ (Fin 4)) (w : UnitAddCircle) (p : CappingSpace),
      (fun s p => chartPert s p) s (rotCapping w p)
        = rotCapping w ((fun s p => chartPert s p) s p) := by
    intro s w p
    obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : UnitAddCircle) = w :=
      ⟨Quotient.out _, Quotient.out_eq _⟩
    rw [← hx]
    exact chartPert_rotCapping_comm x s p
  -- ### Step 8: the identity in the germ's own counts
  have hcnt := sum_CntAt_products_eq_one_of_htop (fun s p => chartPert s p) Q ![0, a, a + c']
    (fun j => (blk j) t) ![c / 2, c / 3, c / 4] htop hblk' hcomm
  -- ### Step 9: the six `CntAt`-to-`sideGerm` conversions
  have hconv : ∀ k j : Fin 3, k ≠ j →
      ((CntAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) j)
          ((![0, a, a + c'] j) - (![0, a, a + c'] k))
          ((fun j => (blk j) t) k, (fun j => (blk j) t) j) : ℕ) : ZMod 2)
        = sideGerm (fun s p => chartPert s p) Q c
            ((![0, a, a + c'] j) - (![0, a, a + c'] k)) := by
    intro k j hkj
    have ht' : ‖((blk k) t, (blk j) t)‖ < ε :=
      lt_of_le_of_lt (norm_pair_blk_le k j t) htε
    exact CntAt_cast_eq_sideGerm_of_level_lt_guarded (fun s p => chartPert s p) Q hΞ hQsm
      ((![0, a, a + c'] j) - (![0, a, a + c'] k)) hε hc (hcpos j)
      (hGerm.1 k j hkj) (hGerm.2.1 k j hkj) (hGerm.2.2 k j hkj) ht' (hdg.2.1 k j hkj)
  -- ### Step 10: the germ identity
  exact sideGerm_identity_of_CntAt_products (fun s p => chartPert s p) Q c a c' ![0, a, a + c']
    rfl rfl rfl (fun j => (blk j) t) ![c / 2, c / 3, c / 4] hcnt hconv

end

end Work.Drive
