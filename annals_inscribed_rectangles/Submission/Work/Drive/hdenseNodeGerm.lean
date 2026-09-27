import Mathlib
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.germLevelParity
import Submission.Work.Drive.sideGerm_parity_eq_of_close_loop
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.coreLoop_disjoint_rotCapping

/-!
# The germ-lane data `GermDataAtN` of the two germ nodes (proved)

`Work.Drive.GermDataAtN Q c cblk u ε` (`Submission/Work/Drive/hdenseOneT.lean`) is the bundle of the
germ lane's locality data at the six ordered pairs of the design's triple: the parity locality at the
level `c`, the parity locality at the levels `cblk j`, and the **cross-level parity agreement**.

The first two conjuncts are the germ route's `hn4`-type statement
(`Work.Drive.sideGerm_parity_eq_of_close_loop`, proved); the third is the cross-level parity, for which
the workspace's `Work.Drive.odd_coreSideCount_eq_of_lt_level` is *not* usable (it needs the faithfulness
of the box parameterisation, which `GoodPair` does not provide and which can fail,
`GEOMETRIC_LOCALITY_STATUS.md` §9).  This file uses instead the unconditional level independence
`Work.Drive.coreMeet_ncard_eq_of_lt_level` (`Submission/Work/Drive/coreMeetLevelIndep.lean`) through
`Work.Drive.odd_CntAt_eq_of_goodAt_of_levels` (`Submission/Work/Drive/germLevelParity.lean`), plus the
level bounds of the perturbed chart (`Work.Drive.exists_eps_level_lt_pertChart`).

The conclusion is the bundle the two germ endpoints consume; its `ε` is produced here (the minimum of
the finitely many locality radii), so that the two nodes only have to supply the chart data.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The germ-lane data `GermDataAtN` exists.**  For a plane chart `Q` of `γ`, the design's level `c`
(above the chart's disk), the three truncation levels `cblk` (positive and below `c`) and the three
angles `u` whose six differences lie in `Zc γ`, there is `ε > 0` with `GermDataAtN Q c cblk u ε`. -/
theorem exists_germDataAtN {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k) (hcblk_lt : ∀ k : Fin 3, cblk k < c)
    (u : Fin 3 → UnitAddCircle) (hu : ∀ k j : Fin 3, k ≠ j → u j - u k ∈ Zc γ) :
    ∃ ε : ℝ, 0 < ε ∧ GermDataAtN Q c cblk u ε := by
  classical
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  -- ## 1. the uniform level bound for small perturbations
  obtain ⟨εl, hεl, hlvl⟩ := exists_eps_level_lt_pertChart hQ (fun s p => chartPert s p) hΞc c hcbot
  -- ## 2. the finite set of ordered pairs
  let ι := {q : Fin 3 × Fin 3 // q.1 ≠ q.2}
  haveI : Fintype ι := Fintype.ofFinite ι
  -- ## 3. for each pair, the two parity localities, at a common radius
  have hpair : ∀ q : ι, ∃ ε : ℝ, 0 < ε ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c (u q.1.2 - u q.1.1) t →
        GoodAt (fun s p => chartPert s p) Q c (u q.1.2 - u q.1.1) t' →
        Odd (CntAt (fun s p => chartPert s p) Q c (u q.1.2 - u q.1.1) t) =
          Odd (CntAt (fun s p => chartPert s p) Q c (u q.1.2 - u q.1.1) t')) ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q (cblk q.1.2) (u q.1.2 - u q.1.1) t →
        GoodAt (fun s p => chartPert s p) Q (cblk q.1.2) (u q.1.2 - u q.1.1) t' →
        Odd (CntAt (fun s p => chartPert s p) Q (cblk q.1.2) (u q.1.2 - u q.1.1) t) =
          Odd (CntAt (fun s p => chartPert s p) Q (cblk q.1.2) (u q.1.2 - u q.1.1) t')) := by
    intro q
    obtain ⟨⟨k, j⟩, hkj⟩ := q
    have hloop : Disjoint (Set.range (coreLoop Q))
        (rotCapping (u j - u k) '' chartDisk Q) :=
      disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ (hu k j hkj)
    have hcbotj : ∀ p ∈ chartDisk Q, cblk j < levelOf p :=
      fun p hp => lt_trans (hcblk_lt j) (hcbot p hp)
    obtain ⟨ε₁, δ₁, hε₁, hδ₁, hU₁⟩ :=
      sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q c hΞc hQd hc hcbot
        (u j - u k) hloop
    obtain ⟨ε₂, δ₂, hε₂, hδ₂, hU₂⟩ :=
      sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q (cblk j) hΞc hQd (hcpos j)
        hcbotj (u j - u k) hloop
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
    · intro t t' ht ht' hg hg'
      refine hU₁ t t' (u j - u k)
        (lt_of_lt_of_le ht (min_le_left _ _)) (lt_of_lt_of_le ht' (min_le_left _ _))
        (by rw [dist_self]; exact hδ₁) hg hg'
    · intro t t' ht ht' hg hg'
      refine hU₂ t t' (u j - u k)
        (lt_of_lt_of_le ht (min_le_right _ _)) (lt_of_lt_of_le ht' (min_le_right _ _))
        (by rw [dist_self]; exact hδ₂) hg hg'
  choose f hf using hpair
  -- ## 4. the common radius
  obtain ⟨q₀⟩ : Nonempty ι := ⟨⟨(0, 1), by decide⟩⟩
  let S : Finset ℝ := insert εl (Finset.univ.image f)
  have hSne : S.Nonempty := ⟨εl, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hSne, ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hεl
    · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hb
      exact (hf q).1
  · have hεle : ∀ q : ι, S.min' hSne ≤ f q := fun q =>
      Finset.min'_le S (f q) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩))
    have hεlel : S.min' hSne ≤ εl := Finset.min'_le S εl (Finset.mem_insert_self _ _)
    have hlevc : ∀ t : EuclideanSpace ℝ (Fin 4), ‖t‖ < S.min' hSne →
        ∀ p ∈ chartDisk Q, c < levelOf (chartPert t p) := fun t ht p hp =>
      hlvl t (lt_of_lt_of_le ht hεlel) p hp
    refine ⟨?_, ?_, ?_⟩
    · -- the parity locality at the level `c`
      rintro k j hkj t t' ht ht' hg hg'
      exact (hf ⟨(k, j), hkj⟩).2.1 t t'
        (lt_of_lt_of_le ht (hεle ⟨(k, j), hkj⟩))
        (lt_of_lt_of_le ht' (hεle ⟨(k, j), hkj⟩)) hg hg'
    · -- the parity locality at the level `cblk j`
      rintro k j hkj t t' ht ht' hg hg'
      exact (hf ⟨(k, j), hkj⟩).2.2 t t'
        (lt_of_lt_of_le ht (hεle ⟨(k, j), hkj⟩))
        (lt_of_lt_of_le ht' (hεle ⟨(k, j), hkj⟩)) hg hg'
    · -- the cross-level parity
      rintro k j hkj t ht hg hg'
      have ht1 : ‖t.1‖ < S.min' hSne := lt_of_le_of_lt (norm_fst_le t) ht
      have ht2 : ‖t.2‖ < S.min' hSne := lt_of_le_of_lt (norm_snd_le t) ht
      have hlev1 : ∀ p ∈ chartDisk Q, c < levelOf (chartPert t.1 p) :=
        fun p hp => hlevc t.1 ht1 p hp
      have hlev1j : ∀ p ∈ chartDisk Q, cblk j < levelOf (chartPert t.1 p) :=
        fun p hp => lt_trans (hcblk_lt j) (hlev1 p hp)
      have hlev2 : ∀ p ∈ chartDisk Q, c < levelOf (chartPert t.2 p) :=
        fun p hp => hlevc t.2 ht2 p hp
      have hlev2j : ∀ p ∈ chartDisk Q, cblk j < levelOf (chartPert t.2 p) :=
        fun p hp => lt_trans (hcblk_lt j) (hlev2 p hp)
      exact odd_CntAt_eq_of_goodAt_of_levels (fun s p => chartPert s p) Q c (cblk j)
        (u j - u k) t hc (hcpos j)
        (levelLoop_pertChart _ Q c t.1 hlev1)
        (levelLoop_pertChart _ Q (cblk j) t.1 hlev1j)
        (level_rotPresentation_pertChart _ Q c t.2 (u j - u k) hlev2)
        (level_rotPresentation_pertChart _ Q (cblk j) t.2 (u j - u k) hlev2j)
        hg hg'

end

end Work.Drive
