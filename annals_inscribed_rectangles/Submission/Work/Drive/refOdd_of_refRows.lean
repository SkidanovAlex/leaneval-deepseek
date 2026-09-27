import Mathlib
import Submission.Work.Drive.refParityRows
import Submission.Work.Drive.hasClassLinearizationAlt
import Submission.Work.Drive.classTripleOdd
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.foldFlatDesign
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.classRowDesignData
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.linPlaneChartsEndTripleReg

/-!
# The class-triple parity of the perturbed reference triple from the six *rows*

The node reduces the `hodd` chapter of the `hn2` configuration to the class-level *rows*: given the
six `PairReg`/`EndTripleReg` rows `Work.Drive.RefRows` of the reference triple
`refTriple Q (refPlanePres φ lam hlam) u v` against the per-block **transported** linear family
`k ↦ (linBase A k).trans (classEquiv (blk k t))`, together with the general-position clauses
`Work.Drive.RefGP`, the class-triple set of the perturbed reference triple has **odd** cardinality.

The proof is the `hn2` analogue of `Work.Drive.exists_classRowFamily` (the design's own row assembly):
the homotopies are the per-block **transported** `(B)`-lane homotopies
`k ↦ transportHom H0 t k` (`Drive/classRowDesignData.lean`), which run from the perturbed reference
plane `refPertBlock … k` to the transported linear model `linRowModel A t k`; the three `Meet3Hyp`
clauses of the class linearisation are produced by `exists_homotopy_meet3Hyp_encodedAlt`, and the whole
is fed to `odd_ncard_classTripleSet_of_hasClassLinearization`.

The one row that `RefRows` does not contain — the *all-linear* row
`EndTripleReg lin₂ lin₀ lin₁` — is **derived** from the general-position clauses alone
(`endTripleReg_linPlaneCharts_uncond`), and the remaining rows of the three clauses are the
cyclic/transposed reorderings of `hL012` and `hL10P2`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem refOdd_of_refRows {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    (u v : UnitAddCircle) (φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Work.Drive.Eucl 3))
    (hH00 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (0, y) = Work.Drive.planeClassMap (Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k) y)
    (hH01 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Work.Drive.linBase A k) 1 one_pos)) y)
    (hH0seam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
      Work.Drive.onSeam2 y → H0 k (s, Work.Drive.seamInv2 y) = H0 k (s, y))
    (hH0sm : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, Work.Drive.mk2 (x 0) (x 1))))
    (t : EuclideanSpace ℝ (Fin 12))
    (hrows : Work.Drive.RefRows Q u v φ lam hlam A t) (hgp : Work.Drive.RefGP A t) :
    Odd (Work.Drive.classTripleSet
      (fun k z => Work.Drive.chartPert (Work.Drive.blk k t)
        (Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k z))).ncard := by
  classical
  -- ## the general position (`RefGP`) and the six rows (`RefRows`)
  obtain ⟨hrank, hgen⟩ := hgp
  obtain ⟨hpairL0L1, hpairL0P2, hpair12, h012, hL012, hL10P2⟩ := hrows
  have hQsm : Work.Drive.IsSmoothChart Q := Work.Drive.IsSmoothChart_of_isPlaneChart hQ
  have hΞc : Work.Drive.ChartPert Q 4 (fun s p => Work.Drive.chartPert s p) :=
    Work.Drive.isChartPert_chartPert Q
  -- ## smoothness, seam invariance and fold flatness of the perturbed reference blocks
  have hsmPert : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k)) := by
    intro k
    have h1 : Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
        (Work.Drive.refPlanePres φ lam hlam) u v t k
        = Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k := rfl
    have hsm : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop
        (Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
          (Work.Drive.refPlanePres φ lam hlam) u v t k) :=
      Work.Drive.refBlock_contMDiff Q hQsm (fun s p => Work.Drive.chartPert s p) hΞc φ lam hlam u v t k
    rw [h1] at hsm
    exact fun y => Work.Drive.contMDiffAt_cls_of_contMDiff_gen (k := 2) hsm y
  have hfoldPert : ∀ k : Fin 3, Work.Drive.FoldFlat
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k)) := by
    intro k
    have h1 : Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
        (Work.Drive.refPlanePres φ lam hlam) u v t k
        = Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k := rfl
    have h : Work.Drive.FoldFlat (Work.Drive.planeClassMap
        (Work.Drive.refBlock (fun s p => Work.Drive.chartPert s p) Q
          (Work.Drive.refPlanePres φ lam hlam) u v t k)) :=
      Work.Drive.foldFlat_refBlock Q hQsm φ lam hlam u v t k
    rwa [h1] at h
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 y →
      Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k (Work.Drive.seamInv2 y)
        = Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k y := by
    intro k y hy
    fin_cases k
    · simpa [Work.Drive.refTriple] using
        (Work.Drive.rotPresentation_seamInv Q hQ.2.2.1 u y hy).symm
    · simpa [Work.Drive.refTriple] using
        (Work.Drive.rotPresentation_seamInv Q hQ.2.2.1 v y hy).symm
    · simpa [Work.Drive.refTriple] using (Work.Drive.refPlanePres_seam φ lam hlam y hy).symm
  have hseamPert : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 y →
      Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k)
          (Work.Drive.seamInv2 y)
        = Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k) y := by
    intro k y hy
    simp only [Work.Drive.refPertBlock, Work.Drive.planeClassMap]
    rw [hPseam k y hy]
  -- ## the same data for the transported linear models `linRowModel A t k`
  have hsmLin : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.linRowModel A t k) := by
    intro k
    change ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t))) 1 one_pos)))
    exact fun y => Work.Drive.contMDiffAt_cls_of_contMDiff_gen (k := 2)
      (Work.Drive.contMDiff_diskPlane (Work.Drive.linPlaneChart_contMDiff _ 1 one_pos)) y
  have hseamLin : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 y →
      (Work.Drive.linRowModel A t k) (Work.Drive.seamInv2 y) = (Work.Drive.linRowModel A t k) y := by
    intro k y hy
    change Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t))) 1 one_pos))
        (Work.Drive.seamInv2 y)
      = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t))) 1 one_pos)) y
    simp only [Work.Drive.planeClassMap]
    rw [Work.Drive.diskPlane_seamInv2
      (Q := Work.Drive.linPlaneChart ((Work.Drive.linBase A k).trans
        (Work.Drive.classEquiv ((Work.Drive.blk k) t))) 1 one_pos)
      (fun z hz => Work.Drive.linPlaneChart_neg _ 1 one_pos hz) hy]
  have hfoldLin : ∀ k : Fin 3, Work.Drive.FoldFlat (Work.Drive.linRowModel A t k) := by
    intro k
    exact Work.Drive.foldFlat_linTransClass (Work.Drive.linBase A k) 1 one_pos ((Work.Drive.blk k) t)
  -- ## the per-block transported `(B)`-lane homotopies
  set H : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Work.Drive.Eucl 3) :=
    fun k => Work.Drive.transportHom H0 t k with hH
  have hsmH : ∀ k, ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H k (x 2, Work.Drive.mk2 (x 0) (x 1))) :=
    fun k => Work.Drive.contMDiff_transportHom_chain H0 t k (hH0sm k)
  have hseamH : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), Work.Drive.onSeam2 y →
      H k (s, Work.Drive.seamInv2 y) = H k (s, y) :=
    fun k s y hy => Work.Drive.transportHom_seam H0 t k (fun s' y' hy' => hH0seam k s' y' hy') s y hy
  have ht0 : ∀ k : Fin 3, (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.transportHom H0 t k (0, y))
      = Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t k) := by
    intro k
    rw [Work.Drive.transportHom_zero_eq H0 t k (funext (hH00 k))]
    funext y
    show Work.Drive.classMap ((Work.Drive.blk k) t) (Work.Drive.planeClassMap
        (Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k) y)
      = Work.Drive.planeClassMap (fun y' => Work.Drive.chartPert ((Work.Drive.blk k) t)
          (Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k y')) y
    rw [Work.Drive.planeClassMap_chartPert_comp_cr]
    rfl
  have ht1 : ∀ k : Fin 3, (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.transportHom H0 t k (1, y))
      = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
          ((Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t))) 1 one_pos)) := by
    intro k
    exact Work.Drive.transportHom_one_design (fun k => Work.Drive.linBase A k) 1 one_pos H0 hH01 t k
  have hconst0 : ∀ (k : Fin 3) (s : ℝ), s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2),
      H k (s, y) = H k (0, y) := fun k s hs y => Work.Drive.transportHom_left H0 t k hs y
  have hconst1 : ∀ (k : Fin 3) (s : ℝ), 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2),
      H k (s, y) = H k (1, y) := fun k s hs y => Work.Drive.transportHom_right H0 t k hs y
  -- ## the rows read at the two ends of the transported homotopies
  have h012' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (0, y))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (0, y)) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 0) from ht0 0]
    exact h012
  have hL012' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (1, y))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (1, y)) = Work.Drive.linRowModel A t 0 from ht1 0]
    exact hL012
  have hP1L0P2 : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (0, y))
      (Work.Drive.linRowModel A t 0)
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (0, y)) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1) from ht0 1]
    exact Work.Drive.endTripleReg_swap23Alt (Work.Drive.endTripleReg_cyclic hL012)
  have hL10P2' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (1, y))
      (Work.Drive.linRowModel A t 0)
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (1, y)) = Work.Drive.linRowModel A t 1 from ht1 1]
    exact hL10P2
  have hP2L0L1 : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (0, y))
      (Work.Drive.linRowModel A t 0) (Work.Drive.linRowModel A t 1) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (0, y)) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2) from ht0 2]
    exact Work.Drive.endTripleReg_swap23Alt
      (Work.Drive.endTripleReg_cyclic (Work.Drive.endTripleReg_cyclic hL10P2))
  -- ## the all-linear row, derived from the general-position clauses alone
  have hLLL : Work.Drive.EndTripleReg (Work.Drive.linRowModel A t 2)
      (Work.Drive.linRowModel A t 0) (Work.Drive.linRowModel A t 1) :=
    Work.Drive.endTripleReg_linPlaneCharts_uncond
      (fun k => (Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t)))
      1 one_pos hrank hgen
  have hLLL' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (1, y))
      (Work.Drive.linRowModel A t 0) (Work.Drive.linRowModel A t 1) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (1, y)) = Work.Drive.linRowModel A t 2 from ht1 2]
    exact hLLL
  -- ## the three clauses of the class linearisation, each by the ends-clause genericity
  have hc₀0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hc₀1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨H0', hH0'0, hH0'1, hM0⟩ := Work.Drive.exists_homotopy_meet3Hyp_encodedAlt
    (H := H 0) (A := Work.Drive.planeClassMap
      (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1))
    (B := Work.Drive.planeClassMap
      (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) hc₀0 hc₀1
    (hsmH 0) (hsmPert 1) (hsmPert 2) (hseamH 0) (hseamPert 1) (hseamPert 2)
    (fun s hs y => hconst0 0 s hs y) (fun s hs y => hconst1 0 s hs y)
    hpair12 h012' hL012' (hfoldPert 1) (hfoldPert 2)
    (by rw [ht0 0]; exact hfoldPert 0) (by rw [ht1 0]; exact hfoldLin 0)
  obtain ⟨H1', hH1'0, hH1'1, hM1⟩ := Work.Drive.exists_homotopy_meet3Hyp_encodedAlt
    (H := H 1) (A := Work.Drive.linRowModel A t 0)
    (B := Work.Drive.planeClassMap
      (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) hc₀0 hc₀1
    (hsmH 1) (hsmLin 0) (hsmPert 2) (hseamH 1) (hseamLin 0) (hseamPert 2)
    (fun s hs y => hconst0 1 s hs y) (fun s hs y => hconst1 1 s hs y)
    hpairL0P2 hP1L0P2 hL10P2' (hfoldLin 0) (hfoldPert 2)
    (by rw [ht0 1]; exact hfoldPert 1) (by rw [ht1 1]; exact hfoldLin 1)
  obtain ⟨H2', hH2'0, hH2'1, hM2⟩ := Work.Drive.exists_homotopy_meet3Hyp_encodedAlt
    (H := H 2) (A := Work.Drive.linRowModel A t 0) (B := Work.Drive.linRowModel A t 1) hc₀0 hc₀1
    (hsmH 2) (hsmLin 0) (hsmLin 1) (hseamH 2) (hseamLin 0) (hseamLin 1)
    (fun s hs y => hconst0 2 s hs y) (fun s hs y => hconst1 2 s hs y)
    hpairL0L1 hP2L0L1 hLLL' (hfoldLin 0) (hfoldLin 1)
    (by rw [ht0 2]; exact hfoldPert 2) (by rw [ht1 2]; exact hfoldLin 2)
  -- ## the class linearisation, and the oddness of the class-triple count
  refine Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization
    (P := fun k y => Work.Drive.chartPert (Work.Drive.blk k t)
      (Work.Drive.refTriple Q (Work.Drive.refPlanePres φ lam hlam) u v k y)) ?_
  refine ⟨fun k => (Work.Drive.linBase A k).trans (Work.Drive.classEquiv ((Work.Drive.blk k) t)),
    1, one_pos, hrank, hgen, ![H0', H1', H2'], 1 / 2, hc₀0, hc₀1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · funext y
      change H0' (0, y) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 0) y
      rw [hH0'0 y]
      exact congrFun (ht0 0) y
    · funext y
      change H1' (0, y) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1) y
      rw [hH1'0 y]
      exact congrFun (ht0 1) y
    · funext y
      change H2' (0, y) = Work.Drive.planeClassMap
        (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2) y
      rw [hH2'0 y]
      exact congrFun (ht0 2) y
  · intro k
    fin_cases k
    · funext y
      change H0' (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A 0).trans (Work.Drive.classEquiv ((Work.Drive.blk 0) t))) 1 one_pos)) y
      rw [hH0'1 y]
      exact congrFun (ht1 0) y
    · funext y
      change H1' (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A 1).trans (Work.Drive.classEquiv ((Work.Drive.blk 1) t))) 1 one_pos)) y
      rw [hH1'1 y]
      exact congrFun (ht1 1) y
    · funext y
      change H2' (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart
        ((Work.Drive.linBase A 2).trans (Work.Drive.classEquiv ((Work.Drive.blk 2) t))) 1 one_pos)) y
      rw [hH2'1 y]
      exact congrFun (ht1 2) y
  · change Work.Drive.Meet3Hyp (Projectivization ℝ (Work.Drive.Eucl 3) × ℝ) (Work.Drive.encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H0' (x 2, Work.Drive.pt2 (x 0) (x 1)))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) (1 / 2))
    exact hM0
  · change Work.Drive.Meet3Hyp (Projectivization ℝ (Work.Drive.Eucl 3) × ℝ) (Work.Drive.encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H1' (x 2, Work.Drive.pt2 (x 0) (x 1)))
      (Work.Drive.linRowModel A t 0)
      (Work.Drive.planeClassMap (Work.Drive.refPertBlock Q (Work.Drive.refPlanePres φ lam hlam) u v t 2)) (1 / 2))
    exact hM1
  · change Work.Drive.Meet3Hyp (Projectivization ℝ (Work.Drive.Eucl 3) × ℝ) (Work.Drive.encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H2' (x 2, Work.Drive.pt2 (x 0) (x 1)))
      (Work.Drive.linRowModel A t 0) (Work.Drive.linRowModel A t 1) (1 / 2))
    exact hM2

end

end Work.Drive
