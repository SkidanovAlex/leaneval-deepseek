import Mathlib
import Submission.Work.Drive.sweepTripleRot
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.sweepTripleSource
import Submission.Work.Drive.sweepTripleLocus
import Submission.Work.Drive.exists_meet3Hyp_of_good_family
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.goodPair_pertChart_exists_near
import Submission.Work.Drive.chartShiftHsurj

/-!
# The joint genericity of the design's triple with a *reference* third plane

This is the reference-triple analogue of `Work.Drive.exists_meet3Hyp_and_goodAt_sweepRotFam`
(`Submission/Work/Drive/meet3HypAndGoodAt.lean`): instead of three rotated presentations
`rotPresentation Q (a j)` of one chart, the third block of the family is an **arbitrary** plane
presentation `R` (in the application: the linear reference plane `diskPlane (linPlaneChart φ lam hlam)`
of `hn2`), while the first two blocks are the rotated presentations of `Q` at the two angles `u`, `v`
of the antisymmetry computation.

The proof is the same as that of the design's version: the two pair-goodness conditions at the pairs
`(0,1)`, `(1,0)` are *open dense* on `𝔼¹²` (`Work.Drive.goodPair_pertChart_isOpen`,
`Work.Drive.goodPair_pertChart_exists_near`), and the triple genericity inside a ball around a small
parameter of that open dense set is the Sard assembly `Work.Drive.exists_meet3Hyp_of_good_family`
applied to the translated family `τ ↦ G (s + τ)`.  Everything else (`sweepLocus`,
`isCompact_sweepLocus`, `exists_eps_source_sweepChartFam`, `hsurj_sweepChartFam`,
`contMDiff_sweepChartSlice_of_family`, `contMDiff_sweepChartFam`) is generic in the plane data `P`,
so only the two plane clauses (`hP 2`, `hPseam 2`) differ from the design's version, where they were
the rotated presentations.

There is no name clash with the design's file: `PairIdx` is not introduced here (the two conditions are
handled as an explicit intersection).
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 40000000
set_option linter.style.haveILetI false

noncomputable section

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_joint : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **The joint genericity of the reference triple**: a single parameter of arbitrarily small norm at
which the three chart-perturbed clamped sweeps of the *reference* triple
`(rotPresentation Q u, rotPresentation Q v, R)` satisfy `Meet3Hyp` and both ordered pairs `(0,1)`,
`(1,0)` are `GoodAt` at the corresponding blocks. -/
theorem exists_meet3Hyp_and_goodAt_refTriple
    {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (c : Fin 3 → ℝ) (hc : ∀ k : Fin 3, 0 < c k)
    (hcdist : ∀ k k' : Fin 3, c k = c k' → k = k') (u v : UnitAddCircle)
    (R : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hR : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) R)
    (hRseam : ∀ y : EuclideanSpace ℝ (Fin 2),
      Work.Drive.onSeam2 y → R y = R (Work.Drive.seamInv2 y))
    (p : Work.Drive.CappingSpace)
    (hloc : ∀ y ∈ Submission.Drive.unitBox 8,
      Work.Drive.TParity.meet3
        (Work.Drive.sweepChartFam
          ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c 0) y →
      ∀ k : Fin 3,
        Work.Drive.sweepChartFam
          ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c 0 k
          (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε' ∧
        Work.Drive.Meet3Hyp Work.Drive.CappingSpace
          (Work.Drive.sweepChartFam
            ![Work.Drive.rotPresentation Q u, Work.Drive.rotPresentation Q v, R] Ξ c t) ∧
        Work.Drive.GoodAt Ξ Q (c 1) (v - u) (Work.Drive.blk 0 t, Work.Drive.blk 1 t) ∧
        Work.Drive.GoodAt Ξ Q (c 0) (u - v) (Work.Drive.blk 1 t, Work.Drive.blk 0 t) := by
  intro ε' hε'
  classical
  -- ## 0. notation: the reference triple and its family of triples
  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace :=
    ![rotPresentation Q u, rotPresentation Q v, R]
  have hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k) := by
    intro k
    fin_cases k
    · simpa [P] using contMDiff_rotPresentation Q u (contMDiff_diskPlane (Q := Q) hQ.1)
    · simpa [P] using contMDiff_rotPresentation Q v (contMDiff_diskPlane (Q := Q) hQ.1)
    · simpa [P] using hR
  have hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k y = P k (seamInv2 y) := by
    intro k y hy
    fin_cases k
    · simpa [P] using rotPresentation_seamInv Q hQ.2 u y hy
    · simpa [P] using rotPresentation_seamInv Q hQ.2 v y hy
    · simpa [P] using hRseam y hy

  let G : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun t k x => sweepChartFam P Ξ c t k x
  have hslice : ∀ k' : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3) =>
        sweepChartSlice P Ξ c k' q.1 q.2) :=
    fun k' => contMDiff_sweepChartSlice_of_family hΞ hP c k'
  have hGsm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) :=
    fun k => contMDiff_sweepChartFam P Ξ c hslice k
  have hGcont : ∀ k : Fin 3, Continuous (fun q : EuclideanSpace ℝ (Fin 12) ×
      EuclideanSpace ℝ (Fin 3) => G q.1 k q.2) := fun k => (hGsm k).continuous
  -- ## 1. the six pair goodness conditions are open and dense
  have hOpenPair : ∀ (c' : ℝ) (w : UnitAddCircle),
      IsOpen {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c' w q} :=
    fun c' w => goodPair_pertChart_isOpen (Ξ := Ξ) (Q := Q) hΞ hQ.1 c' w
  have hDensePair : ∀ (c' : ℝ) (w : UnitAddCircle),
      Dense {q : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) | GoodAt Ξ Q c' w q} := by
    intro c' w
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨dp, hdp, hg⟩ :=
      goodPair_pertChart_exists_near (Ξ := Ξ) (Q := Q) hΞ hQ.1 c' w x.1 x.2 r hr
    refine ⟨(x.1 + dp, x.2), ⟨?_, hg⟩⟩
    have h1 : dist (x.1 + dp) x.1 = ‖dp‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    have h2 : dist x.2 x.2 = 0 := dist_self _
    have hd : dist ((x.1 + dp, x.2) : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))
        (x.1, x.2) = ‖dp‖ := by
      rw [Prod.dist_eq, h1, h2, max_eq_left (norm_nonneg dp)]
    rw [Metric.mem_ball, hd]
    exact hdp
  -- the two pair conditions at the parameters of the blocks `0`, `1`
  let A : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 1) (v - u) (blk 0 t, blk 1 t)}
  let B : Set (EuclideanSpace ℝ (Fin 12)) :=
    {t | GoodAt Ξ Q (c 0) (u - v) (blk 1 t, blk 0 t)}
  have hAopen : IsOpen A := by
    rw [show A = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q'} from rfl]
    exact IsOpen.preimage (((blk 0).continuous.prodMk (blk 1).continuous))
      (hOpenPair (c 1) (v - u))
  have hBopen : IsOpen B := by
    rw [show B = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q'} from rfl]
    exact IsOpen.preimage (((blk 1).continuous.prodMk (blk 0).continuous))
      (hOpenPair (c 0) (u - v))
  have hAdense : Dense A := by
    have hsurj : Function.Surjective ((blk 0).prod (blk 1)) := by
      rintro ⟨x, y⟩
      refine ⟨blkSpan 0 x + blkSpan 1 y, ?_⟩
      have h1 : blk 0 (blkSpan 0 x + blkSpan 1 y) = x := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), add_zero]
      have h2 : blk 1 (blkSpan 0 x + blkSpan 1 y) = y := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), zero_add]
      rw [ContinuousLinearMap.prod_apply]
      exact Prod.ext h1 h2
    have hopen : IsOpenMap (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) :=
      ContinuousLinearMap.isOpenMap ((blk 0).prod (blk 1)) hsurj
    rw [show A = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 0 t, blk 1 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 1) (v - u) q'} from rfl]
    exact (hDensePair (c 1) (v - u)).preimage hopen
  have hBdense : Dense B := by
    have hsurj : Function.Surjective ((blk 1).prod (blk 0)) := by
      rintro ⟨x, y⟩
      refine ⟨blkSpan 1 x + blkSpan 0 y, ?_⟩
      have h1 : blk 1 (blkSpan 1 x + blkSpan 0 y) = x := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 0) (j := 1) (by decide), add_zero]
      have h2 : blk 0 (blkSpan 1 x + blkSpan 0 y) = y := by
        rw [map_add, blk_blkSpan, blk_blkSpan_of_ne (k := 1) (j := 0) (by decide), zero_add]
      rw [ContinuousLinearMap.prod_apply]
      exact Prod.ext h1 h2
    have hopen : IsOpenMap (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) :=
      ContinuousLinearMap.isOpenMap ((blk 1).prod (blk 0)) hsurj
    rw [show B = (fun t : EuclideanSpace ℝ (Fin 12) => (blk 1 t, blk 0 t)) ⁻¹'
        {q' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) |
          GoodAt Ξ Q (c 0) (u - v) q'} from rfl]
    exact (hDensePair (c 0) (u - v)).preimage hopen
  have hOpenInter : IsOpen (A ∩ B) := hAopen.inter hBopen
  have hDenseInter : Dense (A ∩ B) := hAdense.inter_of_isOpen_right hBdense hBopen
  -- ## 2. the compact chart-containment set of the *base* configuration
  have hCont0 : ∀ k : Fin 3, Continuous (fun y : EuclideanSpace ℝ (Fin 9) =>
      G 0 k (Work.Drive.TParity.bPartC k y)) := fun k =>
    (hGcont k).comp (continuous_const.prodMk (Work.Drive.TParity.bPartC k).continuous)
  have hLocusK : IsCompact (sweepLocus P Ξ c) := isCompact_sweepLocus P Ξ c hΞ hP
  have hVopen : IsOpen {y : EuclideanSpace ℝ (Fin 9) | ∀ k : Fin 3,
      G 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.eventually_all.mpr fun k => ?_
    exact ((hCont0 k).continuousAt).preimage_mem_nhds ((chr p).open_source.mem_nhds (hy k))
  have hLV : sweepLocus P Ξ c ⊆ {y : EuclideanSpace ℝ (Fin 9) | ∀ k : Fin 3,
      G 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source} :=
    fun y hy => hloc y hy.1 hy.2
  obtain ⟨δ, hδpos, hδ⟩ := hLocusK.exists_cthickening_subset_open hVopen hLV
  let K : Set (EuclideanSpace ℝ (Fin 9)) := Metric.cthickening δ (sweepLocus P Ξ c)
  have hK : IsCompact K := hLocusK.cthickening
  have hsrcK : ∀ y ∈ K, ∀ k : Fin 3,
      G 0 k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source := fun y hy k => hδ hy k
  have hbase0 : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G 0) y → y ∈ interior K := by
    intro y hy hmeet
    have hyL : y ∈ sweepLocus P Ξ c := ⟨hy, hmeet⟩
    exact interior_maximal (Metric.thickening_subset_cthickening δ (sweepLocus P Ξ c))
      Metric.isOpen_thickening (Metric.self_subset_thickening hδpos (sweepLocus P Ξ c) hyL)
  -- ## 3. the uniform chart containment near `0`
  obtain ⟨εs, hεspos, hεs⟩ := exists_eps_source_sweepChartFam P Ξ c hΞ hP K hK p hsrcK
  -- ## 4. the perturbed locus stays inside `K` near `0`
  have hevK : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin 12)),
      ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
        Work.Drive.TParity.meet3 (G t) y → y ∈ interior K :=
    eventually_meet3_subset_of_isOpen G hGcont (U := interior K) isOpen_interior hbase0
  rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hevK
  obtain ⟨η₀, hη₀pos, hη₀⟩ := hevK
  -- ## 5. a small parameter satisfying both pair conditions
  set η : ℝ := min (η₀ / 2) (min (εs / 2) (ε' / 4)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hη_η₀ : η ≤ η₀ / 2 := by rw [hηdef]; exact min_le_left _ _
  have hη_εs : η ≤ εs / 2 := by
    rw [hηdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_ε' : η ≤ ε' / 4 := by
    rw [hηdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨s, hsPair, hsnorm⟩ : ∃ s : EuclideanSpace ℝ (Fin 12),
      s ∈ A ∩ B ∧ ‖s‖ < η := by
    rw [Metric.dense_iff] at hDenseInter
    obtain ⟨s, hs, hsd⟩ := hDenseInter 0 η hηpos
    exact ⟨s, hsd, by rwa [Metric.mem_ball, dist_zero_right] at hs⟩
  have hsnorm_η₀ : ‖s‖ < η₀ := by linarith
  have hsnorm_εs : ‖s‖ < εs / 2 := by linarith
  have hsnorm_ε' : ‖s‖ < ε' / 4 := by linarith
  obtain ⟨δP, hδPpos, hδPsub⟩ := Metric.isOpen_iff.mp hOpenInter s hsPair
  -- ## 6. the translated family and its data
  let Gs : EuclideanSpace ℝ (Fin 12) → Fin 3 → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun τ k x => G (s + τ) k x
  set ετ : ℝ := min (min δP (εs - ‖s‖)) ((ε' - ‖s‖) / 2) with hετdef
  have hετpos : 0 < ετ := by
    rw [hετdef]
    exact lt_min (lt_min hδPpos (by linarith)) (by linarith)
  have hετ_δP : ετ ≤ δP := le_trans (min_le_left _ _) (min_le_left _ _)
  have hετ_εs : ετ ≤ εs - ‖s‖ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hετ_ε' : ετ ≤ (ε' - ‖s‖) / 2 := min_le_right _ _
  have hst_εs : ∀ τ : EuclideanSpace ℝ (Fin 12), ‖τ‖ < ετ → ‖s + τ‖ < εs := by
    intro τ hτ
    have h1 : ‖τ‖ < εs - ‖s‖ := lt_of_lt_of_le hτ hετ_εs
    calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
      _ < ‖s‖ + (εs - ‖s‖) := by linarith
      _ = εs := by ring
  have hbaseS : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (Gs 0) y → y ∈ interior K := by
    intro y hy hmeet
    exact hη₀ (by rw [Metric.mem_ball, dist_zero_right]; exact hsnorm_η₀) y hy
      (by simpa only [Gs, add_zero] using hmeet)
  have hGs_sm : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => Gs q.1 k q.2) := by
    intro k
    have htrans : ContMDiff (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => (s + q.1, q.2)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hcomp := (hGsm k).comp htrans
    simpa only [Function.comp_def, Gs] using hcomp
  have hGs_slice : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3),
      ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Gs τ k) := by
    intro τ k
    have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ((s + τ, x) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := (hGsm k).comp (contMDiff_iff_contDiff.mpr hφ)
    simpa only [Function.comp_def, Gs, G, sweepChartFam_apply] using hcomp
  have hGs_seam : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (k : Fin 3)
      (x : EuclideanSpace ℝ (Fin 3)), onSeam x → Gs τ k x = Gs τ k (seamInv x) := by
    intro τ k x hx
    have hinst : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
        (fun z => Ξ (blk k (s + τ)) (P k z)) y
          = (fun z => Ξ (blk k (s + τ)) (P k z)) (seamInv2 y) :=
      fun y hy => congrArg (Ξ (blk k (s + τ))) (hPseam k y hy)
    have h := clampedSweep_seamInv (c k) (fun r => 1 - r)
      (fun z => Ξ (blk k (s + τ)) (P k z)) hinst x hx
    simpa only [Gs, G, sweepChartFam_apply, Function.comp_def] using h
  have hGs_contain : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖τ‖ < ετ → y ∈ K → ∀ k : Fin 3,
        Gs τ k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source := fun τ y hτ hy k =>
    hεs (s + τ) y (hst_εs τ hτ) hy k
  have hGs_surj : ∀ (τ : EuclideanSpace ℝ (Fin 12)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖τ‖ < ετ → y ∈ K → Work.Drive.TParity.chartDiff3 p (Gs τ) y = 0 →
      Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
        Work.Drive.TParity.chartDiff3 p (Gs τ') y) τ) := by
    intro τ y hτ hy hz
    have hst := hst_εs τ hτ
    have hsrc : ∀ k : Fin 3, G (s + τ) k (Work.Drive.TParity.bPartC k y) ∈ (chr p).source :=
      hεs (s + τ) y hst hy
    have hz' : Work.Drive.TParity.chartDiff3 p (G (s + τ)) y = 0 := by
      simpa only [Gs] using hz
    have hsurj := hsurj_sweepChartFam P Ξ c hΞ hc hcdist hslice K p hεs (s + τ) y hst hy hz'
    have hsm := contDiffAt_chartDiff3_family_fin 12 G hGsm p (s + τ) hsrc
    have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          ((t', y) : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9))) (s + τ) :=
      contDiffAt_id.prodMk contDiffAt_const
    have hsm'' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 9) =>
          Work.Drive.TParity.chartDiff3 p (G q.1) q.2) ∘
          (fun t' : EuclideanSpace ℝ (Fin 12) => (t', y))) (s + τ) :=
      hsm.comp (s + τ) hinner
    have hsm' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p (G t') y) (s + τ) := hsm''
    have hF : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin 12) =>
        Work.Drive.TParity.chartDiff3 p (G t') y)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p (G t') y) (s + τ)) (s + τ) :=
      (hsm'.differentiableAt top_ne_zero_joint).hasFDerivAt
    have hshift : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 12) => s + τ')
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 12))) τ := by
      simpa using (hasFDerivAt_id τ).const_add s
    have hcomp := hF.comp τ hshift
    rw [ContinuousLinearMap.comp_id] at hcomp
    have heq : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p (Gs τ') y) τ
        = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin 12) =>
          Work.Drive.TParity.chartDiff3 p (G t') y) (s + τ) := by
      have h1 : (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            Work.Drive.TParity.chartDiff3 p (Gs τ') y)
          = (fun τ' : EuclideanSpace ℝ (Fin 12) =>
            Work.Drive.TParity.chartDiff3 p (G (s + τ')) y) := rfl
      rw [h1]
      exact hcomp.fderiv
    rw [heq]
    exact hsurj
  -- ## 7. the Sard assembly at the translated base
  obtain ⟨τ, hτ, hM⟩ := exists_meet3Hyp_of_good_family 12 Gs hGs_sm hGs_slice hGs_seam K hK
    hbaseS p hετpos hGs_contain hGs_surj ετ hετpos
  -- ## 8. the conclusion
  refine ⟨s + τ, ?_, hM, ?_, ?_⟩
  · have h1 : ‖τ‖ < (ε' - ‖s‖) / 2 := lt_of_lt_of_le hτ hετ_ε'
    calc ‖s + τ‖ ≤ ‖s‖ + ‖τ‖ := norm_add_le _ _
      _ < ‖s‖ + (ε' - ‖s‖) / 2 := by linarith
      _ < ε' := by linarith
  · have hmem : s + τ ∈ A ∩ B := by
      refine hδPsub ?_
      rw [Metric.mem_ball, dist_eq_norm]
      rw [add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP
    exact hmem.1
  · have hmem : s + τ ∈ A ∩ B := by
      refine hδPsub ?_
      rw [Metric.mem_ball, dist_eq_norm]
      rw [add_sub_cancel_left]
      exact lt_of_lt_of_le hτ hετ_δP
    exact hmem.2

end

end Work.Drive
