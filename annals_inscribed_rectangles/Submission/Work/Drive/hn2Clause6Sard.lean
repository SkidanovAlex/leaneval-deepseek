import Mathlib
import Submission.Work.Drive.exists_meet3Hyp_opens_near_zero
import Submission.Work.Drive.isOpen_T6GenAtDBox_refTriple
import Submission.Work.Drive.dense_T6GenAtDBox_refTriple
import Submission.Work.Drive.mixedGoodPairs_openDense
import Submission.Work.Drive.threeBlock_dense_point
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.refTripleClause6Data
import Submission.Work.Drive.refTripleLevelBand
import Submission.Work.Drive.transport_disins_reference_block0
import Submission.Work.Drive.refTripleRows
import Submission.Work.Drive.t6GenAtDBox_refTriple_block1_bundles
import Submission.Work.Drive.linBaseRealizesChart

/-!
# The enriched Sard of the `hn2` clause 6

`Work.Drive.refTripleAt_blockT6At_of_data` (`Drive/refTripleClause6Data.lean`) proves clause 6 of the
`hn2` reference-triple producer from, among others, the four *per-parameter* data

* `hgen0`/`hgen1` — the at-one-parameter transport bundles `T6GenAtDBox` at block `0` (core chart = the
  perturbed rotated presentation at angle `u`; planes = the perturbed rotated presentation at angle `v`
  at block `1` and the disk plane `diskPlane QR` at block `2`) and at block `1` (core chart at angle
  `v`; planes at block `0` with angle `u` — level `cblk 0` — and the disk plane at block `2` — level
  `cblk 2`),
* `hgp0`/`hgp1` — the two *mixed* `GoodPair`s (the `(F1)` lane's configurations),

all at a *small* parameter `t`, together with the ten "small `t`" data (`hdisj*`, `hlev*`), the
parametric oddness `hF1` of the mixed factors and the sweeps' `Meet3Hyp` + the two coupled `GoodAt`s.

The last two come from the Sard `Work.Drive.exists_sweepGenericity_opens` unrestricted / the
`near-zero` engine: **one** call produces `t`, the `Meet3Hyp` of the reference triple's sweeps, the two
coupled `GoodAt`s and the membership `t ∈ A` for a prescribed open-dense condition set `A` (the
class-level rows of the `hodd` chapter).

This module *enriches* that call: the same engine is run with
`A' := A ∩ HGen0Set ∩ HGen1Set ∩ MixedGPSet`, which is open and accumulates at `0` (the three
conditions are open — `isOpen_T6GenAtDBox_refTriple`, the block-`1` bundle producer,
`mixedGoodPairs_openDense` — and jointly accumulate at `0` by `threeBlock_dense_point`).  The engine
uses only the openness of `A'` and the accumulation `hA0`, so the enrichment is free.

The block-`1` bundle producer is the *only* genuinely new input; it is taken here as a pair of
hypotheses (`hopen1`, `hdense1`) so that this module is independent of the producer's proof, and it is
instantiated at the end (`exists_sweepGenericity_clause6`) once
`Work.Drive.t6GenAtDBox_refTriple_block1_bundles` is available.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## 1. The three enrichment conditions -/

/-- **The block-`0` transport bundle** of the reference triple `![P_u, P_v, diskPlane QR]` at the
levels `cblk 1`, `cblk 2`: the core chart is the perturbed rotated presentation at angle `u` and block
`0`, the two planes are the perturbed rotated presentation at angle `v` (block `1`) and the disk plane
`diskPlane QR` (block `2`). -/
def HGen0Set (Q QR : ℂ → CappingSpace) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | T6GenAtDBox (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 1 t) (rotPresentation Q v y))
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 2 t) (diskPlane QR y))
        (cblk 1) (cblk 2)}

/-- **The block-`1` transport bundle** of the reference triple: the core chart is the perturbed rotated
presentation at angle `v` and block `1`, the two planes are the perturbed rotated presentation at angle
`u` (block `0`, level `cblk 0`) and the disk plane `diskPlane QR` (block `2`, level `cblk 2`). -/
def HGen1Set (Q QR : ℂ → CappingSpace) (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | T6GenAtDBox (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 0 t) (rotPresentation Q u y))
        (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 2 t) (diskPlane QR y))
        (cblk 0) (cblk 2)}

/-- **The two mixed `GoodPair`s** of the reference triple at truncation level `c₂`. -/
def MixedGPSet (Q QR : ℂ → CappingSpace) (u v : UnitAddCircle) (c₂ : ℝ) :
    Set (EuclideanSpace ℝ (Fin 12)) :=
  {t | GoodPair (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
          (fun z : ℂ => chartPert (blk 2 t) (QR z)) c₂ ∧
        GoodPair (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
          (fun z : ℂ => chartPert (blk 2 t) (QR z)) c₂}

/-! ## 2. Openness and density of the three sets -/

/-- The block-`0` set is the set of the proved openness statement
`Work.Drive.isOpen_T6GenAtDBox_refTriple`, in the `HGen0Set` vocabulary. -/
lemma isOpen_HGen0Set {Q QR : ℂ → CappingSpace} (hQ : IsChartData Q) (hQR : IsSmoothChart QR)
    (hQRseam : ∀ z : ℂ, ‖z‖ = 1 → QR (-z) = QR z)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k) :
    IsOpen (HGen0Set Q QR u v cblk) := by
  exact isOpen_T6GenAtDBox_refTriple (Q := Q) hQ (QR := QR) hQR hQRseam u v cblk hcpos

/-- The block-`0` set satisfies the density statement
`Work.Drive.dense_T6GenAtDBox_refTriple`, in the `HGen0Set` vocabulary. -/
lemma dense_HGen0Set {Q QR : ℂ → CappingSpace} (hQ : IsChartData Q) (hQR : IsSmoothChart QR)
    (hQRseam : ∀ z : ℂ, ‖z‖ = 1 → QR (-z) = QR z)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → cblk 2 < levelOf (Q z))
    (hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (QR z) > cblk 2) :
    ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 0 x) 0 → ∀ ε : ℝ, 0 < ε →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧ t ∈ HGen0Set Q QR u v cblk := by
  intro x hx hx0 ε hε
  obtain ⟨t, ht, hb⟩ := dense_T6GenAtDBox_refTriple (Q := Q) hQ (QR := QR) hQR hQRseam
    u v cblk hcpos hlev hlevR x hx hx0 ε hε
  exact ⟨t, ht, hb⟩

/-- The two mixed `GoodPair`s are an open condition. -/
lemma isOpen_MixedGPSet {Q QR : ℂ → CappingSpace} (hQ : IsSmoothChart Q) (hQR : IsSmoothChart QR)
    (u v : UnitAddCircle) (c₂ : ℝ) :
    IsOpen (MixedGPSet Q QR u v c₂) :=
  (mixedGoodPairs_openDense (Q := Q) (Q₂ := QR) hQ hQR u v c₂).1

/-- A dense point of the two mixed `GoodPair`s, arbitrarily close to any prescribed parameter. -/
lemma dense_MixedGPSet {Q QR : ℂ → CappingSpace} (hQ : IsSmoothChart Q) (hQR : IsSmoothChart QR)
    (u v : UnitAddCircle) (c₂ : ℝ) :
    ∀ (s : EuclideanSpace ℝ (Fin 12)) (δ : ℝ), 0 < δ →
      ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - s‖ < δ ∧ t ∈ MixedGPSet Q QR u v c₂ :=
  fun s δ hδ => (mixedGoodPairs_openDense (Q := Q) (Q₂ := QR) hQ hQR u v c₂).2 s δ hδ

/-! ## 3. The enriched Sard -/

/-- **The enriched Sard of the `hn2` clause 6.**  For a plane chart `Q` of `γ`, a level `c` below the
chart's disk levels, the two angles `u`, `v`, a reference level `lam` above `Q`'s levels and a linear
chart triple `φ` (whose second chart presents the reference plane), the Sard of
`exists_meet3Hyp_opens_near_zero` — run on the *enriched* open set
`A ∩ HGen0Set ∩ HGen1Set ∩ MixedGPSet` — produces, for every `ε > 0`, a parameter `t` of norm `< ε` at
which the reference triple has levels above `c / 2`, its sweeps are a `Meet3Hyp` triple, the two coupled
`GoodAt`s hold, and the two transport bundles and the two mixed `GoodPair`s hold.

`A` is the class-level-rows condition set of the `hodd` chapter (an open set dense at every point of the
closed unit ball).  The block-`1` bundle is an input (`hopen1`, `hdense1`), produced by
`Work.Drive.t6GenAtDBox_refTriple_block1_bundles`. -/
theorem exists_sweepGenericity_clause6_of {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (u v : UnitAddCircle) (lam : ℝ) (hlam : 0 < lam) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    (hopen1 : IsOpen (HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4]))
    (hdense1 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 1 x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          t ∈ HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4])
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
          < levelOf (chartPert (blk k t)
              (refTriple Q (refPlanePres φ lam hlam) u v k y))) ∧
      Meet3Hyp CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1) (v - u)
        (blk 0 t, blk 1 t) ∧
      GoodAt (fun s p => chartPert s p) Q ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0) (u - v)
        (blk 1 t, blk 0 t) ∧
      HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t ∧
      HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t ∧
      MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
        ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) t := by
  classical
  obtain ⟨εl, hεl, hlvl⟩ := exists_levelBound_at_one hQ c hc hcbot u v lam hlam φ habove
  -- ## the data of the reference plane chart
  have hQRsm : IsSmoothChart (linPlaneChart (φ 2) lam hlam) := linPlaneChart_contMDiff (φ 2) lam hlam
  have hQRseam : ∀ z : ℂ, ‖z‖ = 1 → linPlaneChart (φ 2) lam hlam (-z)
      = linPlaneChart (φ 2) lam hlam z := fun z hz => linPlaneChart_neg (φ 2) lam hlam hz
  have hQc : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hcpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hcdist : ∀ k k' : Fin 3, (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k
      = (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k' → k = k' := dblk_distinct hc
  have hlevc : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 < levelOf (Q z) := by
    intro z hz
    have h := hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [h2]; linarith
  have hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (linPlaneChart (φ 2) lam hlam z)
      > (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 := by
    intro z hz
    have hL : levelOf (linPlaneChart (φ 2) lam hlam z) = lam :=
      level_linPlaneChart (φ 2) lam hlam z
    have hcl : c < lam := c_lt_lam hcbot habove
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [hL, h2]; linarith
  -- ## the three sets are open
  have h0open : IsOpen (HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)) :=
    isOpen_HGen0Set hQc hQRsm hQRseam u v _ hcpos
  have hgpopen : IsOpen (MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
      ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)) :=
    isOpen_MixedGPSet hQsm hQRsm u v _
  -- ## the third set of the margined iteration: `A ∩ MixedGP`, open and dense everywhere
  set B : Set (EuclideanSpace ℝ (Fin 12)) :=
    A ∩ MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
      ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) with hB
  have hBopen : IsOpen B := hAopen.inter hgpopen
  have hBdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ B, ‖t - s‖ < δ := by
    intro s hs δ hδ
    obtain ⟨t₀, ht₀A, ht₀⟩ := hAdense s hs (δ / 2) (by linarith)
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds ht₀A)
    have hδ2 : 0 < min (δ / 2) r := lt_min (by linarith) hrpos
    obtain ⟨t, ht, htg⟩ := dense_MixedGPSet hQsm hQRsm u v
      ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) t₀ (min (δ / 2) r) hδ2
    have htA : t ∈ A := hrsub (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le ht (min_le_right _ _))
    refine ⟨t, ⟨htA, htg⟩, ?_⟩
    have h1 : ‖t - s‖ ≤ ‖t - t₀‖ + ‖t₀ - s‖ := by
      have h := norm_add_le (t - t₀) (t₀ - s)
      rwa [sub_add_sub_cancel] at h
    have h2 : ‖t - t₀‖ < δ / 2 := lt_of_lt_of_le ht (min_le_left _ _)
    linarith
  -- ## the margined iteration: points of `HGen0 ∩ HGen1 ∩ B` of arbitrarily small norm
  let A3 : Fin 3 → Set (EuclideanSpace ℝ (Fin 12)) :=
    ![HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ),
      HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ),
      B]
  have hA3open : ∀ k : Fin 3, IsOpen (A3 k) := by
    intro k
    fin_cases k <;> simp only [A3]
    · exact h0open
    · exact hopen1
    · exact hBopen
  have hA3dense : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 12)), ‖x‖ ≤ 1 →
      0 ≤ (blk k x) 0 → ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ A3 k ∧ ‖y - x‖ < δ := by
    intro k x hx hxk δ hδ
    fin_cases k <;> simp only [A3]
    · obtain ⟨y, hy, hymem⟩ :=
        dense_HGen0Set hQc hQRsm hQRseam u v _ hcpos hlevc hlevR x hx (by simpa using hxk) δ hδ
      exact ⟨y, hymem, hy⟩
    · obtain ⟨y, hy, hymem⟩ := hdense1 x hx (by simpa using hxk) δ hδ
      exact ⟨y, hymem, hy⟩
    · exact hBdense x (by simpa using hx) δ hδ
  have hacc : ∀ ρ : ℝ, 0 < ρ → ∃ s : EuclideanSpace ℝ (Fin 12), ‖s‖ < ρ ∧
      s ∈ HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∧
      s ∈ HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∧ s ∈ B := by
    intro ρ hρ
    obtain ⟨s, hs, hsall⟩ := threeBlock_dense_point A3 hA3open hA3dense ρ hρ
    exact ⟨s, hs, hsall 0, hsall 1, hsall 2⟩
  -- ## the enriched set, open and accumulating at `0`
  set A' : Set (EuclideanSpace ℝ (Fin 12)) :=
    A ∩ HGen0Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∩
      HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) ∩
      MixedGPSet Q (linPlaneChart (φ 2) lam hlam) u v
        ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) with hA'
  have hA'open : IsOpen A' := ((hAopen.inter h0open).inter hopen1).inter hgpopen
  have hA'0 : ∀ δ : ℝ, 0 < δ → ∃ t ∈ A', ‖t‖ < δ := by
    intro δ hδ
    obtain ⟨s, hs, hs0, hs1, hsB⟩ := hacc δ hδ
    exact ⟨s, ⟨⟨⟨hsB.1, hs0⟩, hs1⟩, hsB.2⟩, hs⟩
  -- ## the enriched Sard
  obtain ⟨t, ht, htA', hM, hg01, hg10⟩ :=
    exists_meet3Hyp_opens_near_zero (Q := Q) hQc (fun s p => chartPert s p)
      (isChartPert_chartPert Q) (![c / 2, c / 3, c / 4]) hcpos hcdist u v
      (refPlanePres φ lam hlam) (refPlanePres_contMDiff φ lam hlam)
      (refPlanePres_seam φ lam hlam)
      (richness_sweepChartFam (Q := Q) (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) (![c / 2, c / 3, c / 4]) (isChartPert_chartPert Q) hcpos hcdist
        (refTriple_contMDiff Q hQsm φ lam hlam u v))
      A' hA'open hA'0 (min ε εl) (lt_min hε hεl)
  refine ⟨t, lt_of_lt_of_le ht (min_le_left _ _), htA'.1.1.1,
    hlvl t (lt_of_lt_of_le ht (min_le_right _ _)), hM, hg01, hg10,
    htA'.1.1.2, htA'.1.2, htA'.2⟩


/-! ## 4. The producer: `RefTripleAt` minus the class-parity clause

`Work.Drive.RefTripleAt` (`Drive/refTripleOneT.lean`) bundles everything the `hn2` endpoint consumes at
one parameter.  Its *third* conjunct (`Odd (classTripleSet …).ncard`, the `hodd` chapter) is the only
one this module cannot produce; the other five are assembled here from the enriched Sard (§3), the
"small `t`" producers of `Drive/refTripleRows.lean`, `Drive/transport_disins_reference_block0.lean` and
`Drive/refTripleLevelBand.lean`, and the two halves
`Work.Drive.refTripleAt_blockT6At_of_data` + `Work.Drive.exists_blockFactors_of_T6` of the transport. -/

/-- **The Sard-produced part of `RefTripleAt`**: the level bound, the sweeps' `Meet3Hyp`, the two
coupled `GoodAt`s and the block-factor data (with the reference block's factors even and the two mixed
factors odd) — everything `RefTripleAt` contains *except* the class-triple parity. -/
def RefTripleGenericity (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf (chartPert (blk k t) (refTriple Q R u v k y))) ∧
    Meet3Hyp CappingSpace (sweepChartFam (refTriple Q R u v) (fun s p => chartPert s p) cblk t) ∧
    GoodAt (fun s p => chartPert s p) Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
    GoodAt (fun s p => chartPert s p) Q (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
    ∃ g : Fin 3 → Fin 3 → ℕ,
      g 0 1 = CntAt (fun s p => chartPert s p) Q (cblk 1) (v - u) (blk 0 t, blk 1 t) ∧
      g 1 0 = CntAt (fun s p => chartPert s p) Q (cblk 0) (u - v) (blk 1 t, blk 0 t) ∧
      (∀ k : Fin 3,
        Odd (topBdryMeet CappingSpace
          (sweepChartFam (refTriple Q R u v) (fun s p => chartPert s p) cblk t) k).ncard ↔
          (Odd (g k (k + 1)) ∧ Odd (g k (k + 2)))) ∧
      Even (g 2 0) ∧ Even (g 2 1) ∧ Odd (g 0 2) ∧ Odd (g 1 2)

/-- **`RefTripleGenericity` is `RefTripleAt` without its class-parity clause.** -/
theorem refTripleAt_iff_genericity (Q : ℂ → CappingSpace) (R : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12)) :
    RefTripleAt (Ξ := fun s p => chartPert s p) Q R u v cblk t ↔
      RefTripleGenericity Q R u v cblk t ∧
        Odd (classTripleSet (fun k z => chartPert (blk k t) (refTriple Q R u v k z))).ncard := by
  unfold RefTripleAt RefTripleGenericity
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨⟨a, b, d, e, f⟩, c⟩
  · rintro ⟨⟨a, b, d, e, f⟩, c⟩
    exact ⟨a, b, c, d, e, f⟩

/-- **The producer of the Sard-produced part of the `hn2` reference-triple data.**  All the data of
`Work.Drive.RefTripleGenericity` at a parameter `t` of norm `< ε` which moreover lies in the prescribed
open-dense condition set `A` (the class-level rows of the `hodd` chapter).

The hypotheses are the node's own data (`hQ`, `hγ`, the truncation level `c` below the chart's disk
levels, the whole-plane disjointness `hdisjZc`, the two angles with `v - u ∈ Zc γ`), the reference-plane
data (`β`, `lam`, `φ`, `habove`), the parametric oddness `hF1` of the two mixed factors at the reference
chart `φ 2` (produced by `Work.Drive.refTriple_mixedFactors` + the φ-chooser
`Work.Drive.exists_triple_chart_of_middle`), and the block-`1` bundle producer (`hopen1`, `hdense1`). -/
theorem exists_refTripleGenericity {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    {β : ℝ} (hβpos : 0 < β) (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (hβlam : β < lam)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))))
    (hopen1 : IsOpen (HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4]))
    (hdense1 : ∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → 0 ≤ (blk 1 x) 0 →
      ∀ ε : ℝ, 0 < ε →
        ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < ε ∧
          t ∈ HGen1Set Q (linPlaneChart (φ 2) lam hlam) u v ![c / 2, c / 3, c / 4])
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      RefTripleGenericity Q (refPlanePres φ lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  classical
  intro ε hε
  have hcblkpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hcblk2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z) := fun z hz =>
    hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  -- ## the small-`t` data of the two configuration blocks
  obtain ⟨r₁, hr₁, h₁⟩ := transport_disins_reference_block0 (hγne := hγne) (Q := Q)
    hQ.1.continuous hβpos hβ
    φ lam hlam hβlam hdisjZc huv c hc hcbot' hcblk2
  obtain ⟨r₂, hr₂, h₂⟩ := transport_disins_reference_block' (hγne := hγne) (Q := Q)
    hQ.1.continuous hβpos hβ
    φ lam hlam hβlam hdisjZc huv c hc hcbot' hcblk2
  -- ## the budget
  set εs : ℝ := min ε (min r₁ (min r₂ (min (Real.log 2) (min δF (Real.log (lam / β) / 4)))))
    with hεs
  have hlogpos : 0 < Real.log (lam / β) := by
    have h1 : 1 < lam / β := (one_lt_div hβpos).mpr hβlam
    exact Real.log_pos h1
  have hεs' : 0 < εs := by
    rw [hεs]
    exact lt_min hε (lt_min hr₁ (lt_min hr₂ (lt_min (Real.log_pos (by norm_num))
      (lt_min hδF (by linarith)))))
  obtain ⟨t, ht, htA, hlev, hM, hg01, hg10, hgen0, hgen1, hgp0, hgp1⟩ :=
    exists_sweepGenericity_clause6_of hQ c hc hcbot u v lam hlam φ habove hopen1 hdense1
      A hAopen hAdense εs hεs'
  have htε : ‖t‖ < ε := lt_of_lt_of_le ht (by rw [hεs]; exact min_le_left _ _)
  have htr₁ : ‖t‖ < r₁ :=
    lt_of_lt_of_le ht (by rw [hεs]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have htr₂ : ‖t‖ < r₂ :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have htlog2 : ‖t‖ < Real.log 2 :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))
  have htlog3 : ‖t‖ < Real.log 3 :=
    lt_trans htlog2 (Real.log_lt_log (by norm_num) (by norm_num))
  have htδF : ‖t‖ < δF :=
    lt_of_lt_of_le ht (by
      rw [hεs]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have htloglam : 2 * ‖t‖ < Real.log (lam / β) := by
    have h : ‖t‖ < Real.log (lam / β) / 4 :=
      lt_of_lt_of_le ht (by
        rw [hεs]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
    linarith
  -- ## the data at `t`
  obtain ⟨hdisj01, hdisj02, hdisj012', _⟩ := h₁ t htr₁
  obtain ⟨hdisj10, hdisj12, hdisj102', _⟩ := h₂ t htr₂
  have hdisj012 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y' := by
    intro y y' h
    exact (Set.disjoint_left.mp hdisj012' ⟨y, rfl⟩) ⟨y', h.symm⟩
  have hdisj102 : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y' := by
    intro y y' h
    exact (Set.disjoint_left.mp hdisj102' ⟨y, rfl⟩) ⟨y', h.symm⟩
  have hlev01 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1
        < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' u rfl rfl htlog3 0 z hz).1
  have hlev02 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2
        < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' u rfl rfl htlog3 0 z hz).2
  have hlev10 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0
        < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))) :=
    fun z hz => levelOf_chartPert_rotCapping_gt_cblk0 c hc hcbot' v rfl htlog2 1 z hz
  have hlev12 : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2
        < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))) :=
    fun z hz => (levelOf_chartPert_rotCapping_gt_cblk c hc hcbot' v rfl rfl htlog3 1 z hz).2
  have hsmall0 : ‖blk 0 t‖ < δF := lt_of_le_of_lt (norm_blk_le 0 t) htδF
  have hsmall1 : ‖blk 1 t‖ < δF := lt_of_le_of_lt (norm_blk_le 1 t) htδF
  have hsmall2 : ‖blk 2 t‖ < δF := lt_of_le_of_lt (norm_blk_le 2 t) htδF
  -- ## the transport at the two blocks
  obtain ⟨hT6₀, hT6₁, hid01, hid10, hmix0, hmix1⟩ :=
    refTripleAt_blockT6At_of_data hQ hγ u v φ lam hlam (![c / 2, c / 3, c / 4]) hcblkpos t
      hM hgen0 hgen1 hdisj01 hdisj02 hdisj012 hlev01 hlev02 hdisj10 hdisj12 hdisj102 hlev10 hlev12
      hδF hF1 hsmall0 hsmall1 hsmall2 hgp0 hgp1
  have hlow : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k
        ≤ levelOf (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k y) := by
    intro k y
    refine le_trans ?_ (le_of_lt (hlev k y))
    fin_cases k
    · exact le_rfl
    · show c / 3 ≤ c / 2
      linarith
    · show c / 4 ≤ c / 2
      linarith
  have hT2 : topBdryMeet CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t) 2 = ∅ :=
    refTriple_topBdryMeet_two_eq_empty hβpos hβ (φ := φ) (lam := lam) hlam hβlam u v
      (cblk := ![c / 2, c / 3, c / 4]) hcblkpos htloglam hlow
  -- ## the block factors
  obtain ⟨g, hg01', hg10', hblock, h20, h21, h02', h12'⟩ :=
    exists_blockFactors_of_T6 (Ξ := fun s p => chartPert s p) (Q := Q)
      (refPlanePres φ lam hlam) u v (![c / 2, c / 3, c / 4]) t
      (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
      (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
      hT6₀ hT6₁ hT2 hid01 hid10 hmix0 hmix1
  exact ⟨t, htε, htA, hlev, hM, hg01, hg10, g, hg01', hg10', hblock, h20, h21, h02', h12'⟩


/-! ## 5. The same producer with the block-`1` bundle producer discharged -/

/-- **`Work.Drive.exists_refTripleGenericity` with no auxiliary hypotheses**: the block-`1` bundle
producer `Work.Drive.t6GenAtDBox_refTriple_block1_bundles` supplies the `hopen1`/`hdense1` inputs.

The only remaining hypotheses are the node's data, the reference-plane data and the `(F1)` parametric
oddness — i.e. **the class-level rows condition set `A` and the class-triple parity are the only things
still missing from `Work.Drive.RefTripleAt`**. -/
theorem exists_refTripleGenericity_noAux {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    {β : ℝ} (hβpos : 0 < β) (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (hβlam : β < lam)
    (habove : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam)
    {δF : ℝ} (hδF : 0 < δF)
    (hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δF → ‖τ₁‖ < δF → ‖τ₂‖ < δF →
        GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
        Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
            ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))))
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
      RefTripleGenericity Q (refPlanePres φ lam hlam) u v
        (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  have hcblkpos : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := dblk_pos hc
  have hlevc : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 < levelOf (Q z) := by
    intro z hz
    have h := hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [h2]; linarith
  have hlevR : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (linPlaneChart (φ 2) lam hlam z)
      > (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 := by
    intro z hz
    have hL : levelOf (linPlaneChart (φ 2) lam hlam z) = lam :=
      level_linPlaneChart (φ 2) lam hlam z
    have hcl : c < lam := c_lt_lam hcbot habove
    have h2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 = c / 4 := rfl
    rw [hL, h2]; linarith
  obtain ⟨hopen1, hdense1⟩ := t6GenAtDBox_refTriple_block1_bundles (Q := Q)
    (IsChartData_of_isPlaneChart hQ) (linPlaneChart_contMDiff (φ 2) lam hlam)
    (fun z hz => linPlaneChart_neg (φ 2) lam hlam hz) u v (![c / 2, c / 3, c / 4]) hcblkpos
    hlevc hlevR
  exact exists_refTripleGenericity hQ hγ c hc hcbot hdisjZc u v huv hβpos hβ φ lam hlam hβlam
    habove hδF hF1 hopen1 hdense1 A hAopen hAdense


/-! ## 6. The full clause-`6` producer: the reference plane, the `(F1)` chart and the Sard -/

/-- **The `hn2` clause-6 producer, with no auxiliary hypothesis.**  From the node's data (the chart
`Q`, the truncation level `c` below the chart's disk levels, the whole-plane disjointness, the two
angles with `v - u ∈ Zc γ`) and the class-rows condition set `A`, this produces

* a level `lam` and a linear chart triple `φ` (with the reference level above all levels of `Q`), and
* for every `ε > 0` a parameter `t` of norm `< ε` in `A` at which **everything in
  `Work.Drive.RefTripleAt` except its class-triple parity** holds: `RefTripleGenericity`.

The reference plane is `refPlanePres φ lam hlam`, whose presenting chart `φ 2` is the `(F1)`-generic
chart of `Work.Drive.refTriple_mixedFactors` realised in the `linBase` family by
`Work.Drive.exists_triple_chart_of_middle` (`φ 2 = φ₂` *exactly*, so the `(F1)` oddness applies
verbatim), and the level `lam` is the one of `Work.Drive.exists_refPlane_charts`. -/
theorem exists_refTripleGenericity_wall {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    (A : Set (EuclideanSpace ℝ (Fin 12))) (hAopen : IsOpen A)
    (hAdense : ∀ s : EuclideanSpace ℝ (Fin 12), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A, ‖t - s‖ < δ) :
    ∃ (β lam : ℝ) (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
      (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3),
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A ∧
        RefTripleGenericity Q (refPlanePres φ lam hlam) u v
          (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  obtain ⟨β, lam, hβpos, hlam, hβlam, φ₀, hβ, habove, hrank, hgen⟩ := exists_refPlane_charts hQ
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z) := fun z hz =>
    hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  have hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z) := fun z hz => (hcbot' z hz).le
  -- the `(F1)`-generic chart and its radius, at the truncation level `c / 4`
  have hclam : c < lam := c_lt_lam hcbot habove
  obtain ⟨φ₂, δF₀, hδF₀, hF1'⟩ := refTriple_mixedFactors (hγ := hγ) (hγne := hγne) (Q := Q)
    hQ u v (c := c) (β := β) (lam := lam) (c₂ := c / 4) hc hβpos hlam
    (show (0 : ℝ) < c / 4 by linarith) (show c / 4 < c by linarith) hβlam
    (show c / 4 < lam / 2 by linarith) hclow hβ
  -- realise the `(F1)` chart in the slot `2` of a general-position triple
  obtain ⟨φ, hφ2, hrank', hgen'⟩ := exists_triple_chart_of_middle φ₂ lam hlam
  have hδF : 0 < min δF₀ (Real.log 2) := lt_min hδF₀ (Real.log_pos (by norm_num))
  have hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < min δF₀ (Real.log 2) → ‖τ₁‖ < min δF₀ (Real.log 2) →
      ‖τ₂‖ < min δF₀ (Real.log 2) →
      GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
      Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) := by
    intro τ₀ τ₁ τ₂ h0 h1 h2 hgp0 hgp1
    rw [hφ2] at hgp0 hgp1 ⊢
    exact hF1' τ₀ τ₁ τ₂ (lt_of_lt_of_le h0 (min_le_left _ _)) (lt_of_lt_of_le h1 (min_le_left _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _)) (lt_of_lt_of_le h2 (min_le_right _ _)) hgp0 hgp1
  exact ⟨β, lam, hβpos, hlam, hβlam, φ, habove,
    exists_refTripleGenericity_noAux hQ hγ c hc hcbot hdisjZc u v huv hβpos hβ φ lam hlam hβlam
      habove hδF hF1 A hAopen hAdense⟩


/-! ## 7. The `φ`-dependent form: the interface with the class-level rows

The class-parity conjunct of `Work.Drive.RefTripleAt` comes from the class-level rows, whose condition
set depends on the *reference plane* — hence on the pair `(φ, lam)` chosen by the producer.  The
following form takes that set as a function of `(φ, lam)`, so that the class-row producer can be
instantiated at the very `φ`, `lam` the Sard uses, and the class parity of `RefTripleAt` can be
concluded *at the same parameter* `t`. -/

/-- **`Work.Drive.exists_refTripleGenericity_wall` with the condition set depending on the chosen
reference plane.**  The class-level-rows producer supplies `A φ lam hlam` (an open set dense at every
point of the closed unit ball); the conclusion then has `t ∈ A φ lam hlam` at the *same* `t` at which all
of `RefTripleGenericity` holds, so that the class parity of the `hodd` chapter can be added to obtain
`Work.Drive.RefTripleAt` (`Work.Drive.refTripleAt_iff_genericity`). -/
theorem exists_refTripleGenericity_wall_dep {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q))
    (u v : UnitAddCircle) (huv : v - u ∈ Zc γ)
    (A : (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) → (lam : ℝ) → 0 < lam →
      Set (EuclideanSpace ℝ (Fin 12)))
    (hAopen : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam),
      IsOpen (A φ lam hlam))
    (hAdense : ∀ (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
      (s : EuclideanSpace ℝ (Fin 12)), ‖s‖ ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∃ t ∈ A φ lam hlam, ‖t - s‖ < δ) :
    ∃ (β lam : ℝ) (hβpos : 0 < β) (hlam : 0 < lam) (hβlam : β < lam)
      (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3),
      (∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) < lam) ∧
      ∀ ε : ℝ, 0 < ε → ∃ t : EuclideanSpace ℝ (Fin 12), ‖t‖ < ε ∧ t ∈ A φ lam hlam ∧
        RefTripleGenericity Q (refPlanePres φ lam hlam) u v
          (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) t := by
  obtain ⟨β, lam, hβpos, hlam, hβlam, φ₀, hβ, habove, hrank, hgen⟩ := exists_refPlane_charts hQ
  have hcbot' : ∀ z : ℂ, ‖z‖ ≤ 1 → c < levelOf (Q z) := fun z hz =>
    hcbot (Q z) ⟨z, by rwa [Metric.mem_closedBall, dist_zero_right], rfl⟩
  have hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z) := fun z hz => (hcbot' z hz).le
  have hclam : c < lam := c_lt_lam hcbot habove
  obtain ⟨φ₂, δF₀, hδF₀, hF1'⟩ := refTriple_mixedFactors (hγ := hγ) (hγne := hγne) (Q := Q)
    hQ u v (c := c) (β := β) (lam := lam) (c₂ := c / 4) hc hβpos hlam
    (show (0 : ℝ) < c / 4 by linarith) (show c / 4 < c by linarith) hβlam
    (show c / 4 < lam / 2 by linarith) hclow hβ
  obtain ⟨φ, hφ2, hrank', hgen'⟩ := exists_triple_chart_of_middle φ₂ lam hlam
  have hδF : 0 < min δF₀ (Real.log 2) := lt_min hδF₀ (Real.log_pos (by norm_num))
  have hF1 : ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < min δF₀ (Real.log 2) → ‖τ₁‖ < min δF₀ (Real.log 2) →
      ‖τ₂‖ < min δF₀ (Real.log 2) →
      GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2) →
      Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) ∧
      Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping v (Q z)))
          ((![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2)
          (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart (φ 2) lam hlam z)))) := by
    intro τ₀ τ₁ τ₂ h0 h1 h2 hgp0 hgp1
    rw [hφ2] at hgp0 hgp1 ⊢
    exact hF1' τ₀ τ₁ τ₂ (lt_of_lt_of_le h0 (min_le_left _ _)) (lt_of_lt_of_le h1 (min_le_left _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _)) (lt_of_lt_of_le h2 (min_le_right _ _)) hgp0 hgp1
  exact ⟨β, lam, hβpos, hlam, hβlam, φ, habove,
    exists_refTripleGenericity_noAux hQ hγ c hc hcbot hdisjZc u v huv hβpos hβ φ lam hlam hβlam
      habove hδF hF1 (A φ lam hlam) (hAopen φ lam hlam) (hAdense φ lam hlam)⟩

end

end Work.Drive
