import Mathlib
import Submission.Work.RTOwed.CuspPiece
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.sideSlack_pos_of_not_wall
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.wallHi_slack_sign
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.RTOwed.Ksub_chartKlein_le
import Submission.Work.RTOwed.cuspWalk_lower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-!
# The region of the cusp chart is covered by the pieces of its cells

`regionPre v B = mk ⁻¹' (mbarLow v '' chartRegion B)` is the preimage in `X̄ = ZMod 2 × Q̄` of the
image of the region (`B` below the ceiling) under the cusp chart `mbarLow v`.  This file proves that
it is contained in the union of the *pieces*

  `piece v a k B = {x : X̄ | x.1 = cubeBit a ∧ ∃ q ∈ pieceSrc v a k B, x.2.1 = cellPt v a k q}`

over the cubes `a` of the cusp `v` and all lattice offsets `k`.  This is the "the union of the pieces
contains the preimage" direction of the cover of `CuspPiece.lean`; the converse (each piece lies in
the region) is the pending `Work.RTOwed.piece_subset_regionPre`.

## Route

A point of the region is the class of `cuspLowPt v q` for a source point `q` of the region, so
(`mbarLow_eq_beta`) it is the class of the *canonical cell* `(a₀, k₀)` of `q`, where
`a₀ = cubeOf v (uhsXj q)`, `k₀ = cuspCert.floorK v (uhsXj q)` and
`redV v (uhsXj q) = uhsXj q - lamV v k₀` (`cuspCert.sub_lamV_floorK`, `cuspCert.floorV_dvd`).
If `y = actX γ (cuspLowPt v q)` for `γ ∈ Ksub` of the chart point, then
`γ ∈ spanSub a₀ (pinned a₀ u₀)` (`Work.RTOwed.Ksub_chartKlein_le`: `γ` is a subset sum of the
lower-wall types `wGen a₀ i` over the pinned cube coordinates), and the *lower-wall walk*
`Work.RTOwed.cuspWalk_lower` unfolds those reflections of the chart into the cell chart of a further
cell `(a', k')` of the same cusp: the chart value of `(a₀,k₀)` is carried to the chart value of
`(a',k')` by exactly that group element, the copy bits match, and the unfolded coordinate
`uhsXj q - lamV v k'` lies in the cube box of `a'`.  Hence `y` lies in the piece of `(a',k')` with
source point `q ∈ B`.
-/

/-! ## The canonical cell of a source point -/

/-- **The `redChart` of the canonical cube is the cell chart at the floor offset.** -/
theorem redChart_eq_cellPt_floorK (v : Fin 5) (q : CuspE4) :
    redChart v (cubeOf v (uhsXj q)) q = cellPt v (cubeOf v (uhsXj q)) (cuspCert.floorK v (uhsXj q)) q := by
  have hk : uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) = redV v (uhsXj q) :=
    cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  simp only [redChart, cellPt, hk]

/-- **The canonical cell chart lies in `Q̄`** on the region `11/10 ≤ q 3 ≤ β (xOf q)`. -/
theorem redChart_mem_Qbar (v : Fin 5) {q : CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ Cusp.beta (xOf4 q)) :
    redChart v (cubeOf v (uhsXj q)) q ∈ Work.FoldInst.Qbar :=
  chartKlein_mem (cubeOf v (uhsXj q)) (redV_mem_cubeBox v (uhsXj q)) hs1 (le_ceilH_chartRed hs2)

/-- The copy bit of the cusp chart of a source point (on the region, where the junk branch of
`cuspLowPt` is never taken). -/
theorem cuspLowPt_fst (v : Fin 5) {q : CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ Cusp.beta (xOf4 q)) :
    (cuspLowPt v q).1 = cubeBit (cubeOf v (uhsXj q)) := by
  rw [cuspLowPt]
  split_ifs with hh
  · rfl
  · exact absurd (redChart_mem_Qbar v hs1 hs2) hh

/-- **The cusp chart of a source point on the region is the canonical cell chart.** -/
theorem cuspLowPt_snd (v : Fin 5) {q : CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ Cusp.beta (xOf4 q)) :
    (cuspLowPt v q).2.1 = redChart v (cubeOf v (uhsXj q)) q := by
  rw [cuspLowPt]
  split_ifs with hh
  · rfl
  · exact absurd (redChart_mem_Qbar v hs1 hs2) hh

/-! ## The main theorem, from the lower-wall walk -/

/-- **The region of the cusp chart is covered by the pieces of its cells**, given the lower-wall
walk `Work.RTOwed.cuspWalk_lower` as a hypothesis (this is the form in which the walk is consumed;
the theorem below instantiates it). -/
theorem regionPre_subset_pieces_of (v : Fin 5) {B : Set CuspE4} (hB : IsOpen B)
    (hBhi : ∀ q ∈ B, 11 / 10 ≤ q 3)
    (walk : ∀ (q : CuspE4), 11 / 10 ≤ q 3 →
      ∀ (S : Finset (Fin 3)) (a : Fin 48) (k : Fin 3 → ℤ),
        Cusp.cubeCusp a = v →
        (uhsXj q - cuspCert.lamV v k) ∈ cubeBox a →
        (∀ i ∈ S, (uhsXj q - cuspCert.lamV v k) i = (Cusp.cubeCorner a i : ℝ)) →
        ∃ (a' : Fin 48) (k' : Fin 3 → ℤ),
          Cusp.cubeCusp a' = v ∧
          (uhsXj q - cuspCert.lamV v k') ∈ cubeBox a' ∧
          cellPt v a' k' q = FoldInst.act ((S.sum (cuspCert.wGen a)).1) (cellPt v a k q) ∧
          cubeBit a' = cubeBit a + (S.sum (cuspCert.wGen a)).2) :
    regionPre v B ⊆ ⋃ a : {a : Fin 48 // Cusp.cubeCusp a = v}, ⋃ k : Fin 3 → ℤ, piece v a.1 k B := by
  intro y hy
  rw [regionPre_eq] at hy
  obtain ⟨q, hq, hrel⟩ := hy
  have hs1 : 11 / 10 ≤ q 3 := hBhi q hq.1
  have hs2 : q 3 ≤ Cusp.beta (xOf4 q) := hq.2
  -- the canonical cell of the source point
  have hca₀ : Cusp.cubeCusp (cubeOf v (uhsXj q)) = v :=
    cuspCert.cubeCusp_cubeOfMod v (floorV (uhsXj q))
  have hk : uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q)) = redV v (uhsXj q) :=
    cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)
  have hu₀ : (uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q))) ∈ cubeBox (cubeOf v (uhsXj q)) := by
    rw [hk]
    exact redV_mem_cubeBox v (uhsXj q)
  have hstep : cellPt v (cubeOf v (uhsXj q)) (cuspCert.floorK v (uhsXj q)) q
      = redChart v (cubeOf v (uhsXj q)) q := (redChart_eq_cellPt_floorK v q).symm
  -- the group element of the relation
  obtain ⟨γ, hγ, hact⟩ := hrel
  rw [cuspLowPt_snd v hs1 hs2] at hγ
  have hγ' : γ ∈ Work.FoldInst.Ksub
      (chartKlein (cubeOf v (uhsXj q)) (mkE4 (redV v (uhsXj q)) (q 3))) := hγ
  -- `γ` is a sum of the pinned lower-wall types
  have hle := Ksub_chartKlein_le (cubeOf v (uhsXj q))
    (cuspCert.redV_mem_halfopenBox v (uhsXj q)) hs1 (le_ceilH_chartRed hs2)
  have hspan : γ ∈ cuspCert.spanFin (cubeOf v (uhsXj q))
      (cuspCert.pinned (cubeOf v (uhsXj q)) (redV v (uhsXj q))) := by
    have h := hle hγ'
    simpa [cuspCert.spanSub] using h
  obtain ⟨D, hDmem, hDγ⟩ := Finset.mem_image.mp hspan
  have hDsub : D ⊆ cuspCert.pinned (cubeOf v (uhsXj q)) (redV v (uhsXj q)) :=
    Finset.mem_powerset.mp hDmem
  -- the walk across the lower walls of the pinned coordinates
  have hpin : ∀ i ∈ D,
      (uhsXj q - cuspCert.lamV v (cuspCert.floorK v (uhsXj q))) i
        = (Cusp.cubeCorner (cubeOf v (uhsXj q)) i : ℝ) := by
    intro i hi
    rw [hk]
    exact (cuspCert.mem_pinned).mp (hDsub hi)
  obtain ⟨a', k', hca', hbox', hact', hbit'⟩ :=
    walk q hs1 D (cubeOf v (uhsXj q)) (cuspCert.floorK v (uhsXj q)) hca₀ hu₀ hpin
  -- the copy bits
  have hγ2 : (D.sum (cuspCert.wGen (cubeOf v (uhsXj q)))).2 = γ.2 := congrArg Prod.snd hDγ
  have hbitE : cubeBit a' = cubeBit (cubeOf v (uhsXj q)) + γ.2 := by
    rw [hγ2] at hbit'
    exact hbit'
  have hy1 : y.1 = cubeBit (cubeOf v (uhsXj q)) + γ.2 := by
    have h1 : y.1 = (cuspLowPt v q).1 + γ.2 := by
      rw [← hact]
      exact FoldInst.actX_fst γ (cuspLowPt v q)
    rwa [cuspLowPt_fst v hs1 hs2] at h1
  -- the chart values
  have hγ1 : (D.sum (cuspCert.wGen (cubeOf v (uhsXj q)))).1 = γ.1 := congrArg Prod.fst hDγ
  have hy2 : y.2.1 = FoldInst.act γ.1 (redChart v (cubeOf v (uhsXj q)) q) := by
    rw [← hact]
    exact FoldInst.actX_snd γ (cuspLowPt v q) |>.trans (congrArg _ (cuspLowPt_snd v hs1 hs2))
  rw [← hγ1, ← hstep] at hy2
  have hval : y.2.1 = cellPt v a' k' q := hy2.trans hact'.symm
  -- membership in the piece of the walked cell
  refine Set.mem_iUnion.mpr ⟨⟨a', hca'⟩, Set.mem_iUnion.mpr ⟨k', ?_⟩⟩
  exact ⟨hy1.trans hbitE.symm, q, ⟨hq.1, fun j => ⟨by linarith [(hbox' j).1],
    by linarith [(hbox' j).2]⟩⟩, hval⟩

/-- **The region of the cusp chart is covered by the pieces of its cells** (the direction "the
union of the pieces contains the preimage" of the cover of `CuspPiece.lean`), from the support lemma
`Work.RTOwed.Ksub_chartKlein_le` and the lower-wall walk `Work.RTOwed.cuspWalk_lower`: see the
module docstring for the route. -/
theorem regionPre_subset_pieces (v : Fin 5) {B : Set CuspE4} (hB : IsOpen B)
    (hBhi : ∀ q ∈ B, 11 / 10 ≤ q 3) :
    regionPre v B ⊆ ⋃ a : {a : Fin 48 // Cusp.cubeCusp a = v}, ⋃ k : Fin 3 → ℤ, piece v a.1 k B :=
  regionPre_subset_pieces_of v hB hBhi (fun q hs => cuspWalk_lower v q hs)

end Work.RTOwed
