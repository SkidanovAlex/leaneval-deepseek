import Mathlib
import Submission.Work.RTOwed.mbarLow_foldLocal_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function

noncomputable section

/-- **A coordinatewise (sup) bound controls the Euclidean distance**: if every coordinate of `x`
differs from the corresponding coordinate of `q` by less than `ε`, then `dist x q < 4 * ε`. -/
private lemma dist_lt_of_coord {x q : CuspE4} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ j : Fin 4, |x j - q j| < ε) : dist x q < 4 * ε := by
  rw [EuclideanSpace.dist_eq]
  have h1 : ∀ i : Fin 4, dist (x.ofLp i) (q.ofLp i) ^ 2 ≤ ε ^ 2 := by
    intro i
    rw [Real.dist_eq, sq_abs]
    have hi := abs_lt.mp (h i)
    nlinarith [hi.1, hi.2, hε]
  calc √(∑ i : Fin 4, dist (x.ofLp i) (q.ofLp i) ^ 2)
      ≤ √(∑ _i : Fin 4, ε ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => h1 i))
    _ = √((2 * ε) ^ 2) := by rw [Fin.sum_univ_four]; ring_nf
    _ = 2 * ε := Real.sqrt_sq (by linarith)
    _ < 4 * ε := by linarith

theorem cellLift_base_mem_Dvor (v : Fin 5) (i : Fin 98)
    (r : Fin (Work.FoldInst.foldCodim i) → Bool) {q : Work.RTOwed.CuspE4}
    (hr : Work.RTOwed.cellLift v (Work.RTOwed.walkCube v q ∅) (Work.RTOwed.walkK v q ∅) q
      ∈ Work.FoldInst.Dvor i r)
    (hq1 : 11 / 10 ≤ q 3)
    (hq2 : q 3 ≤ Work.RTOwed.ceilH (Work.RTOwed.walkCube v q ∅)
        (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q ∅))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : Work.RTOwed.CuspE4),
      (∀ j : Fin 4, |x j - q j| < ε) →
      (∀ j : Fin 3, (Work.Cusp.cubeCorner (Work.RTOwed.walkCube v q ∅) j : ℝ)
            ≤ (Work.RTOwed.uhsXj x - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q ∅)) j
          ∧ (Work.RTOwed.uhsXj x - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q ∅)) j
            < (Work.Cusp.cubeCorner (Work.RTOwed.walkCube v q ∅) j : ℝ) + 1) →
      (11 / 10 ≤ x 3) →
      (x 3 ≤ Work.RTOwed.ceilH (Work.RTOwed.walkCube v q ∅)
        (Work.RTOwed.uhsXj x - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q ∅))) →
      Work.RTOwed.cellLift v (Work.RTOwed.walkCube v q ∅) (Work.RTOwed.walkK v q ∅) x
        ∈ Work.FoldInst.Dvor i r := by
  -- the cell of the walk at the empty crossing set, in local notation
  set a : Fin 48 := walkCube v q ∅ with ha
  set k : Fin 3 → ℤ := walkK v q ∅ with hk
  have hk0 : k = cuspCert.floorK v (uhsXj q) := by rw [hk, walkK_empty]
  have ha0 : a = cubeOf v (uhsXj q) := by rw [ha, walkCube_empty]
  -- `q` lies in the closed box of its own cell and below its ceiling
  have hboxq : uhsXj q - cuspCert.lamV v k ∈ cubeBox a := by
    rw [hk0, ha0,
      cuspCert.sub_lamV_floorK v (uhsXj q) (fun i => cuspCert.floorV_dvd v (uhsXj q) i)]
    exact redV_mem_cubeBox v (uhsXj q)
  have hmemq : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∈ Work.FoldInst.Qbar :=
    chartKlein_mem a hboxq hq1 hq2
  -- the two conclusions of the hypothesis `hr`
  have hfq : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3))
      ∈ Work.FoldInst.VoronoiOpen i r := by
    have h := hr
    rw [cellLift_eq hmemq] at h
    exact h.2
  have hbit : cubeBit a = Work.FoldInst.foldCr i r := by
    have h := hr
    rw [cellLift_eq hmemq] at h
    exact h.1
  -- the region on which the chart of the cell is continuous (the closed cell below `11/10`)
  have hqR : q ∈ cellPre v a k ∩ {y : CuspE4 | 11 / 10 ≤ y 3} :=
    ⟨by rw [mem_cellPre]; exact hboxq, hq1⟩
  have hpre : (fun y : CuspE4 => chartKlein a (mkE4 (uhsXj y - cuspCert.lamV v k) (y 3))) ⁻¹'
      Work.FoldInst.VoronoiOpen i r
      ∈ 𝓝[cellPre v a k ∩ {y : CuspE4 | 11 / 10 ≤ y 3}] q :=
    ((continuousOn_chartKlein_cell v a k).continuousWithinAt hqR).preimage_mem_nhdsWithin
      ((Work.FoldInst.isOpen_VoronoiOpen i r).mem_nhds hfq)
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  refine ⟨δ / 4, by linarith, ?_⟩
  intro x hxcoord hxbox hx1 hx2
  -- `x` lies in the region, and in the ball
  have hxbox' : uhsXj x - cuspCert.lamV v k ∈ cubeBox a :=
    fun j => ⟨(hxbox j).1, le_of_lt (hxbox j).2⟩
  have hxR : x ∈ cellPre v a k ∩ {y : CuspE4 | 11 / 10 ≤ y 3} :=
    ⟨by rw [mem_cellPre]; exact hxbox', hx1⟩
  have hdist : dist x q < δ := by
    have hlt := dist_lt_of_coord (x := x) (q := q) (ε := δ / 4) (by linarith) hxcoord
    linarith
  have hfx : chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3))
      ∈ Work.FoldInst.VoronoiOpen i r :=
    hδsub ⟨Metric.mem_ball.mpr hdist, hxR⟩
  have hmemx : chartKlein a (mkE4 (uhsXj x - cuspCert.lamV v k) (x 3)) ∈ Work.FoldInst.Qbar :=
    chartKlein_mem a hxbox' hx1 hx2
  rw [cellLift_eq hmemx]
  exact ⟨hbit, hfx⟩

end

end Work.RTOwed
