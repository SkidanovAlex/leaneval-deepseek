import Mathlib
import Submission.Work.RTOwed.mbarLow_cont
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.RTOwed.sideSlack_wallHi_chartKlein
import Submission.Work.RTOwed.wallGam_sideType
import Submission.Work.RTOwed.wallNb_upper
import Submission.Work.RTOwed.isOpen_piece

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Set Topology Function
open scoped BigOperators

open chartKleinMem

/-! ## The two form certificates at an arbitrary positive height

The certificates `Work.RTOwed.chartKlein_wall_pos` and
`Work.RTOwed.sideSlack_wallHi_chartKlein_pos` of
`Submission/Work/RTOwed/piece_subset_regionPre.lean` are the versions for `0 < s` of the wall
certificates `chartKlein_wall` / `sideSlack_wallHi_chartKlein` of
`Submission/Work/RTOwed/chartKlein_wall.lean` and
`Submission/Work/RTOwed/sideSlack_wallHi_chartKlein.lean`.  Because that module is being rewritten
in parallel, the two statements are (re)proved here from the same polynomial identities — in both
cases the only height input is `s ≠ 0`, so the `11/10 ≤ s` hypothesis of the original certificates is
never used. -/

/-- **The wall gluing certificate of the cube charts at every positive height.** -/
theorem chartKlein_wall_pos' (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3}
    (hy : y i = (Cusp.cubeCorner a i : ℝ) + (if (side : ℕ) = 0 then 0 else 1)) {s : ℝ}
    (hs : 0 < s) :
    chartKlein (wallNb a i side) (mkE4 (y - wallLamV a i side) s)
      = FoldInst.act (wallGamK a i side) (chartKlein a (mkE4 y s)) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [cwChart _ _ _ hs0, cwChart _ _ _ hs0, cwVec_wall a i side y s hy, cwKlein_signExt]

/-- **The high wall of the cube chart is tight, at every positive height.** -/
theorem sideSlack_wallHi_chartKlein_pos' (a : Fin 48) (i : Fin 3) {y : CuspE3} {s : ℝ}
    (hy : y ∈ cubeBox a) (hface : y i = (Cusp.cubeCorner a i : ℝ) + 1) (hs : 0 < s) :
    FoldInst.sideSlack (wallHi a i) (chartKlein a (mkE4 y s)) = 0 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have h4 : 0 < chartVec a y s 4 := chartVec4_pos_any a y s
  rw [sideSlack_eq a (wallHi a i) y s hs0 h4.ne', Nside_wallHi_eq_zero a i hface]
  ring

/-! ## The junk branch of `mbX`

`mbX v a k q` takes the junk value `(0, ⟨0, zero_mem_Qbar⟩)` exactly when the chart value of the
cube `a` at the reduced coordinate is not in `Q̄`.  This is the case that the weak height hypothesis
`0 < q 3` (without any ceiling bound) forces us to treat separately: outside `Q̄` nothing is known
about the chart point. -/
theorem mbX_eq_junk (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : CuspE4}
    (h : chartKlein a (mkE4 (uhsXj q - cuspCert.lamV v k) (q 3)) ∉ Work.FoldInst.Qbar) :
    mbX v a k q = (0, ⟨0, zero_mem_Qbar⟩) := by
  unfold mbX
  rw [dif_neg h]

/-! ## The wall step of the floor induction at an arbitrary positive height

This is the copy of `Work.RTOwed.mbFloor_step_tmp` with the height hypothesis weakened from
`11/10 ≤ q 3` to `0 < q 3` and the ceiling hypothesis dropped.  The only two inputs of the original
proof that used the height are `chartKlein_wall` (existence of the wall certificate) and
`sideSlack_wallHi_chartKlein` (tightness of the high wall), and the `_pos` versions of both
(`Submission/Work/RTOwed/piece_subset_regionPre.lean`) need only `0 < s`.  The auxiliary facts
`chartKlein_mem` used to place the chart values in `Q̄` are replaced by a case split: if the chart
value is outside `Q̄`, then so is its wall neighbour (the two are related by the sign change
`wallGamK a j 1`, and `Q̄` is invariant under sign changes), and both `mbX` values are the junk
point. -/
theorem mbFloor_step_pos (v : Fin 5) (m : Fin 3 → ℤ) (j : Fin 3) (q : CuspE4)
    (hbox : ∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1)
    (hface : (uhsXj q) j = (m j : ℝ) + 1)
    (hs : 0 < q 3) :
    mbFloor v m q = mbFloor v (eFloor m j) q := by
  set V1 : CuspE4 := chartKlein (cb v m) (mkE4 (uhsXj q - cuspCert.lamV v (kc v m)) (q 3)) with hV1
  set V2 : CuspE4 := chartKlein (cb v (eFloor m j))
      (mkE4 (uhsXj q - cuspCert.lamV v (kc v (eFloor m j))) (q 3)) with hV2
  have hcell : q ∈ cellPre v (cb v m) (kc v m) := by
    rw [cellPre_cb_kc]; exact hbox
  have hy1mem : uhsXj q - cuspCert.lamV v (kc v m) ∈ cubeBox (cb v m) :=
    (mem_cellPre (v := v) (a := cb v m) (k := kc v m) (q := q)).mp hcell
  have hface1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
      = (Work.Cusp.cubeCorner (cb v m) j : ℝ) + 1 := by
    have h1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
        = (uhsXj q) j - (cuspCert.lamK v (kc v m) j : ℝ) := by
      simp only [PiLp.sub_apply, cuspCert.lamV]
    rw [h1, lamK_kc, hface]
    ring
  have hy1 : (uhsXj q - cuspCert.lamV v (kc v m)) j
      = (Work.Cusp.cubeCorner (cb v m) j : ℝ) + (if ((1 : Fin 2) : ℕ) = 0 then 0 else 1) := by
    rw [hface1]
    norm_num
  have hcert := chartKlein_wall_pos' (cb v m) j 1 hy1 hs
  rw [← hV1] at hcert
  have hkb : cuspCert.lamV v (kc v (eFloor m j))
      = cuspCert.lamV v (kc v m) + wallLamV (cb v m) j 1 := lamV_kc_eFloor v m j
  have hy2 : uhsXj q - cuspCert.lamV v (kc v (eFloor m j))
      = (uhsXj q - cuspCert.lamV v (kc v m)) - wallLamV (cb v m) j 1 := by
    rw [hkb]; abel
  have hV2eq : V2 = Work.FoldInst.act (wallGamK (cb v m) j 1) V1 := by
    rw [hV2, cb_eFloor, hy2]
    exact hcert
  by_cases hQ1 : V1 ∈ Work.FoldInst.Qbar
  · have hQ2 : V2 ∈ Work.FoldInst.Qbar := by
      rw [hV2eq]
      exact (Work.FoldInst.Qbar_act (wallGamK (cb v m) j 1) V1).mpr hQ1
    have hslack : Work.FoldInst.sideSlack (wallHi (cb v m) j) V1 = 0 := by
      rw [hV1]
      exact sideSlack_wallHi_chartKlein_pos' (cb v m) j hy1mem hface1 hs
    have hK : (wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1) ∈ Work.FoldInst.Ksub V1 :=
      AddSubgroup.subset_closure ⟨wallHi (cb v m) j, hslack, (wallGam_sideType (cb v m) j).2⟩
    have hact : Work.FoldInst.actX (wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1)
        (xbarOf (cb v m) V1 hQ1) = xbarOf (cb v (eFloor m j)) V2 hQ2 := by
      refine Prod.ext ?_ ?_
      · show cubeBit (cb v m) + wallGamFlip (cb v m) j 1 = cubeBit (cb v (eFloor m j))
        rw [cb_eFloor]
        exact ((wallGam_sideType (cb v m) j).1).symm
      · apply Subtype.ext
        show Work.FoldInst.act (wallGamK (cb v m) j 1) V1 = V2
        exact hV2eq.symm
    have hm1 : mbFloor v m q = Work.FoldInst.mk (xbarOf (cb v m) V1 hQ1) := by
      rw [mbFloor]
      exact congrArg Work.FoldInst.mk (mbX_eq v (cb v m) (kc v m) hQ1)
    have hm2 : mbFloor v (eFloor m j) q
        = Work.FoldInst.mk (xbarOf (cb v (eFloor m j)) V2 hQ2) := by
      rw [mbFloor]
      exact congrArg Work.FoldInst.mk (mbX_eq v (cb v (eFloor m j)) (kc v (eFloor m j)) hQ2)
    rw [hm1, hm2]
    apply Quotient.sound
    exact ⟨(wallGamK (cb v m) j 1, wallGamFlip (cb v m) j 1), hK, hact⟩
  · have hV1j : ¬ chartKlein (cb v m) (mkE4 (uhsXj q - cuspCert.lamV v (kc v m)) (q 3))
        ∈ Work.FoldInst.Qbar := fun h => hQ1 (by rw [hV1]; exact h)
    have hV2j : ¬ chartKlein (cb v (eFloor m j))
        (mkE4 (uhsXj q - cuspCert.lamV v (kc v (eFloor m j))) (q 3))
        ∈ Work.FoldInst.Qbar := by
      intro h
      have h' : V2 ∈ Work.FoldInst.Qbar := by rw [hV2]; exact h
      exact hQ1 ((Work.FoldInst.Qbar_act (wallGamK (cb v m) j 1) V1).mp (hV2eq ▸ h'))
    have h1 : mbFloor v m q = Work.FoldInst.mk (0, ⟨0, zero_mem_Qbar⟩) := by
      unfold mbFloor mbBranch
      rw [mbX_eq_junk v (cb v m) (kc v m) hV1j]
    have h2 : mbFloor v (eFloor m j) q = Work.FoldInst.mk (0, ⟨0, zero_mem_Qbar⟩) := by
      unfold mbFloor mbBranch
      rw [mbX_eq_junk v (cb v (eFloor m j)) (kc v (eFloor m j)) hV2j]
    rw [h1, h2]

/-! ## The floor induction at arbitrary positive height -/

/-- **The chart of a box of the lattice is the chart of the canonical cell**, for every positive
height.  This is the copy of `Work.RTOwed.mbFloor_eq_mbarLow` with `11/10 ≤ q 3` weakened to
`0 < q 3` and the ceiling hypothesis dropped; the induction is unchanged, only the step lemma is
replaced by `mbFloor_step_pos`. -/
theorem mbFloor_eq_mbarLow_pos (v : Fin 5) (m : Fin 3 → ℤ) (q : CuspE4)
    (hbox : ∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1)
    (hs : 0 < q 3) :
    mbFloor v m q = mbarLow v q := by
  have H : ∀ (N : ℕ) (m : Fin 3 → ℤ) (q : CuspE4),
      (belowSet m (uhsXj q)).card = N →
      (∀ l : Fin 3, (m l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (m l : ℝ) + 1) →
      0 < q 3 →
      mbFloor v m q = mbarLow v q := by
    intro N
    refine Nat.strong_induction_on N (fun N ih => ?_)
    intro m q hcard hbox hs
    by_cases hne : (belowSet m (uhsXj q)).Nonempty
    · obtain ⟨j, hj⟩ := hne
      rw [mem_belowSet] at hj
      have hxj : (uhsXj q) j = (m j : ℝ) + 1 := by
        have h1 : (m j : ℝ) + 1 ≤ (uhsXj q) j := by
          have hle : m j + 1 ≤ floorV (uhsXj q) j := by omega
          have hle' : ((m j + 1 : ℤ) : ℝ) ≤ (floorV (uhsXj q) j : ℝ) := by exact_mod_cast hle
          have hfl : (floorV (uhsXj q) j : ℝ) ≤ (uhsXj q) j := Int.floor_le _
          push_cast at hle'
          linarith
        linarith [(hbox j).2]
      have hstep := mbFloor_step_pos v m j q hbox hxj hs
      have hcard' : (belowSet (eFloor m j) (uhsXj q)).card < N := by
        rw [← hcard]
        exact belowSet_eFloor_card_lt m (uhsXj q) j hbox hj
      have hbox' : ∀ l : Fin 3, (eFloor m j l : ℝ) ≤ (uhsXj q) l ∧
          (uhsXj q) l ≤ (eFloor m j l : ℝ) + 1 := by
        intro l
        by_cases h : l = j
        · rw [h, eFloor_self]
          constructor
          · push_cast; linarith [hxj]
          · push_cast; linarith [(hbox j).2]
        · rw [eFloor_of_ne m h]
          exact hbox l
      rw [hstep]
      exact ih _ hcard' (eFloor m j) q rfl hbox' hs
    · have hempty : belowSet m (uhsXj q) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hm : m = floorV (uhsXj q) := by
        funext l
        have hnot : ¬ (m l < floorV (uhsXj q) l) := by
          intro hlt
          have : l ∈ belowSet m (uhsXj q) := by rw [mem_belowSet]; exact hlt
          rw [hempty] at this
          exact absurd this (Finset.notMem_empty l)
        have h1 : floorV (uhsXj q) l ≤ m l := by omega
        have h2 : m l ≤ floorV (uhsXj q) l := (Int.le_floor).mpr (hbox l).1
        omega
      rw [hm, mbarLow_eq_mbFloor_self]
  exact H _ m q rfl hbox hs

/-! ## The target -/

/-- **The chart of an arbitrary cell of the cusp is the value of `mbarLow`**, with the height
hypothesis `11/10 ≤ q 3` of `Work.RTOwed.mbarLow_eq_mbBranch` weakened to `0 < q 3` and its ceiling
hypothesis dropped.

This is the floor induction of `Submission/Work/RTOwed/mbarLow_cont.lean`: prove first (helper
lemmas of your own, in this file) the two statements

  `mbFloor_step_pos (v) (m) (j) (q) (hbox) (hface) (hs : 0 < q 3) :
      mbFloor v m q = mbFloor v (eFloor m j) q`

  `mbFloor_eq_mbarLow_pos (v) (m) (q) (hbox) (hs : 0 < q 3) : mbFloor v m q = mbarLow v q`

(the copies of `Work.RTOwed.mbFloor_step_tmp` / `Work.RTOwed.mbFloor_eq_mbarLow` with
`hs1 : 11/10 ≤ q 3` replaced by `0 < q 3` and `hs2` dropped), and then finish with the copy of the
proof of `Work.RTOwed.mbarLow_eq_mbBranch` (`m := corner a + lamK v k`, `cb v m = a`, `kc v m = k`,
then `mbFloor_eq_mbarLow_pos`).  Do not use `Work.RTOwed.mbFloor_step_tmp`, whose height
hypotheses are too strong here.

Route of `mbFloor_step_pos` (as in the docstring of `mbFloor_step_tmp`): put `a := cb v m`,
`k := kc v m`, `a' := cb v (eFloor m j)`, `k' := kc v (eFloor m j)` and
`y := uhsXj q - cuspCert.lamV v k`; then `y ∈ cubeBox a` and `y j = cubeCorner a j + 1`
(`cellPre_cb_kc`/`lamK_kc`/`hface`), `a' = wallNb a j 1` (`cb_eFloor`) and
`lamV v k' = lamV v k + wallLamV a j 1` (`lamV_kc_eFloor`).  If the chart value
`p := chartKlein a (mkE4 y (q 3))` is not in `Q̄`, both `mbFloor` values are the junk point
`(0, ⟨0, zero_mem_Qbar⟩)` (use `Work.FoldInst.Qbar_act` for the crossing); if `p ∈ Q̄`, then
`γ := (wallGamK a j 1, wallGamFlip a j 1)` satisfies
`mbX v a' k' q = FoldInst.actX γ (mbX v a k q)` (`chartKlein_wall_pos` for the Klein coordinate —
see `Submission/Work/RTOwed/piece_subset_regionPre.lean`, whose `11/10 ≤ s` hypothesis is never
used — and `wallGam_sideType` for the copy bit) and `γ ∈ FoldInst.Ksub p` because
`γ = FoldInst.sideType (wallHi a j)` and `sideSlack (wallHi a j) p = 0`
(`sideSlack_wallHi_chartKlein_pos`, again in `piece_subset_regionPre.lean`); hence the two values
are equal by `Quotient.sound` (`Work.FoldInst.rel`). -/
theorem mbarLow_eq_mbBranch_pos (v : Fin 5) (a : Fin 48) (k : Fin 3 → ℤ) {q : Work.RTOwed.CuspE4}
    (hcusp : Work.Cusp.cubeCusp a = v)
    (hbox : Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k ∈ Work.RTOwed.cubeBox a)
    (hs : 0 < q 3) :
    Work.RTOwed.mbarLow v q = Work.RTOwed.mbBranch v a k q := by
  set mm : Fin 3 → ℤ := fun l => Work.Cusp.cubeCorner a l + cuspCert.lamK v k l with hmm
  have hq : q ∈ cellPre v a k := hbox
  have hmem := (mem_cellPre_iff v a k q).mp hq
  have hbox' : ∀ l : Fin 3, (mm l : ℝ) ≤ (uhsXj q) l ∧ (uhsXj q) l ≤ (mm l : ℝ) + 1 := by
    intro l
    have h := hmem l
    have hcast : (mm l : ℝ) = (Work.Cusp.cubeCorner a l : ℝ) + (cuspCert.lamK v k l : ℝ) := by
      simp only [hmm]
      push_cast
      ring
    rw [hcast]
    exact h
  have hcb : cb v mm = a := by
    calc cb v mm = Work.Cusp.cubeOfMod v (Work.Cusp.cubeCorner a) := by
          refine cubeOfMod_residue v (fun i => ?_)
          have h : mm i - Work.Cusp.cubeCorner a i = cuspCert.lamK v k i := by
            simp only [hmm]
            ring
          rw [h]
          exact ⟨k i, by simp only [cuspCert.lamK]⟩
      _ = Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a) (Work.Cusp.cubeCorner a) := by rw [hcusp]
      _ = a := cubeOfMod_corner a
  have hkc : kc v mm = k := by
    funext i
    simp only [kc, hcb]
    have h : mm i - Work.Cusp.cubeCorner a i = k i * (Work.Cusp.latMod v i : ℤ) := by
      simp only [hmm, cuspCert.lamK]
      ring
    rw [h]
    exact Int.mul_ediv_cancel _ (ne_of_gt (cuspCert.latMod_pos v i))
  have h1 := mbFloor_eq_mbarLow_pos v mm q hbox' hs
  have h2 : mbFloor v mm q = mbBranch v a k q := by
    rw [mbFloor, hcb, hkc]
  exact h1.symm.trans h2

end Work.RTOwed
