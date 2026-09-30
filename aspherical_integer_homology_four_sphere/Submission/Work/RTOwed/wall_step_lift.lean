import Mathlib
import Submission.Work.RTOwed.mbarLow_foldLocal_defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The lift form of the one-step wall unfolding of the walk.**

Crossing the wall of the cell of the crossing set `S'` in the direction `m` (`m ∉ S'`) and lifting
into `X̄ = ZMod 2 × Q̄` turns the lift over the `S' ∪ {m}`-cell of the walk into the group translate
(by the wall element `wallGam (walkCube v q S') m 0`) of the lift over the `S'`-cell at the reflected
point `wallRefl q m x`.

This is the `xbarOf` form of the chart-level certificate `chartKlein_wall_refl_zero'`: the far cube
of the walk is `wallNb (walkCube v q S') m 0` (`walkCube_insert`), its offset is `walkK v q S' + k₀`
(`walkK_insert_sub`), and the reflected chart argument of the near cell is the near-cell chart
argument of the reflected point (`uhsXj_wallRefl`), at the unchanged height (`wallRefl_three`); the
copy bit is supplied by the wall table (`cuspWallTableCerts`). -/
theorem wall_step_lift (v : Fin 5) (q : Work.RTOwed.CuspE4) (S' : Finset (Fin 3))
    {m : Fin 3} (hmS' : m ∉ S') {k₀ : Fin 3 → ℤ}
    (hk₀ : Work.RTOwed.cuspCert.lamV v k₀ = Work.RTOwed.wallLamV (Work.RTOwed.walkCube v q S') m 0)
    {x : Work.RTOwed.CuspE4} (hs1 : 11 / 10 ≤ x 3)
    {hF : Work.RTOwed.chartKlein (Work.RTOwed.walkCube v q (insert m S'))
        (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj x
          - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q (insert m S'))) (x 3))
      ∈ Work.FoldInst.Qbar}
    {hN : Work.RTOwed.chartKlein (Work.RTOwed.walkCube v q S')
        (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj (Work.RTOwed.wallRefl q m x)
          - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q S'))
          ((Work.RTOwed.wallRefl q m x) 3))
      ∈ Work.FoldInst.Qbar} :
    Work.RTOwed.xbarOf (Work.RTOwed.walkCube v q (insert m S'))
        (Work.RTOwed.chartKlein (Work.RTOwed.walkCube v q (insert m S'))
          (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj x
            - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q (insert m S'))) (x 3))) hF
      = Work.FoldInst.actX (Work.RTOwed.wallGam (Work.RTOwed.walkCube v q S') m 0)
          (Work.RTOwed.xbarOf (Work.RTOwed.walkCube v q S')
            (Work.RTOwed.chartKlein (Work.RTOwed.walkCube v q S')
              (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj (Work.RTOwed.wallRefl q m x)
                - Work.RTOwed.cuspCert.lamV v (Work.RTOwed.walkK v q S'))
                ((Work.RTOwed.wallRefl q m x) 3))) hN) := by
  -- the far cube of the walk is the far cube of the wall `m` of the `S'`-cell
  have hcube : walkCube v q (insert m S') = wallNb (walkCube v q S') m 0 :=
    walkCube_insert v q S' hmS'
  -- and its offset is the offset of the `S'`-cell shifted by the wall vector `k₀`
  have hk : walkK v q (insert m S') = walkK v q S' + k₀ :=
    walkK_insert_sub v q S' hmS' k₀ hk₀
  -- the height is unchanged by the wall reflection
  have hs3 : (wallRefl q m x) 3 = x 3 := wallRefl_three q m x
  -- the reflected point's near-cell coordinate is the reflection of the near-cell coordinate
  have hrefl := uhsXj_wallRefl (v := v) (q := q) (S := S') (m := m) hmS' x
  -- the chart identity of the one-step unfolding, in the walk's coordinates
  have hchart : chartKlein (walkCube v q (insert m S'))
        (mkE4 (uhsXj x - cuspCert.lamV v (walkK v q (insert m S'))) (x 3))
      = Work.FoldInst.act (wallGamK (walkCube v q S') m 0)
          (chartKlein (walkCube v q S')
            (mkE4 (uhsXj (wallRefl q m x) - cuspCert.lamV v (walkK v q S'))
              ((wallRefl q m x) 3))) := by
    rw [hcube, hk]
    rw [chartKlein_wall_refl_zero' v (walkCube v q S') (walkK v q S') k₀ m hk₀ x (by linarith)]
    rw [← hrefl, hs3]
  refine Prod.ext ?_ ?_
  · -- the copy bit of the far cube
    show cubeBit (walkCube v q (insert m S'))
      = cubeBit (walkCube v q S') + wallGamFlip (walkCube v q S') m 0
    rw [hcube]
    exact cuspWallTableCerts.2.1 (walkCube v q S') m 0
  · -- the Klein coordinate
    apply Subtype.ext
    exact hchart

end Work.RTOwed
