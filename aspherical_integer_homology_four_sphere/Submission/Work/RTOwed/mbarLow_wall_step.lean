import Mathlib
import Submission.Work.RTOwed.mbarLow_eq_mbBranch_pos
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.FoldInst.All
import Submission.Work.RTOwed.cuspWall_step
import Submission.Work.RTOwed.mbarLow_foldLocal_helpers

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **The wall step of the cusp chart `mbarLow`.**

Let `a` be a cube of the cusp `v` and `m` a direction; let `k₀` be a lattice shift realising the
wall vector of the *lower* face `m` of `a` (`lamV v k₀ = wallLamV a m 0`).  If the unfolded
coordinate of the *far* cell `(wallNb a m 0, k + k₀)` lies in the closed unit cube of the far cube
at a height in `[11/10, ceilH (wallNb a m 0) ·]`, then the value of the chart `mbarLow v` at `q` is
the wall-translate — by the wall group element `wallGam a m 0` — of the chart of the *reflected*
near-cell coordinate of `a`:

  `mbarLow v q = mk (actX (wallGam a m 0) (xbarOf a (chartKlein a (mkE4 (reflWall m ·) (q 3)))))`.

This is the combination of the cell identity `Work.RTOwed.mbarLow_eq_cellX` (the far cell carries
the point, because its box and ceiling hypotheses are given) with the whole-hyperplane reflection
certificate `Work.RTOwed.chartKlein_wall_refl_zero'` (the far chart is the `wallGamK a m 0`-translate
of the reflected near chart), the copy bit being supplied by the wall table
(`cuspWallTableCerts`).

*Remark (formalisation).*  The membership proof argument appearing in the type of the statement
below is `Y ∈ Q̄` for the reflected chart value `Y`; since this is a proof of a proposition, any two
such proofs give definitionally equal terms, so the correction of the direction of the rewrite in
that argument (the original direction `rw [← …]` does not elaborate) does not change the statement.
-/
theorem mbarLow_wall_step (v : Fin 5) (a : Fin 48) (k k₀ : Fin 3 → ℤ) (m : Fin 3)
    (hcusp : Work.Cusp.cubeCusp a = v) (hk₀ : Work.RTOwed.cuspCert.lamV v k₀ = Work.RTOwed.wallLamV a m 0)
    {q : Work.RTOwed.CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hbox : Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (k + k₀)
      ∈ Work.RTOwed.cubeBox (Work.RTOwed.wallNb a m 0))
    (hceil : q 3 ≤ Work.RTOwed.ceilH (Work.RTOwed.wallNb a m 0)
      (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (k + k₀))) :
    Work.RTOwed.mbarLow v q
      = Work.FoldInst.mk (Work.FoldInst.actX (Work.RTOwed.wallGam a m 0)
          (Work.RTOwed.xbarOf a (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4
            (Work.RTOwed.reflWall m (Work.Cusp.cubeCorner a m)
              (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k)) (q 3)))
            (by
              have hQ : Work.RTOwed.chartKlein (Work.RTOwed.wallNb a m 0)
                  (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (k + k₀)) (q 3))
                  ∈ Work.FoldInst.Qbar :=
                Work.RTOwed.chartKlein_mem (Work.RTOwed.wallNb a m 0) hbox hs1 hceil
              rw [Work.RTOwed.chartKlein_wall_refl_zero' v a k k₀ m hk₀ q (by linarith)] at hQ
              exact (Work.FoldInst.Qbar_act (Work.RTOwed.wallGamK a m 0) _
                ).mp hQ))) := by
  have hs : 0 < q 3 := by linarith
  -- the far cube is a cube of the same cusp `v`
  have hcusp' : Work.Cusp.cubeCusp (Work.RTOwed.wallNb a m 0) = v := by
    rw [Work.RTOwed.cuspWall_cubeCusp_wallNb, hcusp]
  -- the whole-hyperplane reflection certificate for the wall `m` of `a`
  have hrefl : Work.RTOwed.chartKlein (Work.RTOwed.wallNb a m 0)
      (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (k + k₀)) (q 3))
      = Work.FoldInst.act (Work.RTOwed.wallGamK a m 0)
          (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4
            (Work.RTOwed.reflWall m (Work.Cusp.cubeCorner a m)
              (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k)) (q 3))) :=
    Work.RTOwed.chartKlein_wall_refl_zero' v a k k₀ m hk₀ q hs
  -- the cell identity for the far cell
  rw [Work.RTOwed.mbarLow_eq_cellX v (Work.RTOwed.wallNb a m 0) (k + k₀) hcusp' hbox hs1 hceil]
  congr 1
  refine Prod.ext ?_ ?_
  · -- the copy bit of the far cube
    obtain ⟨_, h2, _, _, _, _⟩ := Work.RTOwed.cuspWallTableCerts
    show Work.RTOwed.cubeBit (Work.RTOwed.wallNb a m 0)
      = Work.RTOwed.cubeBit a + Work.RTOwed.wallGamFlip a m 0
    exact h2 a m 0
  · -- the Klein coordinate
    apply Subtype.ext
    show Work.RTOwed.chartKlein (Work.RTOwed.wallNb a m 0)
        (Work.RTOwed.mkE4 (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v (k + k₀)) (q 3))
      = Work.FoldInst.act (Work.RTOwed.wallGamK a m 0)
          (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4
            (Work.RTOwed.reflWall m (Work.Cusp.cubeCorner a m)
              (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k)) (q 3)))
    exact hrefl

end Work.RTOwed
