import Mathlib
import Submission.Work.ThomBordism.phiDSplitBlocks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.CofAtlas

/-- **The block structure of `phiD`**: in the splitting of `ℝ^{9+k}` into the level directions
`range (chartIota x)` and the normal-form complement `ker (chartBeta x)`
(`Work.ThomBordism.CofAtlas.splitMap`), the map `phiD x p = (chartBeta x, Omega x p)` is
block-upper-triangular with the *identity* on the level block: its first component is `(u,c) ↦ u` and
its second depends only on the normal coordinate.  Hypotheses `p ∈ D.src x` and `p` interior in `M`
(mirroring `range_chartIota_eq_ker_Omega`) — without them the statement is false. -/
theorem phiDSplitBlocks (k n : ℕ) : Work.ThomBordism.CofAtlas.PhiDSplitBlocks k n := by
  intro M _ _ _ _ _ D x p hp hpint u c
  -- `splitMap` is the inverse of `chartT` composed with the coordinate swap `(u,c) ↦ (c,u)`:
  -- it sends the level direction `u` to `chartIota x u` and the normal direction `c` to
  -- `chartT x`.symm (c, 0)`.
  have hsplit : Work.ThomBordism.CofAtlas.splitMap D x (u, c)
      = D.S.chartIota x u + (D.S.chartT x).symm (c, 0) := rfl
  constructor
  · -- the level block: `chartBeta` reads the second coordinate of `chartT`, which is `u`
    rw [hsplit, map_add]
    show D.S.chartBeta x (D.S.chartIota x u)
      + D.S.chartBeta x ((D.S.chartT x).symm (c, 0)) = u
    rw [Work.PTGeometric.Lvl.Setup.chartBeta_iota]
    have h : D.S.chartBeta x ((D.S.chartT x).symm (c, 0)) = 0 := by
      rw [Work.PTGeometric.Lvl.Setup.chartBeta_apply]
      simp
    rw [h, add_zero]
  · -- the normal block: `Omega` kills the level directions (the hard direction of
    -- `range_chartIota_eq_ker_Omega`), so only the normal coordinate contributes
    rw [hsplit, map_add]
    show D.Omega x (p : M) (D.S.chartIota x u)
      + D.Omega x (p : M) ((D.S.chartT x).symm (c, 0))
      = D.Omega x (p : M) ((D.S.chartT x).symm (c, 0))
    have hmem : D.S.chartIota x u ∈ LinearMap.ker (D.Omega x (p : M)).toLinearMap := by
      rw [← Work.ThomBordism.CofAtlas.range_chartIota_eq_ker_Omega D x hp hpint]
      exact ⟨u, rfl⟩
    have hzero : D.Omega x (p : M) (D.S.chartIota x u) = 0 := hmem
    rw [hzero, zero_add]

end Work.CofAtlas
