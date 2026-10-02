import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-- **The cut point of the arm `A` lies in the arm `A`, in the filled Julia set `K c`, and on
the boundary of the level-`n` region `Δ̂ₙ = S.D n` of the nest at `b₂`.**

The level-`n` region is the region of the admissible ray polygon `[Za n, Zb n, Zc n]` at level
`Dlev S.L n > 1`, so its boundary `polyCurve [Za n, Zb n, Zc n] (Dlev S.L n)` is a Jordan curve
(`polyCurve_isJordan`).  By `frontier_polyRegion_inter_K` the frontier of the region meets the
filled Julia set `K c` exactly in the three landing points `cutA n`, `cutB n`, `cutC n` of the
pairs of the polygon (the ray pieces of the polygon avoid `K c`, and its equipotential arc of
level `> 1` does too).  The cut point `cutA n` is the first of these, so it lies in the frontier;
and `cutA_mem` of `NestData` places it in the arm `A`. -/
theorem cut_mem_A {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    S.cutA n ∈ S.armA ∩ Work.EL.K c ∩ frontier (S.D n) := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  -- the level of the level-`n` region is `> 1`
  have hR : 1 < Work.ELNest.Dlev S.L n := by
    rw [Work.ELNest.Dlev]
    exact Real.one_lt_rpow S.hL (by positivity)
  -- the boundary of the region is a Jordan curve
  have hC : Work.Top.IsJordanCurve
      (Work.EL.polyCurve [S.Za n, S.Zb n, S.Zc n] (Work.ELNest.Dlev S.L n)) :=
    Work.ELTop.polyCurve_isJordan S.d.hN _ (S.D_adm n) hR
  -- the frontier of the region meets `K c` exactly in the three cut points
  have hfr := Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ
    [S.Za n, S.Zb n, S.Zc n] (S.D_adm n) hR hC
  have hmem : S.cutA n ∈ frontier (S.D n) ∩ Work.EL.K c := by
    rw [show S.D n = Work.EL.polyRegion [S.Za n, S.Zb n, S.Zc n] (Work.ELNest.Dlev S.L n)
      from rfl, hfr]
    exact ⟨S.Za n, by simp, rfl⟩
  exact ⟨⟨S.cutA_mem n, hmem.2⟩, hmem.1⟩

end Work.ELNest
