import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.ELTop.tripodArms_cover
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set

noncomputable section

namespace Work.ELNest

/-- **The cut point of the arm `A` is the only point of the arm `A` on the boundary of the
level-`n` region of the nest at `b₂`.**

The level-`n` region `Δ̂ₙ = S.D n` is the region of the admissible ray polygon
`[Za n, Zb n, Zc n]` at level `Dlev S.L n > 1`, and `polyCurve_isJordan` shows that its boundary
`polyCurve [Za n, Zb n, Zc n] (Dlev S.L n)` is a Jordan curve.  By
`frontier_polyRegion_inter_K` the frontier of the region meets the filled Julia set `K c` exactly
in the three landing points `cutA n`, `cutB n`, `cutC n` of the three pairs of the polygon (the
ray pieces of the polygon avoid `K c`, and its equipotential arc of level `> 1` does too).

Intersecting with the arm `A` leaves only `cutA n`: the cut point of the arm `A` lies in the arm
`A` by `cutA_mem`, while the cut points of the arms `B` and `C` lie in the arms `B` and `C`
(`cutB_mem`, `cutC_mem`) and the three arms of the tripod are pairwise disjoint
(`tripodArms_disjoint`). -/
theorem cut_unique_A {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) :
    frontier (S.D n) ∩ Work.EL.K c ∩ S.armA = {S.cutA n} := by
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
  rw [show S.D n = Work.EL.polyRegion [S.Za n, S.Zb n, S.Zc n] (Work.ELNest.Dlev S.L n)
    from rfl, hfr]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨P, hP, hyz⟩, hzA⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl
    · exact hyz.symm
    · -- `cutB n` lies in the arm `B`, which is disjoint from the arm `A`
      exfalso
      have hzB : z ∈ S.armB := hyz ▸ S.cutB_mem n
      exact (Set.disjoint_left.mp (Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).1 hzA) hzB
    · -- `cutC n` lies in the arm `C`, which is disjoint from the arm `A`
      exfalso
      have hzC : z ∈ S.armC := hyz ▸ S.cutC_mem n
      exact (Set.disjoint_left.mp
        ((Work.ELTop.tripodArms_disjoint S.d.hN hJ S.tripod).2.2).symm hzA) hzC
  · intro hz
    subst hz
    exact ⟨⟨S.Za n, by simp, rfl⟩, S.cutA_mem n⟩

end Work.ELNest
