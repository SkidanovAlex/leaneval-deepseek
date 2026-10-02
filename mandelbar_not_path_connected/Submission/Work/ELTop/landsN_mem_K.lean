import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- A ray which lands at `y` lands inside the filled Julia set: the potential of the ray points
tends to `0` as the level tends to `1`, and the potential is continuous and vanishes exactly on
`K c`. -/
theorem landsN_mem_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : y ∈ Work.EL.K c := by
  -- on the filter `nhdsWithin 1 (Ioi 1)` the level `t` is eventually `> 1`, where the potential is
  -- the external level `log t`
  have hpot : (fun t : ℝ => Work.EL.pot hN (Work.EL.rayPt hN θ t))
      =ᶠ[nhdsWithin (1:ℝ) (Set.Ioi 1)] Real.log := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Work.EL.pot_rayPt hN ht
  -- `log t → log 1 = 0` as `t → 1⁺`
  have hlog : Filter.Tendsto (fun t : ℝ => Real.log t) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 1))
    simpa using h
  -- hence the potential of the ray points tends to `0`
  have h2 : Filter.Tendsto (fun t : ℝ => Work.EL.pot hN (Work.EL.rayPt hN θ t))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    Filter.Tendsto.congr' hpot.symm hlog
  -- and by continuity of the potential it also tends to the potential of the landing point
  have h1 : Filter.Tendsto (fun t : ℝ => Work.EL.pot hN (Work.EL.rayPt hN θ t))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.EL.pot hN y)) := by
    have hc := hN.continuous_potential.continuousAt.tendsto.comp h
    simpa only [Work.EL.pot, Function.comp_def] using hc
  have hy0 : Work.EL.pot hN y = 0 := tendsto_nhds_unique h1 h2
  exact (Work.EL.pot_eq_zero_iff hN y).mp hy0

end Work.ELTop
