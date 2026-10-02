import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Nest_coLand
import Submission.Work.ELAssembly.rayPt_eq_of_eqOn_compl

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.Top

/-- **Co-landing of the nest pairs at `z₁`, transported to the Böttcher coordinate `d.φ`.**

The canonical Böttcher data `hNcan` and the Böttcher data `d.hN` of the root-parabolic parameter
`d` have the same Nakane datum `Mb = K c`, and the two Böttcher coordinates agree off `K c`
(this is `hψ`).  By `rayPt_eq_of_eqOn_compl` the rays — and hence the landings — of the two sets
of data coincide, so the co-landing statement `Work.ELNest.nest_pair_coLands` proved for `hNcan`
transports to `d.hN`. -/
theorem coLand_Q {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (d : Work.EL.RootParabolic c) (hNcan : Work.ELPull.DynB c) (hφcan : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (hψ : ∀ z : ℂ, z ∉ Work.EL.K c → d.φ z = Work.ParamRays.dynPhiOf c z) (htop : Work.ELPull.PB1Top hNcan) (hbase : ∃ y : ℂ, Work.ELPull.LandsN hNcan (Work.ELNest.bAng 0) y ∧ Work.ELPull.LandsN hNcan (Work.ELNest.bAng' 0) y) (hcv : ∀ (n t : ℕ) (Q : Work.ELPull.CoPair hNcan), t < 10 → Q.a = (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t).1 → Q.b = (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t).2 → c ∈ Work.ELPull.arcSide hNcan Q (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).2 (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).1) : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.bAng' n) y ∧ Work.EL.LandsN d.hN (Work.ELNest.bAng n + 1) y := by
  -- the two Böttcher coordinates agree off `K c`
  have hagree : ∀ z : ℂ, z ∉ Work.EL.K c →
      Work.ParamRays.dynPhi c z = Work.EL.dynPhi c d.φ z := by
    intro z hz
    rw [Work.ParamRays.dynPhi_of_not_mem hz, Work.EL.dynPhi_of_notMem hz, ← hψ z hz]
  -- transport the rays of `hNcan` to the rays of `d.hN`
  have hray := rayPt_eq_of_eqOn_compl hNcan d.hN hagree
  -- the co-landing statement in the canonical data
  have key := Work.ELNest.nest_pair_coLands hc hNcan hφcan htop hbase hcv
  intro n
  obtain ⟨y, h1, h2⟩ := key n
  exact ⟨y, (hray.2 (Work.ELNest.bAng' n) y).mp h1,
    (hray.2 (Work.ELNest.bAng n + 1) y).mp h2⟩

end Work.ELAssembly
