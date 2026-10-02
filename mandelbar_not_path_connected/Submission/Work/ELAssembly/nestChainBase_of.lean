import Mathlib
import Submission.Work.ELAssembly.ELPullChains
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELNest.uPair_lands
import Submission.Work.ELNest.Nest_coLand

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-- The level-`0` pair of the `z₁`-nest is the `u`-pair, whose co-landing is `uPair_lands`. -/
theorem nestChainBase_of {c : ℂ} (d : Work.EL.RootParabolic c) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hbase₀ : ∃ y : ℂ, Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (((Work.ELPull.Cert.uChain 10).1 : ℚ) : ℝ) y ∧ Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (((Work.ELPull.Cert.uChain 10).2 : ℚ) : ℝ) y) (hcv₀ : ∀ (i : Fin 10) (Q : Work.ELPull.CoPair (Work.ELAssembly.hNcanOf d)), Q.a = ((Work.ELPull.Cert.uChain i.succ).1 : ℝ) → Q.b = ((Work.ELPull.Cert.uChain i.succ).2 : ℝ) → c ∈ Work.ELPull.arcSide (Work.ELAssembly.hNcanOf d) Q ((Work.ELPull.Cert.uChainArc i).2 : ℝ) ((Work.ELPull.Cert.uChainArc i).1 : ℝ)) : ∃ y : ℂ, Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.bAng 0) y ∧ Work.ELPull.LandsN (Work.ELAssembly.hNcanOf d) (Work.ELNest.bAng' 0) y := by
  obtain ⟨y, hy, hy'⟩ :=
    Work.ELNest.uPair_lands hc (hNcanOf d) (hφcanOf d) (htopOf (hNcanOf d)) hbase₀ hcv₀
  have hU0 : ((Work.ELPull.Cert.U0 : ℚ) : ℝ) = Work.ELNest.bAng 0 := by
    simp only [Work.ELPull.Cert.U0, Work.ELPull.qq, Work.ELNest.bAng_zero_val,
      Work.ELNest.beta0]
    norm_num
  have hU0p : ((Work.ELPull.Cert.U0p : ℚ) : ℝ) = Work.ELNest.bAng' 0 := by
    simp only [Work.ELPull.Cert.U0p, Work.ELPull.qq, Work.ELNest.bAng_zero_base,
      Work.ELNest.beta0']
    norm_num
  exact ⟨y, hU0 ▸ hy, hU0p ▸ hy'⟩

end Work.ELAssembly
