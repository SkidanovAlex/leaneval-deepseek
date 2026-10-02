/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.g_mem_of_split`

The two split fixed points `m c ± E c/2` of the second return map `F c = (T_c)^{10}` are
*continuous* in the parameter `c` (`SplitData.cont_m`, `SplitData.cont_E`) and collapse onto the
parabolic point `d.z₁` at `c = c₀` (`SplitData.m₀`, `SplitData.E₀`).  The antiholomorphic square
root `gtc c = (T_c)^[5]` of `F c` is jointly continuous in `(c, z)`.  Hence the image
`gtc c (m c + E c/2)` of the first split point is continuous in `c` and equals `d.z₁` at `c₀`
(because `d.z₁` is fixed by `gtc c₀`, `RootParabolic.per_half`).  Since `d.z₁` lies in the *open*
disc `ball d.z₁ S.R`, continuity at `c₀` gives a whole parameter ball on which the image stays in
that disc.  This is the hypothesis `hmem` of `SplitData.swap_or_fix_of_split`, so that the
`swap`/`fix` dichotomy applies on a ball of parameters.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- **Joint continuity of `(c, z) ↦ gtc c z = (T_c)^[5] z`.**  The parameter-dependent iterate
is the second component of the fifth iterate of the continuous map
`(c, z) ↦ (c, T_c z)` on `ℂ × ℂ`. -/
theorem continuous_gtc_prod :
    Continuous fun p : ℂ × ℂ => (Tantibar p.1)^[5] p.2 := by
  have hTmap : Continuous fun p : ℂ × ℂ => (p.1, Tantibar p.1 p.2) := by
    refine continuous_fst.prodMk ?_
    unfold LeanEval.ComplexAnalysis.Tantibar
    fun_prop
  have key : (fun p : ℂ × ℂ => (Tantibar p.1)^[5] p.2)
      = fun p => ((fun p : ℂ × ℂ => (p.1, Tantibar p.1 p.2))^[5] p).2 := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [Function.iterate_succ_apply']
    rfl
  rw [key]
  exact continuous_snd.comp (hTmap.iterate 5)

theorem g_mem_of_split {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ S.ρ ∧
      ∀ c ∈ Metric.ball c₀ ρ', gtc c (S.m c + S.E c / 2) ∈ Metric.ball d.z₁ S.R := by
  -- the curve `c ↦ gtc c (m c + E c/2)` is continuous at `c₀`
  have hmem : c₀ ∈ ball c₀ S.ρ := mem_ball_self S.hρ
  have hm : ContinuousAt S.m c₀ := S.cont_m.continuousAt (isOpen_ball.mem_nhds hmem)
  have hE : ContinuousAt S.E c₀ := S.cont_E.continuousAt (isOpen_ball.mem_nhds hmem)
  have hpair : ContinuousAt (fun c : ℂ => (c, S.m c + S.E c / 2)) c₀ :=
    continuousAt_id.prodMk (hm.add (hE.div_const 2))
  have hcontΦ' : ContinuousAt (fun c : ℂ => (Tantibar c)^[5] (S.m c + S.E c / 2)) c₀ :=
    ContinuousAt.comp (f := fun c : ℂ => (c, S.m c + S.E c / 2)) (x := c₀)
      continuous_gtc_prod.continuousAt hpair
  have hcontΦ : ContinuousAt (fun c : ℂ => gtc c (S.m c + S.E c / 2)) c₀ := hcontΦ'
  -- its value at `c₀` is `d.z₁`, which lies in the open disc `ball d.z₁ S.R`
  have hbase : gtc c₀ (S.m c₀ + S.E c₀ / 2) = d.z₁ := by
    rw [S.m₀, S.E₀, zero_div, add_zero]
    exact d.per_half
  have hmem0 : gtc c₀ (S.m c₀ + S.E c₀ / 2) ∈ ball d.z₁ S.R := by
    rw [hbase]; exact mem_ball_self S.hR
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp
    (hcontΦ.preimage_mem_nhds (isOpen_ball.mem_nhds hmem0))
  exact ⟨min S.ρ ε, lt_min S.hρ hε0, min_le_left _ _, fun c hc =>
    hε (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) (min_le_right _ _)))⟩

end Work.PARIMPL.ParSplit
