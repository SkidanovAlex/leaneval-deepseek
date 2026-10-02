import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.MRMT.Found.exists_homeomorph_of_localInj_proper
import Submission.Work.SeedDyn.varphiCrit_comm_Tsq
import Submission.Work.Bottcher.Inverse.injOn_far

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Injectivity of the canonical critical Böttcher coordinate far out.**

For `c ∈ M*` and `φ = varphiCrit c`, the far region `{z | farR c ≤ ‖z‖}` lies in the escaping
set and `φ` is injective there.

The four Böttcher hypotheses of `Work.Bottcher.Inverse.injOn_far` hold for `φ = varphiCrit c`
on the escape set `{G_c > 0} = esc c`:

* `φ` is analytic there (`analyticOnNhd_varphiCrit_esc`),
* `φ ∘ p_c = φ^4` (`varphiCrit_comm_Tsq`, with `p_c = Tsq c` the holomorphic second iterate),
* `‖φ z‖ = exp (G_c z)` (`norm_varphiCrit_esc`),
* `φ z / z → 1` at infinity (`Work.Bottcher.varphiCrit_div_tendsto_one`).

Hence `injOn_far` gives injectivity on `{farR c ≤ ‖z‖}`, and the same radius bounds the far
region inside `esc c` because `escapeRadius c ≤ farR c`. -/
theorem injOn_varphiCrit_far {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (hderiv : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖deriv (Work.Bottcher.varphiCrit c) z - 1‖ ≤ ε) :
    ∃ R : ℝ, {z : ℂ | R ≤ ‖z‖} ⊆ Work.SeedDyn.esc c ∧
      Set.InjOn (Work.Bottcher.varphiCrit c) {z : ℂ | R ≤ ‖z‖} := by
  -- membership in the escape set, in terms of `Work.Bottcher.green`
  have hmem : ∀ z : ℂ, z ∈ Work.SeedDyn.esc c ↔ 0 < Work.Bottcher.green c z := by
    intro z
    rw [mem_esc, ← Work.ParamRays.greenFun_pos_iff_escaping,
      ← Work.Bottcher.CritBasic.green_eq]
  -- the analyticity hypothesis of `injOn_far`
  have han : AnalyticOnNhd ℂ (Work.Bottcher.varphiCrit c)
      {z : ℂ | 0 < Work.Bottcher.green c z} :=
    (analyticOnNhd_varphiCrit_esc hc).mono (fun z hz => (hmem z).mpr hz)
  -- the functional equation `φ ∘ p_c = φ^4`
  have hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      Work.Bottcher.varphiCrit c (Work.Bottcher.pMap c z)
        = (Work.Bottcher.varphiCrit c z) ^ 4 := by
    intro z hz
    have hzesc : z ∈ Work.SeedDyn.esc c := (hmem z).mpr hz
    have hpT : Work.Bottcher.pMap c z = Work.Landing.Tsq c z := by
      rw [Work.Bottcher.pMap_eq_iterate_two, Work.ELPull.Tsq_eq_iterate]
    rw [hpT, varphiCrit_comm_Tsq hc hzesc]
  -- the modulus hypothesis of `injOn_far`
  have hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖Work.Bottcher.varphiCrit c z‖ = Real.exp (Work.Bottcher.green c z) := by
    intro z hz
    have hzesc : z ∈ Work.SeedDyn.esc c := (hmem z).mpr hz
    rw [norm_varphiCrit_esc hc hzesc, ← Work.Bottcher.CritBasic.green_eq]
  -- the tangency hypothesis of `injOn_far`
  have has : Filter.Tendsto (fun z : ℂ => Work.Bottcher.varphiCrit c z / z)
      (Filter.cocompact ℂ) (nhds (1 : ℂ)) :=
    Work.Bottcher.varphiCrit_div_tendsto_one c
  refine ⟨Work.Bottcher.Inverse.farR c, ?_, ?_⟩
  · -- the far region is escaping
    intro z hz
    exact (hmem z).mpr
      (Work.Bottcher.Inverse.green_pos_of_escapeRadius_le c z
        (le_trans (Work.Bottcher.Inverse.escapeRadius_le_farR c) hz))
  · -- injectivity on the far region
    intro z₁ hz₁ z₂ hz₂ hφ
    exact Work.Bottcher.Inverse.injOn_far c (Work.Bottcher.varphiCrit c)
      han hfe hmod has hz₁ hz₂ hφ

end Work.SeedDyn
