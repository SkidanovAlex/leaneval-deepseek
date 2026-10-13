/-
# `Submission/Work/FTS_MuLipC/Main.lean` — **the deliverable** `Work.FTS_MuLipC.muLipC_pExp`

The frozen producer `Work.FTS.FinalV2.muLipC_pExp` (conjunct (1c) of `FinalV2.Producers`),
proved here from the three difference rows of this area:

* `Work.FTS_MuLipC.diffRow0` (`RowN0/diffRow0.lean`) — the quadratic block `N₀`,
* `Work.FTS_MuLipC.diffRow1` (`RowN/diffRow1.lean`) — the bilinear block `N`,
* `Work.FTS_MuLipC.diffRow2` (`RowT/diffRow2.lean`) — the transport block,

glued by `muLipC_of_diffRows` (`Defs.lean`).  The threshold `α₂` only has to make
`pExp α ≤ 1` and `C₀·(pExp α)² ≤ 1` hold; the profile is `pExp α = 3α`.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS_MuLipC.RowN0.diffRow0
import Submission.Work.FTS_MuLipC.RowN.diffRow1
import Submission.Work.FTS_MuLipC.RowT.diffRow2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_MuLipC

open Work.FTS.Galerkin (Fn Fam slice muDyn)

set_option autoImplicit false

/-- **The class-`C` Lipschitz bound of the modulation, at the profile exponent
`pExp α = 3α`** — the frozen producer `Work.FTS.FinalV2.muLipC_pExp` (conjunct (1c) of the
final interface `Inputs'`, `FinalV2/Producers.lean`).

The threshold is `α₂ = min (1/4) (1/(4 + 12·C₀))`, which makes both `pExp α ≤ 1` and
`C₀·(pExp α)² ≤ 1` hold. -/
theorem muLipC_pExp {C₀ Ce Cs : ℝ} (hC₀ : 0 < C₀) :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ {Φs : Fn} {E : Fn →ₗ[ℝ] Fn},
      Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs →
      (∀ f : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) f →
        Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp α) Ce f (E f)) →
      Work.FTS.FinalV2.MuLipC (Work.FTS.Regularity.pExp α) C₀ Φs E := by
  refine ⟨min (1 / 4) (1 / (4 + 12 * C₀)), lt_min (by norm_num) (by positivity), ?_⟩
  intro α hα Φs E hstar hell
  have hα0 : 0 < α := hα.1
  have hαb : α ≤ 1 / (4 + 12 * C₀) := le_trans hα.2 (min_le_right _ _)
  have hαq : α ≤ 1 / 4 := by
    have := le_trans hα.2 (min_le_left (1 / 4 : ℝ) (1 / (4 + 12 * C₀)))
    linarith
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα0
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := by
    rw [Work.FTS.Regularity.pExp_eq]; linarith
  have hsmall : C₀ * (Work.FTS.Regularity.pExp α) ^ 2 ≤ 1 := by
    have hden : (0 : ℝ) < 4 + 12 * C₀ := by positivity
    have hmul : α * (4 + 12 * C₀) ≤ 1 := by
      rw [le_div_iff₀ hden] at hαb
      linarith
    have hCα : C₀ * α ≤ 1 / 12 := by nlinarith
    have hstep : C₀ * α ^ 2 ≤ (1 / 12) * (1 / 4) := by
      calc C₀ * α ^ 2 = α * (C₀ * α) := by ring
        _ ≤ (1 / 4) * (1 / 12) := mul_le_mul hαq hCα (by positivity) (by norm_num)
        _ = (1 / 12) * (1 / 4) := by ring
    rw [Work.FTS.Regularity.pExp_eq]
    have h3 : C₀ * (3 * α) ^ 2 = 9 * (C₀ * α ^ 2) := by ring
    rw [h3]
    linarith
  have hEadd : ∀ a b : Fn, (⇑E) (a - b) = (⇑E) a - (⇑E) b := fun a b => E.map_sub a b
  have hEsmul : ∀ (c : ℝ) (a : Fn), (⇑E) (c • a) = c • (⇑E) a := fun c a => E.map_smul c a
  exact muLipC_of_diffRows hp0
    (Work.FTS_MuLipC.RowN0.diffRow0 hp0 hp1 hsmall)
    (Work.FTS_MuLipC.RowN.diffRow1 hp0 hp1 hsmall hEadd hEsmul hstar hell)
    (Work.FTS_MuLipC.RowT.diffRow2 hp0 hp1)

end Work.FTS_MuLipC
