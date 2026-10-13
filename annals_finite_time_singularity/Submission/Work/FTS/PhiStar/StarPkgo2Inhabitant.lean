import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.StarPkgo2OfCore
import Submission.Work.FTS.PhiStar.StarCoreInhabitant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.StarPkgo2Inhabitant` — the packaged star node

`StarPkgo2 α Cs Φ_*` for every `0 < α ≤ α₀`, obtained by composing the analysis node
`StarCore_inhabitant` (the flat bound on `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ`) with the purely algebraic
conversion `StarPkgo2OfCore`.
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The star package, inhabited.** -/
theorem StarPkgo2_inhabitant : ∃ Cs α₀ : ℝ, 0 < Cs ∧ 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ Φs : Fn, Work.FTS.VocabO2.StarPkgo2 α Cs Φs := by
  obtain ⟨C, hC, hconv⟩ := StarPkgo2OfCore
  obtain ⟨Cs0, hCs0, hinh⟩ := StarCore_inhabitant
  refine ⟨C * Cs0, 1 / 5, by positivity, by norm_num, fun α hα hα5 => ?_⟩
  obtain ⟨Φs, hΦs⟩ := hinh α hα hα5
  exact ⟨Φs, hconv α Cs0 Φs hα (by linarith) hCs0 hΦs⟩

/-- **The frozen `StarPkgo` too** — `StarPkgo2` extends it, so the older node name is an
immediate corollary (this is the form the pre-2026-10-06 consumers use). -/
theorem StarPkgo_inhabitant : ∃ Cs α₀ : ℝ, 0 < Cs ∧ 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∃ Φs : Fn, Work.FTS.VocabO.StarPkgo α Cs Φs := by
  obtain ⟨Cs, α₀, hCs, hα₀, h⟩ := StarPkgo2_inhabitant
  refine ⟨Cs, α₀, hCs, hα₀, fun α hα hαα => ?_⟩
  obtain ⟨Φs, hΦs⟩ := h α hα hαα
  exact ⟨Φs, hΦs.toStarPkgo⟩

end Work.FTS.PhiStar
