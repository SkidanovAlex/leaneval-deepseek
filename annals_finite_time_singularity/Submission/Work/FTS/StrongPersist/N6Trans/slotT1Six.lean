/-
Copyright: work module for the Elgindi finite-time singularity project.

# `slotT1Six` — the level-six per-slot `D_θ`-transport bound

The target `Work.FTS.StrongPersist.N6Trans.slotT1Six`: for `a + b ≤ 6`, every leaf weight `ρ`
of `IP6` and `f, g` smooth on the open quadrant with honest `HkMem α 6`,

  `|slotPairing ρ a b (f · D_θ g) g| ≤ C α^{-1/2} |f|_{ℋ⁶} |g|²_{ℋ⁶}`

uniformly in `α ∈ (0,1]`.  The generic-exponent estimate is `slotT1SixAux`
(`Submission/Work/FTS/StrongPersist/N6Trans/T1SixAux/AuxProof.lean`); the case analysis of the
leaf weight `ρ` is `T1SixAux.leafW_canon_cases`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false

/-- **The level-six per-slot `D_θ`-transport bound** (`slotT1Six`). -/
theorem slotT1Six : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f g : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f
            * (Work.Spaces.HkNorm α 6 g) ^ 2 := by
  obtain ⟨K, hK0, hmain⟩ := slotT1SixAux
  refine ⟨K, 1, hK0, by norm_num, ?_⟩
  intro α hα f g a b ρ hF hmF hG hmG hab hρ
  obtain ⟨q, hρeq, hq0, hqγ, hqη⟩ :=
    Work.FTS.StrongPersist.N6Trans.T1SixAux.leafW_canon_cases hα.1 hρ
  rw [hρeq]
  have h := hmain α q f g a b hα.1 hα.2 hF hmF hG hmG hab hq0 hqγ hqη
  have hsq : Work.Spaces.HkNorm α 6 g ^ 2 = Work.Spaces.HkSq α 6 g :=
    Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)
  rw [hsq]
  exact h

end Work.FTS.StrongPersist.N6Trans
