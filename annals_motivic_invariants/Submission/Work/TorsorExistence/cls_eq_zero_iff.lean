import Mathlib
import Submission.Work.TorsorExistence.Twist

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.TorsorExistence

/-- **The coboundary criterion.**  The class of the cocycle `σ ↦ P` in
`H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` is trivial if and only if `P` is a coboundary, i.e. iff
`(σ - 1)R = P` for some `R ∈ E(L)`.  Geometrically (Galois descent for the twisted action
`g ⋆ Q = g·Q + P`): the twist `C` has a `𝕜`-point iff the class is trivial. -/
theorem cls_eq_zero_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    D.cls = 0 ↔ ∃ R : D.LPoints, D.shift R = D.PL := by
  -- `PL` lies in `ker N`; name that cocycle.
  have hx : D.PL ∈ D.cocycles := by
    rw [QuinticTwist.cocycles, AddMonoidHom.mem_ker]; exact D.norm_PL
  -- `cls` is the class of this cocycle.
  have hcls : D.cls = QuotientAddGroup.mk' D.coboundaries (⟨D.PL, hx⟩ : D.cocycles) := by
    show QuotientAddGroup.mk' D.coboundaries (⟨D.PL, D.norm_PL⟩ : D.cocycles) =
      QuotientAddGroup.mk' D.coboundaries (⟨D.PL, hx⟩ : D.cocycles)
    congr 1
  -- the class of a cocycle is zero iff the cocycle is a coboundary.
  have hiff : (QuotientAddGroup.mk' D.coboundaries (⟨D.PL, hx⟩ : D.cocycles) = 0) ↔
      (⟨D.PL, hx⟩ : D.cocycles) ∈ D.coboundaries :=
    QuotientAddGroup.eq_zero_iff _
  rw [hcls, hiff]
  -- `coboundaries = (σ - 1)E(L)` inside `ker N`; unwrap the `comap`/`map`.
  constructor
  · intro h
    rw [QuinticTwist.coboundaries, AddSubgroup.mem_comap, AddSubgroup.mem_map] at h
    obtain ⟨x, _, hx'⟩ := h
    exact ⟨x, hx'⟩
  · rintro ⟨R, hR⟩
    rw [QuinticTwist.coboundaries, AddSubgroup.mem_comap, AddSubgroup.mem_map]
    exact ⟨R, trivial, hR⟩

end Work.TorsorExistence
