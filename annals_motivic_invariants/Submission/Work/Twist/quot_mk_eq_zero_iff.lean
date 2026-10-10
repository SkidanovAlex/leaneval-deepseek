import Mathlib
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- The class of a cocycle `y ∈ ker N` in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` vanishes if and
only if `y` is a coboundary.  This is `Work.TorsorExistence.cls_eq_zero_iff` (the special case
`y = P`) for an arbitrary cocycle, and it is what turns the divisor-degree condition
`n • cls = 0` of the twist into the statement `∃ R, σ R - R = n • P`.

`D.cocycles = (D.norm).ker ⊆ D.LPoints` and `D.coboundaries = (σ - 1)E(L)` viewed inside
`D.cocycles` are defined in `Submission/Work/TorsorExistence/Twist.lean`; the proof is the same
unwinding as `cls_eq_zero_iff` (`QuotientAddGroup.eq_zero_iff`, then `AddSubgroup.mem_comap` /
`mem_map`), not using anything about `P`. -/
theorem quot_mk_eq_zero_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (y : D.LPoints) (hy : y ∈ D.cocycles) :
    (QuotientAddGroup.mk' D.coboundaries ⟨y, hy⟩ : D.H1) = 0 ↔
      ∃ R : D.LPoints, D.shift R = y := by
  have hiff : ((QuotientAddGroup.mk' D.coboundaries ⟨y, hy⟩ : D.H1) = 0) ↔
      (⟨y, hy⟩ : D.cocycles) ∈ D.coboundaries :=
    QuotientAddGroup.eq_zero_iff _
  rw [hiff]
  constructor
  · intro h
    rw [Work.TorsorExistence.QuinticTwist.coboundaries, AddSubgroup.mem_comap,
      AddSubgroup.mem_map] at h
    obtain ⟨x, _, hx⟩ := h
    exact ⟨x, hx⟩
  · rintro ⟨R, hR⟩
    rw [Work.TorsorExistence.QuinticTwist.coboundaries, AddSubgroup.mem_comap,
      AddSubgroup.mem_map]
    exact ⟨R, trivial, hR⟩

end Work.Twist
