import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- Degenerate case of the local-obstruction criterion: if `σ` acts trivially on `E(L)` (i.e.
`E(L) = E(𝕜)`, as happens for a constant elliptic curve over a rational function field with
algebraically closed constants), then `(σ - 1)E(L) = 0` and the twist is pointless as soon as
`P ≠ 0`. -/
theorem pointless_of_galMap_eq {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : ∀ x : D.LPoints, D.galMap x = x) : D.Pointless := by
  -- `σ` fixes every point of `E(L)`, so the shift `σ - 1` vanishes identically: the subgroup of
  -- coboundaries `(σ - 1)E(L)` in `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` is trivial.
  have hshift : ∀ x : D.LPoints, D.shift x = 0 := by
    intro x
    rw [show D.shift x = D.galMap x - x from rfl, h x, sub_self]
  -- The marked point `P` has exact order `5`, hence is non-zero, and base change `E(𝕜) → E(L)`
  -- is injective, so `P` is still non-zero in `E(L)`.
  have hPL : D.PL ≠ 0 := by
    intro h0
    refine D.P_ne_zero (WeierstrassCurve.Affine.Point.map_injective (W' := D.E)
      (f := Algebra.ofId 𝕜 D.ext.L) ?_)
    exact h0
  -- Hence `P` is not a coboundary, i.e. its class in `ker N / (σ - 1)E(L)` is non-zero.
  intro hcls
  have hmem : (⟨D.PL, D.norm_PL⟩ : D.cocycles) ∈ D.coboundaries :=
    (QuotientAddGroup.eq_zero_iff (N := D.coboundaries) ⟨D.PL, D.norm_PL⟩).mp hcls
  rw [show D.coboundaries = (AddSubgroup.map D.shift ⊤).comap (D.cocycles).subtype from rfl,
    AddSubgroup.mem_comap, AddSubgroup.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  simp only [AddSubgroup.coe_subtype] at hy
  exact hPL (by rw [← hy, hshift y])

end Work.PointlessIndexFive
