import Mathlib
import Submission.Work.Mostow.mlDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! The inverse of a loxodromic element is loxodromic with the same pair.

Use the Busemann cocycle clause of `HypIsometryProp`: for `ξ ∈ Sph n` and any `u : E n`,
`busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0)`.

* `bd a⁻¹ x = x`: `bd (a⁻¹ * a) x = bd a⁻¹ (bd a x) = bd a⁻¹ x` by the multiplicativity of `bd`
  (`POActionProp`), while `bd (a⁻¹ * a) x = bd 1 x = x`; likewise for `y`.
* `busemann x (a⁻¹ • 0) = - busemann x (a • 0) ≠ 0`: apply the cocycle clause with `g := a`, `ξ := x`,
  `u := a⁻¹ • 0`; the left side is `busemann x (a • (a⁻¹ • 0)) = busemann x 0 = 0` (action law
  `(g * h) • u = g • (h • u)` and `busemann x 0 = Real.log 1 = 0`), giving
  `0 = busemann x (a⁻¹ • 0) + busemann x (a • 0)`. -/
theorem loxPairInv (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {a : LeanEval.Geometry.MostowRigidity.PO n 1}
    {x y : Submission.Mostow.E n} (h : Submission.Mostow.LoxPair a x y) :
    Submission.Mostow.LoxPair a⁻¹ x y := by
  obtain ⟨hx, hy, hxy, hax, hay, hβ⟩ := h
  -- a boundary point fixed by `a` is fixed by `a⁻¹`
  have hfix : ∀ {ξ : E n}, ξ ∈ Sph n → bd a ξ = ξ → bd a⁻¹ ξ = ξ := by
    intro ξ hξ hξ'
    have h1 : bd (a⁻¹ * a) ξ = bd a⁻¹ (bd a ξ) :=
      hA.2.2.2.2.2.2.2.2.2.1 a⁻¹ a ξ hξ
    rw [inv_mul_cancel, hA.2.2.2.2.2.2.2.2.1 ξ hξ, hξ'] at h1
    exact h1.symm
  refine ⟨hx, hy, hxy, hfix hx hax, hfix hy hay, ?_⟩
  -- the Busemann cocycle at `g := a`, `ξ := x`, `u := a⁻¹ • 0`
  have hcoc := hI.2.2.2.2.2.2.2.2.2.2.2.2 a x (a⁻¹ • (0 : E n)) hx
  have hact : a • (a⁻¹ • (0 : E n)) = (0 : E n) := by
    rw [← hA.2.2.2.2.1 a a⁻¹ (0 : E n), mul_inv_cancel, hA.2.2.2.1 (0 : E n)]
  rw [hact, hax, busemann_zero] at hcoc
  -- `0 = busemann x (a⁻¹ • 0) + busemann x (a • 0)`
  intro h0
  rw [h0, zero_add] at hcoc
  exact hβ hcoc.symm

end Work.Mostow
