import Mathlib
import Submission.Work.Milnor.Clutch
import Submission.Work.Milnor.glue2_diffeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bounding 8-manifold: the open disc bundle over `S⁴`

Part (B) of Milnor's theorem (the exoticness of `Mk (-2)`) is proved by gluing a compact
8-manifold `W` with `∂W = Mk (-2)` to the standard disc `D⁸` along a supposed diffeomorphism
`Mk (-2) ≃ₘ S⁷`, and reading off the contradiction from the dimension-8 signature theorem.

This file provides the first ingredient: the **total space of the rank-4 vector bundle `ξ` over
`S⁴`**, realised in the same two-chart style as `Mk` (`Submission.Work.Milnor.Clutch`), but with
the fibre `S³` replaced by the whole quaternion line `ℍ = ℝ⁴`:

* the two charts are copies of `ℝ⁴ × ℍ = MSpace8`;
* they are glued along `{x ≠ 0} × ℍ` by `(x, y) ↦ (x/‖x‖², ûᵏ y û⁻¹)` (`û = x/‖x‖`).

Restricting the second coordinate to the unit sphere `‖y‖ = 1` recovers the clutching construction
of `Mk`, so the *unit sphere bundle* of `ξ` is `Mk k`; the closed unit disc bundle is Milnor's
`W`, and the interior of `W` is the open manifold whose atlas we set up here.

The definitions are deliberately kept in a separate file: they require no proofs, and the two
smoothness statements (`Work.Milnor.vMap_smooth`) and the inverse laws
(`Work.Milnor.vMap_inv`) are proved separately, so that they can be delegated.
-/

namespace Submission.Milnor

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

noncomputable section

/-- The total space of the trivial rank-4 bundle over one chart of `S⁴`: a base coordinate in `ℝ⁴`
and a fibre coordinate in `ℍ = ℝ⁴` (the quaternions). -/
abbrev MSpace8 : Type := EuclideanSpace ℝ (Fin 4) × Quaternion ℝ

/-- The twisting `y ↦ qᵐ y q⁻¹` of the fibre, for `m : ℤ`. -/
def vTwist (m : ℤ) (q y : Quaternion ℝ) : Quaternion ℝ := q ^ m * y * q⁻¹

/-- The inverse twisting `y ↦ q⁻ᵐ y q` of the fibre, for `m : ℤ`. -/
def vTwistInv (m : ℤ) (q y : Quaternion ℝ) : Quaternion ℝ := q ^ (-m) * y * q

/-- The clutching map of the vector bundle `ξ`: in the second chart the coordinates are
`(x/‖x‖², û⁻ᵏ y û⁻¹)`, where `û = x/‖x‖` is the unit direction. -/
def vMap (k : ℤ) (p : MSpace8) : MSpace8 :=
  (invBase p.1, vTwist (-k) ((unitDir p.1 : QS3) : Quaternion ℝ) p.2)

/-- The inverse of `vMap k`: `(x/‖x‖², ûᵏ y û)`. -/
def vMapInv (k : ℤ) (p : MSpace8) : MSpace8 :=
  (invBase p.1, vTwistInv (-k) ((unitDir p.1 : QS3) : Quaternion ℝ) p.2)

/-- The open set `{x ≠ 0} × ℍ ⊆ ℝ⁴ × ℍ` along which the two charts are glued. -/
def vOpens : Opens MSpace8 where
  carrier := {p : MSpace8 | p.1 ≠ 0}
  is_open' := isOpen_ne_fun continuous_fst continuous_const

lemma mem_vOpens {p : MSpace8} : p ∈ vOpens ↔ p.1 ≠ 0 := Iff.rfl

end

end Submission.Milnor
