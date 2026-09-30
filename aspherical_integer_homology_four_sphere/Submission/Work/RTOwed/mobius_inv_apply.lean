import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `mobius A⁻¹` inverts `mobius A`

The Möbius transformation of the upper half space model attached to a Lorentz matrix `A` is

`mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)`.

Because the Möbius action is a *right action* of the Lorentz group
(`Work.HypModel.mobius_mul`: `mobius (A * B) q = mobius A (mobius B q)` for `0 < q 3`) and the
inverse `A⁻¹` of a Lorentz matrix is again a Lorentz matrix
(`Work.FoldInst.isLorentzMat_inv`), the inverse of `mobius A` is `mobius A⁻¹`:

`mobius A⁻¹ (mobius A q) = mobius (A⁻¹ * A) q = mobius 1 q = q`.

The only algebraic input is that `A⁻¹ * A = 1` for a Lorentz matrix, proved here from
`Aᵀ * J * A = J` and `J * J = 1` alone (see `inv_mul_self_eq_one`).
-/

noncomputable section

namespace Work.RTOwed

open Matrix

/-- **A Lorentz matrix is a left inverse of its own `nonsing_inv`:** `A⁻¹ * A = 1`.

`J * Aᵀ * J` is a left inverse of `A` because
`(J * Aᵀ * J) * A = J * (Aᵀ * J * A) = J * J = 1` (using `Aᵀ * J * A = J` and `J * J = 1`),
so `Matrix.inv_eq_left_inv` identifies `A⁻¹` with `J * Aᵀ * J`, and the same computation gives
the claim. -/
private theorem inv_mul_self_eq_one {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Work.HypModel.IsLorentzMat A) : A⁻¹ * A = 1 := by
  have hBA : (Work.HypModel.J * Aᵀ * Work.HypModel.J) * A = 1 := by
    calc (Work.HypModel.J * Aᵀ * Work.HypModel.J) * A
        = Work.HypModel.J * (Aᵀ * Work.HypModel.J * A) := by noncomm_ring
      _ = Work.HypModel.J * Work.HypModel.J := by rw [hA.1]
      _ = 1 := Work.FoldInst.foldInst_J_self_mul
  rw [Matrix.inv_eq_left_inv hBA]
  exact hBA

/-- **`mobius A⁻¹` is a left inverse of `mobius A`.**  The Möbius action is a right action of the
Lorentz group, so `mobius A⁻¹ (mobius A q) = mobius (A⁻¹ * A) q`, and `A⁻¹ * A = 1` together with
`mobius 1 = id` on the upper half space finishes the proof. -/
theorem mobius_inv_apply {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : Work.HypModel.IsLorentzMat A)
    {q : Work.FoldInst.E4} (hq : 0 < q 3) :
    Work.HypModel.mobius A⁻¹ (Work.HypModel.mobius A q) = q := by
  have hAinv : Work.HypModel.IsLorentzMat A⁻¹ := Work.FoldInst.isLorentzMat_inv hA
  have hmul : Work.HypModel.mobius (A⁻¹ * A) q
      = Work.HypModel.mobius A⁻¹ (Work.HypModel.mobius A q) :=
    Work.HypModel.mobius_mul hAinv hA hq
  rw [inv_mul_self_eq_one hA, Work.HypModel.mobius_one q hq] at hmul
  exact hmul.symm

end Work.RTOwed
