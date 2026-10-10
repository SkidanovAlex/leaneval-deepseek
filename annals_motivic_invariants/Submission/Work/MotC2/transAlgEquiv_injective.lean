import Mathlib
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.InfPlace
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.TransPlace
import Submission.Work.MotC2.CoordPreserved

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- **The translation map is injective on points.**

For an elliptic Weierstrass curve `E` over a field `L`, the map `Q ↦ τ_Q` from the points of `E` to
the `L`-algebra automorphisms `L(E) ≃ₐ[L] L(E)` given by `Work.MotC2.transAlgEquiv` is injective:
the translation by two points coincides only if the points do (the group `E(L) ≅ ker(τ)` is
trivial).

This is the "cancel the translations" step of the T4 (LAM) arithmetic
(`Submission/Work/MotT/twist_iso_pointK.lean`): the comparison of the twisted Galois actions yields
`τ_{σQ - Q} = τ_{A_σ}` and one must conclude the *point* equality `σQ - Q = A_σ`.

Route.  `transAlgEquiv` is a monoid homomorphism `E.toAffine.Point →* (Func E ≃ₐ[L] Func E)`
(`Work.MotC2.transAlgEquiv_add`, `Work.MotC2.transAlgEquiv_zero`), so `τ_X = τ_Y` implies
`τ_{X - Y} = τ_X * (τ_Y)⁻¹ = 1`.  If `C := X - Y` is `Point.some a b h` (the case `C = 0` is
immediate), then `C` is a nonsingular affine point and `Work.MotC2.TransPlace L E a b h` gives
`Subalgebra.map (τ_C).toAlgHom (affPlaceAt E a b) = infPlace E`, while `τ_C = 1` gives
`Subalgebra.map (τ_C).toAlgHom (affPlaceAt E a b) = affPlaceAt E a b`.  Hence
`affPlaceAt E a b = infPlace E`; but `genX E ∈ affPlaceAt E a b` (the coordinate ring is contained
in `affPlaceAt`, `algebraMap_mem_affPlaceAt`, and `genX E = algebraMap _ _ (coordX E)`) while
`genX E ∉ infPlace E` (public copy: `Submission/Work/MotC2/CoordPreserved.lean`), a contradiction. -/
theorem transAlgEquiv_injective {L : Type} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    [E.IsElliptic] : Function.Injective (Work.MotC2.transAlgEquiv E) := by
  -- `transAlgEquiv` is multiplicative, so `τ_X = τ_Y` forces `τ_{X - Y} = 1`.
  have hC : ∀ X Y : E.toAffine.Point, transAlgEquiv E X = transAlgEquiv E Y →
      transAlgEquiv E (X - Y) = 1 := by
    intro X Y hXY
    rw [sub_eq_add_neg, transAlgEquiv_add, hXY, ← transAlgEquiv_add E Y (-Y),
      add_neg_cancel, transAlgEquiv_zero]
  intro X Y hXY
  -- If `X - Y = 0` there is nothing to prove.
  rcases hP : (X - Y) with _ | ⟨a, b, hns⟩
  · exact sub_eq_zero.mp (hP.trans WeierstrassCurve.Affine.Point.zero_def.symm)
  · -- Otherwise `X - Y` is a nonsingular affine point `(a, b)` and `τ_{X-Y} = 1`.
    have hτ : transAlgEquiv E (WeierstrassCurve.Affine.Point.some a b hns) = 1 := by
      rw [← hP]
      exact hC X Y hXY
    -- The translation by `(a, b)` sends the local ring at `(a, b)` to the local ring at `O`
    -- (`TransPlace`); since `τ = 1`, it fixes it, so the two local rings coincide.
    have hmap : affPlaceAt E a b = infPlace E := by
      have h1 := (TransPlace L E a b hns).1
      rw [hτ] at h1
      rw [show ((1 : Func E ≃ₐ[L] Func E) : Func E →ₐ[L] Func E) = AlgHom.id L (Func E) from rfl,
        Subalgebra.map_id] at h1
      exact h1
    -- But `x = genX E` is regular at `(a, b)` and has a pole at `O`: contradiction.
    exact absurd (hmap ▸ algebraMap_mem_affPlaceAt E a b (coordX E)) (genX_notMem_infPlace E)

end Work.MotC2
