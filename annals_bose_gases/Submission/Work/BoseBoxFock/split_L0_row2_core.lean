import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.TildeDataInst
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-!
# `Work.BoseBoxFock.split_L0_row2_core`

The "row 2" of the anti-normal dictionary of FS §8: on the algebraic core of the
Fock space with the spectator operator `lift B` inserted at the *inner* position,

    a₀† (lift B (a₀† (a₀ y))) = (monoOp 1 2 B − 2 • monoOp 0 1 B) y .

Writing `A = a₀`, `Ad = a₀†`, `L = lift B` (the spectator lift, which commutes
with `a₀` and `a₀†`), the left-hand side is

    Ad (L (Ad (A y))) = Ad (Ad (A (L y))) = (Ad ∘ Ad ∘ A) (L y) ,

while `monoOp 1 2 B = A ∘ Ad ∘ Ad ∘ L` and `monoOp 0 1 B = Ad ∘ L`.  So the
identity is the second-order canonical commutation relation
`Ad² A = A Ad² − 2 Ad` (`Work.BoseB4.a0_comp_a0d_sq`) pushed through the lift.

## Proof

Everything is done at the level of the core vector `y`:

1. `monoOp 1 2 B` is unfolded to `a0 ∘ (a0d ∘ a0d) ∘ lift B` (`monoOp` is
   `a0pow 1 ∘ a0dpow 2 ∘ lift B`, and `a0pow 1 = a₀`, `a0dpow 2 = a₀†a₀†`);
   `monoOp 0 1 B` is `a0d ∘ lift B` (`Work.BoseB4.monoOp_zero_one`).
2. `lift B` is moved past `a₀†` and then past `a₀` with `Work.BoseB4.lift_a0d`,
   `Work.BoseB4.lift_a0`, turning the left-hand side into
   `a₀† (a₀† (a₀ (lift B y)))`.
3. The right-hand side becomes `a₀ (a₀† (a₀† (lift B y))) − 2 • a₀† (lift B y)`,
   and `Work.BoseB4.a0_comp_a0d_sq`, applied to `lift B y`, is exactly
   `a₀ (a₀† (a₀† w)) = a₀† (a₀† (a₀ w)) + 2 • a₀† w`.  Substituting it and
   cancelling the two `2 • a₀† (lift B y)` terms closes the goal.
-/

/-- `1 ∘ₗ f = f` in the numeral shape in which `a0pow 0` / `a0dpow 0` present the
identity on the core (`LinearMap.id_comp` does not fire on the `OfNat` numeral). -/
private lemma one_comp_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) :
    (1 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E).comp f = f := by
  rw [show (1 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) = LinearMap.id from rfl,
    LinearMap.id_comp]

theorem split_L0_row2_core {m : ℕ} [NeZero m]
    (B : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (y : ℕ →₀ Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    Work.BoseB4.a0d (Work.BoseB4.lift B (Work.BoseB4.a0d (Work.BoseB4.a0 y)))
      = (Work.BoseB4.monoOp 1 2 B - (2 : ℂ) • Work.BoseB4.monoOp 0 1 B) y := by
  -- `monoOp 1 2 B = a₀ ∘ (a₀† ∘ a₀†) ∘ lift B`, i.e. `a0pow 1 = a₀` and `a0dpow 2 = a₀†a₀†`.
  have hmono1 : Work.BoseB4.monoOp 1 2 B
      = Work.BoseB4.a0.comp ((Work.BoseB4.a0d.comp Work.BoseB4.a0d).comp (Work.BoseB4.lift B)) := by
    simp only [Work.BoseB4.monoOp, Work.BoseB4.a0pow_zero, Work.BoseB4.a0pow_succ,
      Work.BoseB4.a0dpow_zero, Work.BoseB4.a0dpow_succ]
    rw [one_comp_core, one_comp_core]
  -- `monoOp 0 1 B = a₀† ∘ lift B` and the pointwise form of the difference.
  rw [hmono1, Work.BoseB4.monoOp_zero_one]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- `lift B` commutes with `a₀†` and with `a₀`, so it moves to the right.
  rw [Work.BoseB4.lift_a0d, Work.BoseB4.lift_a0]
  -- The second-order CCR `a₀†a₀†a₀ = a₀a₀†a₀† − 2a₀†`, applied to `lift B y`.
  have hsq := congrArg (fun f : Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) →ₗ[ℂ]
      Work.BoseB4.FockCore (Work.BoseB4.cfock (Work.BoseB4.Excited m)) =>
      f (Work.BoseB4.lift B y))
    (Work.BoseB4.a0_comp_a0d_sq (E := Work.BoseB4.cfock (Work.BoseB4.Excited m)))
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hsq
  rw [hsq]
  abel

end Work.BoseBoxFock
