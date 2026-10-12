import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.monoOp_apply_lift` — the monomial with `lift B` moved outside

The anti-normal monomial is defined as

    `monoOp p q B = a₀^p ∘ ((a₀†)^q ∘ lift B)`,

i.e. `a₀^p (a₀†)^q (lift B ·)`: the spectator operator `B` sits *inside*, next to the
core vector.  Since `lift B` commutes with `a₀` (`lift_comm_a0`) and with `a₀†`
(`lift_comm_a0d`), it commutes with every power `a0pow p` / `a0dpow q`, so `B` may
just as well be applied *outside*:

    `monoOp p q B v = lift B (a₀^p (a₀†)^q v)`.

This is the form in which the monomial can be evaluated on a vector of the core
whose spectator component is untouched by the condensate ladders.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Function-level form of `lift_comm_a0`: `lift B` commutes with `a₀`. -/
lemma lift_a0 (B : E →ₗ[ℂ] E) (w : FockCore E) : lift B (a0 w) = a0 (lift B w) := by
  have := congrArg (fun f : FockCore E →ₗ[ℂ] FockCore E => f w) (lift_comm_a0 B)
  simpa using this

/-- Function-level form of `lift_comm_a0d`: `lift B` commutes with `a₀†`. -/
lemma lift_a0d (B : E →ₗ[ℂ] E) (w : FockCore E) : lift B (a0d w) = a0d (lift B w) := by
  have := congrArg (fun f : FockCore E →ₗ[ℂ] FockCore E => f w) (lift_comm_a0d B)
  simpa using this

/-- `lift B` commutes with every power `a₀^p` of condensate annihilation. -/
lemma lift_a0pow (B : E →ₗ[ℂ] E) (p : ℕ) (w : FockCore E) :
    lift B (a0pow p w) = a0pow p (lift B w) := by
  induction p generalizing w with
  | zero => simp
  | succ d ih =>
    rw [a0pow_succ, LinearMap.comp_apply, ih (a0 w), lift_a0, ← LinearMap.comp_apply,
      ← a0pow_succ]

/-- `lift B` commutes with every power `(a₀†)^q` of condensate creation. -/
lemma lift_a0dpow (B : E →ₗ[ℂ] E) (q : ℕ) (w : FockCore E) :
    lift B (a0dpow q w) = a0dpow q (lift B w) := by
  induction q generalizing w with
  | zero => simp
  | succ d ih =>
    rw [a0dpow_succ, LinearMap.comp_apply, ih (a0d w), lift_a0d, ← LinearMap.comp_apply,
      ← a0dpow_succ]

theorem monoOp_apply_lift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p q : ℕ) (B : E →ₗ[ℂ] E) (v : Work.BoseB4.FockCore E) :
    Work.BoseB4.monoOp p q B v = Work.BoseB4.lift B (Work.BoseB4.a0pow p (Work.BoseB4.a0dpow q v)) := by
  simp only [monoOp, LinearMap.comp_apply]
  rw [← lift_a0dpow B q v, ← lift_a0pow B p (a0dpow q v)]

end Work.BoseB4
