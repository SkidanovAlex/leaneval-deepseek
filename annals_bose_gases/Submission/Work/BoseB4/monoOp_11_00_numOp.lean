import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.monoOp_11_00_numOp` — the `(p,q) = (1,1)` monomial is `n₀`

FS `eq:HLambdaSecond` writes the second-quantised Hamiltonian as a finite sum of
anti-normal monomials `monoOp p q B = a₀^p (a₀†)^q ⊗ B`.  The special case
`(p,q) = (1,1)` is the *normal-ordered* number operator of the condensate,

    `a₀ a₀† = a₀† a₀ + 1 = n₀ + 1`,

so `monoOp 1 1 B − monoOp 0 0 B = n₀ ⊗ B`.  That is exactly the identity proved
here, and it is what lets one split off the "spectator number operator" part of
a monomial: the anti-normal ordering `a₀ a₀†` differs from the normal one only by
the vacuum commutator `[a₀, a₀†] = 1`, acting as `lift (-B)`.

The proof is the canonical commutation relation `ccr` (`[a₀,a₀†] = 1` on the
core, `Defs.lean`) pushed through `lift B`, which commutes with `a₀` and `a₀†`
(`lift_comm_a0`, `lift_comm_a0d`).
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

/-- `1 ∘ f = f` in the exact (numeral) shape in which `a0pow 0` / `a0dpow 0`
produce the identity on the core.  `LinearMap.id_comp` does not fire on
`1 ∘ₗ f` because that `1` is an `OfNat` numeral rather than the literal
`LinearMap.id`. -/
private lemma one_comp_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : FockCore E →ₗ[ℂ] FockCore E) :
    (1 : FockCore E →ₗ[ℂ] FockCore E).comp f = f := by
  ext x; simp

theorem monoOp_11_00_numOp {m : ℕ} [NeZero m]
    (B : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    Work.BoseB4.monoOp 1 1 B + Work.BoseB4.monoOp 0 0 (-B)
      = Work.BoseB4.numOp.comp (Work.BoseB4.lift B) := by
  -- `a0pow 1 = a0` and `a0dpow 1 = a0d` (up to the numeral identity on the core).
  have h1 : monoOp 1 1 B = a0.comp (a0d.comp (lift B)) := by
    simp only [monoOp, a0pow_zero, a0pow_succ, a0dpow_zero, a0dpow_succ]
    rw [one_comp_core, one_comp_core]
  -- `monoOp 0 0 (-B) = lift (-B) = -lift B`.
  have h0 : monoOp 0 0 (-B) = -lift B := by
    simp only [monoOp, a0pow_zero, a0dpow_zero]
    rw [one_comp_core, one_comp_core]
    ext x; simp
  -- Now `a₀ (a₀† ⊗ B) − B = n₀ ⊗ B` is the commutator `[a₀,a₀†] = 1`.
  rw [h1, h0, numOp, ← LinearMap.comp_assoc, ccr, LinearMap.add_comp]
  rw [one_comp_core]
  abel

end Work.BoseB4
