import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.a0d_comp_a0_sq`

The iterated canonical commutation relation on the algebraic core of the Fock space:

    a₀† (a₀ a₀) = (a₀ a₀) a₀† - 2 a₀ .

It is the `q = 2` case of `[a₀, (a₀†)^q] = q (a₀†)^{q-1}`, obtained here from
`Work.BoseB4.ccr` (`[a₀, a₀†] = 1`, `Defs.lean`) by a purely algebraic argument
carried out in the endomorphism ring `FockCore E →ₗ[ℂ] FockCore E`, where the ring
product is composition (`mul_eq_comp` below).
-/

namespace Work.BoseB4

set_option autoImplicit false

/-- The algebraic core of the identity: in any (noncommutative) ring, `a * b = b * a + 1`
implies `b * (a * a) = a * a * b - (a + a)`.  This is the elementary form of
`[a, b] = 1 ⟹ [a², b] = -2a`. -/
private lemma a0d_comp_a0_sq_ring_aux {R : Type*} [Ring R] {a b : R}
    (h : a * b = b * a + 1) : b * (a * a) = a * a * b - (a + a) := by
  have h' : b * a = a * b - 1 := by rw [h]; noncomm_ring
  calc b * (a * a) = (b * a) * a := by noncomm_ring
    _ = (a * b - 1) * a := by rw [h']
    _ = a * (b * a) - a := by noncomm_ring
    _ = a * (a * b - 1) - a := by rw [h']
    _ = a * a * b - (a + a) := by noncomm_ring

/-- Multiplication in the endomorphism ring `FockCore E →ₗ[ℂ] FockCore E` is
composition. -/
private lemma mul_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f g : FockCore E →ₗ[ℂ] FockCore E) : f * g = f.comp g := by
  ext x
  simp [Module.End.mul_apply]

theorem a0d_comp_a0_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (Work.BoseB4.a0d : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E).comp
        (Work.BoseB4.a0.comp Work.BoseB4.a0)
      = (Work.BoseB4.a0.comp Work.BoseB4.a0).comp Work.BoseB4.a0d
        - (2 : ℂ) • (Work.BoseB4.a0 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) := by
  have h : (a0 : FockCore E →ₗ[ℂ] FockCore E) * a0d = a0d * a0 + 1 := by
    rw [mul_eq_comp, mul_eq_comp]
    exact ccr
  have hmain := a0d_comp_a0_sq_ring_aux
    (a := (a0 : FockCore E →ₗ[ℂ] FockCore E))
    (b := (a0d : FockCore E →ₗ[ℂ] FockCore E)) h
  simp only [mul_eq_comp] at hmain
  rw [show (2 : ℂ) • (a0 : FockCore E →ₗ[ℂ] FockCore E)
        = (a0 : FockCore E →ₗ[ℂ] FockCore E) + a0 from two_smul ℂ _]
  exact hmain

end Work.BoseB4
