import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius

namespace Work.DSTR.M110.twistAux

open OnePoint

/-- An order-two permutation of the projective line whose value on the affine part is
`z ↦ a·σz + b` forces the norm condition `a·σa = 1`.

The point is that `hform` is already enough to iterate `y`: for each field element `z` the
value `a·σz + b` again lies in the affine part, so `y` can be applied a second time by the
same formula.  Comparing `y (y z) = z` with the computed value gives, for all `z`,
`(a·σa)·(σ(σz)) + (a·σb + b) = z`; evaluating at `z = 0` kills the constant term and then
`z = 1` gives `a·σa = 1`.  In particular `a ≠ 0` follows. -/
theorem twistAuxOrderTwoAffineNorm (F : Type*) [Field F] [DecidableEq F]
    (σ : F ≃+* F) (a b : F) (y : Equiv.Perm (Work.AUTL2.P1 F))
    (hform : ∀ z : F, y (z : Work.AUTL2.P1 F) = ((a * σ z + b : F) : Work.AUTL2.P1 F))
    (hy2 : y * y = 1) : a * σ a = 1 := by
  -- `y` is an involution, pointwise.
  have hy2' : ∀ x : Work.AUTL2.P1 F, y (y x) = x := by
    intro x
    have h := DFunLike.congr_fun hy2 x
    simpa using h
  -- Iterating the formula: `y (y z) = (a·σa)·(σ(σz)) + (a·σb + b)`.
  have hkey : ∀ z : F, a * σ (a * σ z + b) + b = z := by
    intro z
    have h := hy2' (z : Work.AUTL2.P1 F)
    rw [hform z, hform (a * σ z + b)] at h
    simpa using h
  -- The constant term vanishes.
  have h0 : a * σ b + b = 0 := by
    have := hkey 0
    simpa using this
  -- Evaluating at `1` then gives the norm condition.
  have h1 : a * σ a = 1 := by
    have h := hkey 1
    simp only [map_one, mul_one, map_add, mul_add, add_assoc] at h
    rw [h0, add_zero] at h
    exact h
  exact h1

end Work.DSTR.M110.twistAux
