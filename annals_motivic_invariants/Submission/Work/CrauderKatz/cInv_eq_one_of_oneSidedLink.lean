import Mathlib
import Submission.Work.CrauderKatz.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz

/-- **The one-sided L-link.**  A birational map `ψ : X ⤏ Y` over `𝕜` with *no* exceptional divisor in
the forward direction and exactly one, `y`, in the inverse direction has `[κ(y)]`-coefficient
exactly `1`, with **no** field-theoretic input at all: the source-side count is empty, the
target-side count is one.

This is the reason the "one-sided" route to Theorem 1.2 (1) is attractive: the inverse of a blow-up
of a variety along a centre of codimension at least two is such a map, and its invariant is
non-zero without any need for two non-isomorphic function fields.  The obstruction to using it is
the transport to `Cr 𝕜 3`, which cancels it (`Work.CrauderKatz.cInv_conj_eq`); see §6.3(a) of
`Submission/Work/CrauderKatz/NOTES.md`. -/
theorem cInv_eq_one_of_oneSidedLink (𝕜 : Type) [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (ψ : X.BirationalMap Y) (y : Y)
    (hx : exDiv ψ = ∅) (hy : exDiv ψ.symm = {y}) :
    cInv 𝕜 y ψ = 1 := by
  -- forward direction: no exceptional divisor at all, so nothing contributes
  have h2 : excCount 𝕜 y ψ = 0 :=
    Work.LLink.excCount_eq_zero_of_exDiv_eq_empty (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Y) y ψ hx
  -- inverse direction: the single exceptional divisor `y` matches the base point `y` itself
  have h1 : excCount 𝕜 y ψ.symm = 1 :=
    Work.LLink.excCount_eq_one_of_exDiv_eq_singleton (𝕜 := 𝕜) (X := Y) (Y := X) (Z := Y) y ψ.symm
      hy (Work.Motivic.ResEquiv.refl 𝕜 y)
  show (excCount 𝕜 y ψ.symm : ℤ) - (excCount 𝕜 y ψ : ℤ) = 1
  rw [h1, h2]
  norm_num

end Work.CrauderKatz
