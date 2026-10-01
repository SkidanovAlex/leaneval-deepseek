import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero

namespace Work.LinnikAreas

/-- If `u` is a zero (in the sense of the Linnik contract, i.e. a zero of the *completed*
`L`-function of the primitive character inducing `χ`) of a non-principal Dirichlet character `χ`
of level `q`, then `u` is a genuine zero of the ordinary `L`-function `L(s, χ)` of `χ` itself,
even when `χ` is imprimitive.

Route: `Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero` gives
`L(s, χ.primitiveCharacter) u = 0`; then Mathlib's `LFunction_changeLevel` writes
`L(s, χ) = L(s, χ.primitiveCharacter) · ∏_{p | q} (1 - χ.primitiveCharacter(p) p^{-s})`
(because `changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ`), a finite product,
so the right side vanishes at `u`. -/
theorem LFunctionImprimitiveZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1)
    (h : Work.LinnikContract.zeroMult χ u ≠ 0) :
    DirichletCharacter.LFunction χ u = 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- `u` lies in the strip, hence is not `1`.
  have hu : u ≠ 1 := by
    intro h1
    rw [h1] at hu1
    norm_num at hu1
  -- The primitive zero is a genuine zero of the primitive `L`-function.
  have hprim : DirichletCharacter.LFunction χ.primitiveCharacter u = 0 :=
    Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero χ hχ h
  -- `χ` is the level-`q` lift of its primitive character.
  have hχeq : χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
    (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
  -- Level-change relation: the imprimitive `L`-function is the primitive one times a
  -- finite (Euler-type) product.
  rw [hχeq, DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
      (Or.inr hu), hprim, zero_mul]

end Work.LinnikAreas
