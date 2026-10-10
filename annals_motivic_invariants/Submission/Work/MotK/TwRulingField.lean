import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwRuleMem

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ruling point of the T-twisted link at the twisted base point

This file fixes the *field-level* objects of the census of `Work.MotK.LinkCertT`
(`AUDIT_LinkCertT.md` §9, steps 2–4): with `K = RatFunc 𝕜`, `h ≠ 0` and
`F₁ = Work.MotV.twistFieldT D h ⊆ Om D`, we need the ruling parametrisation of the twisted
Crauder–Katz link evaluated at the *base point* of the twisted Klein curve, i.e. at the twisted
coordinates `y_j = Work.MotV.twCoord D h j`.

* `twCoordF D h j` is `twCoord D h j` viewed in the twist field `↥F₁`;
* `twRulePtF D h` is the ruling point `λ·A(c) + μ·B(c)` of `TwRule.lean` at `c = y`,
  `λ = 1`, `μ = T` (the `RatFunc` variable), i.e. the vector
  `A_j(y) + T·B_j(y)` in `RatFunc ↥F₁`.

## The identity that the census needs (step 2 of the roadmap)

`Work.MotK.KleinTwRuleQuadraticMem` (sibling file) proves the ruling identity
`kleinTwR (λA + μB) ∝ c` modulo the five twisted quadrics (`KleinTwRuleMem`, proved).  Combining
it with the twisted I2 (`Work.MotK.KleinTwI2inv`: `kleinTwP (kleinTwR z) = kleinTwSDualV z • z`)
and with `Work.MotV.twCoord_eq` (`kleinTwP (twCoord) = 0`) gives, at the base point `c = y`:

  `kleinTwSDualInv (A(y) + T·B(y)) = 0`  in `RatFunc ↥F₁`,

i.e. the *ruling lines of the twisted link lie in the divisor `{s' = 0}`* of the target side —
equivalently, the quintic `q̄₅ = kleinTwSDualInv (C a) (C b) (C h) (chart3)` maps to `0` under the
dehomogenised ruling map `X_i ↦ (A_{i+1}(y) + T·B_{i+1}(y)) / (A_4(y) + T·B_4(y))` (by the
homogeneity `kleinTwSDualV_homog`: `s'(λz) = λ⁵ s'(z)`, the dehomogenisation of `s' = 0` is
again `0`).  This is `Work.MotK.KleinTwRulingQuinticMem` (sibling file).

Route for that statement, in detail:

1. `KleinTwRuleMem` gives, for the *constant* parameters `(λ,μ) ∈ K²` and the variables `c`,
   `R_i(ℓ_c)·c_j − R_j(ℓ_c)·c_i ∈ I := (kleinTwP₀,…,kleinTwP₄)(c)` in `MvPolynomial (Fin 5) K`.
   The version with `μ` a *variable* follows, because the difference is homogeneous of degree `3`
   in `(λ,μ)` and `K = RatFunc 𝕜` is infinite (a polynomial in `(λ,μ)` vanishing at all
   `(λ,μ) ∈ K²` with values in the torsion-free module `K[c]/I` is zero, or: re-prove the
   identity in `MvPolynomial (Fin 7) K` — the "universal certificate" of
   `CensusFibre.ruling_mem`'s docstring).
2. Evaluating (1) at `c := y` (the evaluation kills `I` by `Work.MotV.twCoord_eq`, transported to
   `RatFunc ↥F₁`) gives `kleinTwR(w) ∝ y` for `w = twRulePtF D h`, say `kleinTwR(w) = λ·y` with
   `λ ≠ 0` in `RatFunc ↥F₁` (the "projective" statement: all `2×2` minors of `(kleinTwR w, y)`
   vanish).
3. Twisted I2 at `z := w`: `kleinTwP (kleinTwR w) = kleinTwSDualV w • w`.  The left side is
   `kleinTwP (λ·y) = λ² • kleinTwP (y) = 0` (quadraticity of `kleinTwP` + `twCoord_eq`), hence
   `kleinTwSDualV w • w = 0`, i.e. `s'(w)·w_i = 0` for all `i`.
4. `RatFunc ↥F₁` is a domain and the vector `w = A(y) + T·B(y)` is nonzero (e.g. because
   `A_3(y) ≠ 0`, or any coordinate that is a nonzero polynomial in the transcendental-ish
   coordinates `y`); hence `s'(w) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

noncomputable section

open MvPolynomial

/-- The twisted coordinate `twCoord D h j` of the base point, viewed in the twist field
`↥(twistFieldT D h)`. -/
def twCoordF (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (h : RatFunc 𝕜) (j : Fin 5) :
    ↥(Work.MotV.twistFieldT D h) :=
  ⟨Work.MotV.twCoord D h j,
    IntermediateField.subset_adjoin (RatFunc 𝕜) (Set.range (Work.MotV.twCoord D h))
      (Set.mem_range_self j)⟩

@[simp] theorem twCoordF_coe (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (h : RatFunc 𝕜)
    (j : Fin 5) :
    ((twCoordF 𝕜 D h j : ↥(Work.MotV.twistFieldT D h)) : Work.MotV.Om D) =
      Work.MotV.twCoord D h j := rfl

/-- The ruling point of the twisted Crauder–Katz link at the base point of the twisted Klein curve,
with ruling parameter `T = RatFunc.X`: the vector `A_j(y) + T·B_j(y)` over the twist field. -/
def twRulePtF (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (h : RatFunc 𝕜) :
    Fin 5 → RatFunc ↥(Work.MotV.twistFieldT D h) :=
  kleinTwRulePt (algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.a)
    (algebraMap 𝕜 (RatFunc ↥(Work.MotV.twistFieldT D h)) D.b)
    (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotV.twistFieldT D h)) h)
    (fun j => algebraMap ↥(Work.MotV.twistFieldT D h) (RatFunc ↥(Work.MotV.twistFieldT D h))
      (twCoordF 𝕜 D h j))
    (1 : RatFunc ↥(Work.MotV.twistFieldT D h))
    (RatFunc.X : RatFunc ↥(Work.MotV.twistFieldT D h))

end

end Work.MotK
