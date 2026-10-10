/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Geometry.Reduction
import Submission.Work.FFResidual.Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field classes at the rational function field `𝔽(x₁,…,x_{n+1})`

`FractionRing (MvPolynomial (Fin (n+1)) 𝔽)` is the function field of affine `(n+1)`-space over `𝔽`,
i.e. the rational function field in `n+1` variables.  It carries a place over `𝔽` — the local ring of
the generic point of the hyperplane `X 0 = 0`
(`Work.FFResidual.Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial`) — so the whole
function-field machinery of `Submission/Work/FFResidual` applies and the residual of the classes
`(b)`, `(c)`, `(d)` is a **theorem** at this field.

For `n = 0` this is the one-variable case `𝔽(t)`, already closed in `Work.ClassBCD.RatFunc` by the
`ConstantsOnly` route (`E(𝔽(s)) = E(𝔽)`, genus chapter).  For `n ≥ 1` it is a function field of
transcendence degree `≥ 2`, which that route does **not** reach (a higher-dimensional variety maps
non-constantly to the constant elliptic curve); the place obstruction produced here is what decides
those cases.  This is the concrete, unconditional instance of the residual at a *higher-dimensional*
function field, and it shows that the geometric sub-residual
`Work.FFResidual.HasIntegrallyClosedCodimOnePoint` is satisfiable.

## Main results

* `Work.FFResidual.nonempty_functionFieldResidual_fractionRing_mvPolynomial` (Kummer case, from
  `ζ₅ ∈ 𝔽` and a good Tate parameter) and the characteristic-`5` analogue
  `..._charP`;
* the arithmetic halves `Work.FFResidual.hasPointlessTwist_fractionRing_mvPolynomial_of_zeta5`
  (unconditional over an infinite `𝔽` with `ζ₅ ∈ 𝔽`) and
  `hasPointlessTwist_fractionRing_mvPolynomial_charP`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

namespace Work.FFResidual

noncomputable section

/-- The rational function field in `n+1` variables over `𝔽`. -/
abbrev MvRatFunc (𝔽 : Type) [Field 𝔽] (n : ℕ) : Type := FractionRing (MvPolynomial (Fin (n+1)) 𝔽)

/-- **The residual at `𝔽(x₁,…,x_{n+1})`** (Kummer case). -/
theorem nonempty_functionFieldResidual_fractionRing_mvPolynomial
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 (FractionRing (MvPolynomial (Fin (n+1)) 𝔽))) :=
  ((Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial 𝔽 n).some).nonempty_functionFieldResidual
    ζ hζ c hΔ hj

/-- **The arithmetic half of the classes at `𝔽(x₁,…,x_{n+1})`** (Kummer case). -/
theorem nonempty_hasPointlessTwist_fractionRing_mvPolynomial
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] (n : ℕ) (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)),
      @Work.PointlessTwist.HasPointlessTwist (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)) _ dec :=
  ((Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial 𝔽 n).some).nonempty_hasPointlessTwist_of_place
    ζ hζ c hΔ hj

/-- **The classes at `𝔽(x₁,…,x_{n+1})` for an infinite `𝔽` containing a primitive fifth root of
unity**: the Tate parameter is `Work.TorsorExistence.Tate.exists_tate_param`. -/
theorem hasPointlessTwist_fractionRing_mvPolynomial_of_zeta5
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [Infinite 𝔽] (n : ℕ) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) :
    ∃ dec : DecidableEq (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)),
      @Work.PointlessTwist.HasPointlessTwist (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)) _ dec := by
  classical
  obtain ⟨c, hcΔ, hcj⟩ := Work.TorsorExistence.Tate.exists_tate_param (𝕜 := 𝔽)
  have hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0 := by
    rwa [Work.TorsorExistence.Tate.tateCurve_Δ]
  have hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ := by
    rwa [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]
  exact nonempty_hasPointlessTwist_fractionRing_mvPolynomial 𝔽 n ζ hζ c hΔ hj

/-- **The residual at `𝔽(x₁,…,x_{n+1})` in characteristic five** (Artin–Schreier case). -/
theorem nonempty_functionFieldResidual_fractionRing_mvPolynomial_charP
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [CharP 𝔽 5] (n : ℕ) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 (FractionRing (MvPolynomial (Fin (n+1)) 𝔽))) := by
  haveI : CharP (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)) 5 :=
    charP_of_injective_algebraMap
      (algebraMap 𝔽 (FractionRing (MvPolynomial (Fin (n+1)) 𝔽))).injective 5
  exact ((Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial 𝔽 n).some)
    |>.nonempty_functionFieldResidual_charP c hΔ hj

/-- **The classes at `𝔽(x₁,…,x_{n+1})` in characteristic five**, from a good Tate parameter. -/
theorem hasPointlessTwist_fractionRing_mvPolynomial_charP
    (𝔽 : Type) [Field 𝔽] [DecidableEq 𝔽] [CharP 𝔽 5] (n : ℕ) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)),
      @Work.PointlessTwist.HasPointlessTwist (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)) _ dec := by
  haveI : CharP (FractionRing (MvPolynomial (Fin (n+1)) 𝔽)) 5 :=
    charP_of_injective_algebraMap
      (algebraMap 𝔽 (FractionRing (MvPolynomial (Fin (n+1)) 𝔽))).injective 5
  exact ((Geometry.hasFunctionFieldPlace_fractionRing_mvPolynomial 𝔽 n).some)
    |>.nonempty_hasPointlessTwist_of_place_charP c hΔ hj


/-! ## Concrete classes at a higher-dimensional rational function field -/

section Concrete

/-- **Class (b) at the rational function field `ℚ(ζ₅)(x₁,…,x_{n+1})`**, unconditionally: the
constants are the number field `ℚ(ζ₅)`, the field has transcendence degree `n+1`, and the function
field carries the place at the hyperplane `X 0 = 0`.  This is the class theorem of Theorem 1.2 (1)
(b) at a function field of dimension `≥ 2` whenever `n ≥ 1` (in particular it strictly extends the
`𝔽(t)` results of `Work.ClassBCD.RatFunc`, whose `ConstantsOnly` route does not reach these fields). -/
theorem hasPointlessTwist_fractionRing_mvPolynomial_cyclotomic (n : ℕ) :
    ∃ dec : DecidableEq (FractionRing (MvPolynomial (Fin (n+1)) (CyclotomicField 5 ℚ))),
      @Work.PointlessTwist.HasPointlessTwist
        (FractionRing (MvPolynomial (Fin (n+1)) (CyclotomicField 5 ℚ))) _ dec := by
  classical
  haveI : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {5}) ℚ
    (CyclotomicField 5 ℚ) rfl (by norm_num : (5 : ℕ) ≠ 0)
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (1 : CyclotomicField 5 ℚ)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]; norm_num
  have hj : (Work.TorsorExistence.Tate.tateCurve (1 : CyclotomicField 5 ℚ)).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve (1 : CyclotomicField 5 ℚ)).Δ := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]; norm_num
  exact nonempty_hasPointlessTwist_fractionRing_mvPolynomial (CyclotomicField 5 ℚ) n ζ hζ 1 hΔ hj

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Class (c)/(d) at the rational function field `𝔽₅(x₁,…,x_{n+1})`** (characteristic `5`,
Artin–Schreier route), unconditionally. -/
theorem hasPointlessTwist_fractionRing_mvPolynomial_five (n : ℕ) :
    ∃ dec : DecidableEq (FractionRing (MvPolynomial (Fin (n+1)) (ZMod 5))),
      @Work.PointlessTwist.HasPointlessTwist
        (FractionRing (MvPolynomial (Fin (n+1)) (ZMod 5))) _ dec := by
  have hΔ : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ ≠ 0 := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ]; decide
  have hj : (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve (1 : ZMod 5)).Δ := by
    rw [Work.TorsorExistence.Tate.tateCurve_Δ, Work.TorsorExistence.Tate.tateCurve_c₄]; decide
  exact hasPointlessTwist_fractionRing_mvPolynomial_charP (ZMod 5) n 1 hΔ hj

end Concrete

end

end Work.FFResidual
