/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.MotC.WireU.WeierstrassCharP
import Submission.Work.Wire123.RatFuncCoeff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# One-variable Weierstrass rigidity in characteristic `p`, without perfectness

`Work.MotC.WireU.exists_algebraMap_of_weierstrass_charP` proves that over a **perfect** field `F` of
characteristic `p ≠ 2` every `F(t)`-point of a non-singular Weierstrass curve is constant.

Here we remove the perfectness hypothesis.  Given an arbitrary field `K` of characteristic `p` and
`(x, y) ∈ RatFunc K` satisfying the Weierstrass equation of `E⁄K`, one passes to the algebraic
closure `M := AlgebraicClosure K` (perfect, algebraically closed), applies the perfect-field theorem
there, and descends along the coefficient extension `RatFunc K →+* RatFunc M`
(`Work.Wire123.ratFuncCoeffMap`): a `K`-rational function whose image is a constant of `M` is a
constant of `K` (`Work.Wire123.exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap`).
-/

open WeierstrassCurve Polynomial
open Work.Wire123

namespace Work.MotC.WireU

theorem exists_algebraMap_of_weierstrass_ratFunc_charP {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (h2 : (2 : K) ≠ 0) (E : WeierstrassCurve K) (hΔ : E.Δ ≠ 0) {x y : RatFunc K}
    (h : y ^ 2 + algebraMap K (RatFunc K) E.a₁ * x * y + algebraMap K (RatFunc K) E.a₃ * y
      = x ^ 3 + algebraMap K (RatFunc K) E.a₂ * x ^ 2 + algebraMap K (RatFunc K) E.a₄ * x
        + algebraMap K (RatFunc K) E.a₆) :
    (∃ x₀ : K, x = algebraMap K (RatFunc K) x₀) ∧ (∃ y₀ : K, y = algebraMap K (RatFunc K) y₀) := by
  let M := AlgebraicClosure K
  haveI : PerfectField M := inferInstance
  haveI : CharP M p := inferInstance
  have hpdvd : ¬ p ∣ 2 := fun hdvd => h2 ((CharP.cast_eq_zero_iff K p 2).mpr hdvd)
  have h2M : (2 : M) ≠ 0 := fun hz => hpdvd ((CharP.cast_eq_zero_iff M p 2).mp hz)
  set E' : WeierstrassCurve M := E.baseChange M with hE'
  have hΔ' : E'.Δ ≠ 0 := by
    rw [hE', WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    intro hh
    exact hΔ ((algebraMap K M).injective (by rw [hh, map_zero]))
  set x' : RatFunc M := ratFuncCoeffMap K M x with hx'
  set y' : RatFunc M := ratFuncCoeffMap K M y with hy'
  have h' : y' ^ 2 + algebraMap M (RatFunc M) E'.a₁ * x' * y'
        + algebraMap M (RatFunc M) E'.a₃ * y'
      = x' ^ 3 + algebraMap M (RatFunc M) E'.a₂ * x' ^ 2 + algebraMap M (RatFunc M) E'.a₄ * x'
        + algebraMap M (RatFunc M) E'.a₆ := by
    have hh := congrArg (ratFuncCoeffMap K M) h
    simp only [map_add, map_mul, map_pow] at hh
    rw [← hx', ← hy'] at hh
    simp only [ratFuncCoeffMap_algebraMap] at hh
    rw [hE', WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    exact hh
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ :=
    Work.MotC.WireU.exists_algebraMap_of_weierstrass_charP (F := M) (p := p) h2M E' hΔ' h'
  refine ⟨?_, ?_⟩
  · exact exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap (hx'.symm.trans hm)
  · exact exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap (hy'.symm.trans hn)

end Work.MotC.WireU
