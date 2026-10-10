/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The coefficient extension of `RatFunc`, and a descent lemma

For a field extension `K → M` there is a "coefficient extension" ring hom
`ratFuncCoeffMap K M : RatFunc K →+* RatFunc M`, sending the variable `X` to `X` and coefficients
along `algebraMap K M`.

The main point of this file is the *descent* lemma
`exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap`: an element `x : RatFunc K` whose image in
`RatFunc M` is a **constant** of `M` is itself a constant of `K`.  (This is the ingredient that lets
one replace a non-perfect base field by its algebraic closure.)

The proof is elementary: write `x = p / q` with `p = x.num`, `q = x.denom`; the hypothesis says
`(p.map) = (C m) * (q.map)` in `M[X]`; comparing coefficients shows that `m` is the image of an
element of `K` and that `p` is that constant times `q`.
-/

open Polynomial

namespace Work.Wire123

/-- The coefficient extension `RatFunc K →+* RatFunc M` induced by `algebraMap K M`: the ring
homomorphism of fraction fields of `K[X] → M[X]` given by `Polynomial.map (algebraMap K M)`. -/
noncomputable def ratFuncCoeffMap (K M : Type*) [Field K] [Field M] [Algebra K M] :
    RatFunc K →+* RatFunc M :=
  RatFunc.liftRingHom
    ((algebraMap (Polynomial M) (RatFunc M)).comp (Polynomial.mapRingHom (algebraMap K M)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (fun _ _ h =>
        Polynomial.map_injective (algebraMap K M) (algebraMap K M).injective
          (IsFractionRing.injective (Polynomial M) (RatFunc M) h)))

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

@[simp]
lemma ratFuncCoeffMap_algebraMap_poly (p : Polynomial K) :
    ratFuncCoeffMap K M (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial M) (RatFunc M) (p.map (algebraMap K M)) := by
  show RatFunc.liftRingHom _ _ (algebraMap (Polynomial K) (RatFunc K) p) = _
  rw [RatFunc.liftRingHom_algebraMap]
  rfl

lemma ratFuncCoeffMap_algebraMap (c : K) :
    ratFuncCoeffMap K M (algebraMap K (RatFunc K) c)
      = algebraMap M (RatFunc M) (algebraMap K M c) := by
  have h : (algebraMap K (RatFunc K) c : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
    rfl
  rw [h, ratFuncCoeffMap_algebraMap_poly, Polynomial.map_C, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

/-- **Descent.**  If the image of `x : RatFunc K` under the coefficient extension `K → M` is a
constant of `M`, then `x` is already a constant of `K`. -/
theorem exists_algebraMap_of_ratFuncCoeffMap_eq_algebraMap {x : RatFunc K} {m : M}
    (h : ratFuncCoeffMap K M x = algebraMap M (RatFunc M) m) :
    ∃ c : K, x = algebraMap K (RatFunc K) c := by
  set p := x.num with hp
  set q := x.denom with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact RatFunc.denom_ne_zero x
  have hnum : x = algebraMap (Polynomial K) (RatFunc K) p
      / algebraMap (Polynomial K) (RatFunc K) q := by
    rw [hp, hq]; exact (RatFunc.num_div_denom x).symm
  have hmain : Polynomial.map (algebraMap K M) p
      = Polynomial.C m * Polynomial.map (algebraMap K M) q := by
    have hB : algebraMap (Polynomial M) (RatFunc M) (Polynomial.map (algebraMap K M) q) ≠ 0 := by
      intro hz
      have h1 : Polynomial.map (algebraMap K M) q = 0 := by
        apply IsFractionRing.injective (Polynomial M) (RatFunc M)
        rw [hz, map_zero]
      exact hq0 (Polynomial.map_injective (algebraMap K M) (algebraMap K M).injective
        (by simpa using h1))
    have hC : algebraMap M (RatFunc M) m
        = algebraMap (Polynomial M) (RatFunc M) (Polynomial.C m) := by
      rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C]
    rw [hnum, map_div₀, ratFuncCoeffMap_algebraMap_poly, ratFuncCoeffMap_algebraMap_poly, hC] at h
    rw [div_eq_iff hB, ← map_mul] at h
    exact IsFractionRing.injective (Polynomial M) (RatFunc M) h
  have hcoeff : ∀ i, algebraMap K M (p.coeff i) = m * algebraMap K M (q.coeff i) := by
    intro i
    have := congrArg (fun r : Polynomial M => r.coeff i) hmain
    simpa only [Polynomial.coeff_map, Polynomial.coeff_C_mul] using this
  obtain ⟨i, hi⟩ : ∃ i, q.coeff i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq0 (Polynomial.ext fun n => by simpa using hcon n)
  refine ⟨p.coeff i / q.coeff i, ?_⟩
  have hb : algebraMap K M (q.coeff i) ≠ 0 :=
    fun hz => hi ((algebraMap K M).injective (by rw [hz, map_zero]))
  have hm : m = algebraMap K M (p.coeff i / q.coeff i) := by
    rw [map_div₀, eq_div_iff hb, hcoeff i]
  have hpq : p = Polynomial.C (p.coeff i / q.coeff i) * q := by
    apply Polynomial.map_injective (algebraMap K M) (algebraMap K M).injective
    rw [Polynomial.map_mul, Polynomial.map_C, ← hm]
    exact hmain
  have hc : (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (p.coeff i / q.coeff i))
        : RatFunc K) = algebraMap K (RatFunc K) (p.coeff i / q.coeff i) := by
    rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
  conv_lhs => rw [hnum, hpq, map_mul, hc, mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hq0)]

end Work.Wire123
