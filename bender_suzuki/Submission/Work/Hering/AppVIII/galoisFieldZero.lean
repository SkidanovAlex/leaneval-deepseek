import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Polynomial

namespace Work.Hering.AppVIII

/-- `GaloisField 2 0` is the splitting field of `X ^ 2 ^ 0 - X = 0` over `ZMod 2`, i.e. of the
zero polynomial.  Its underlying "auxiliary" splitting field is therefore the base field
`ZMod 2` itself, and we may identify the two. -/
private noncomputable def galoisFieldTwoZeroEquivZModTwo : GaloisField 2 0 ≃+* ZMod 2 :=
  (SplittingField.algEquivSplittingFieldAux (X ^ 2 ^ 0 - X : (ZMod 2)[X])).toRingEquiv.trans
    (by
      have h : (X ^ 2 ^ 0 - X : (ZMod 2)[X]).natDegree = 0 := by simp
      rw [h]
      exact RingEquiv.refl _)

/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h2 : x.val = 0 ∨ x.val = 1 := by have := ZMod.val_lt x; omega
  rcases h2 with h2 | h2 <;> [left; right] <;>
    rw [← ZMod.natCast_zmod_val x, h2] <;> simp

theorem galoisFieldZero (φ : GaloisField 2 0 ≃+* GaloisField 2 0) : φ = 1 := by
  let e := galoisFieldTwoZeroEquivZModTwo
  ext x
  change φ x = x
  rcases zmodTwo_eq_zero_or_one (e x) with h | h
  · have hx : x = 0 := e.injective (by rw [h, map_zero])
    rw [hx, map_zero]
  · have hx : x = 1 := e.injective (by rw [h, map_one])
    rw [hx, map_one]

end Work.Hering.AppVIII
