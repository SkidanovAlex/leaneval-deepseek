import Mathlib
import Submission.NK.Chebotarev.KroneckerWeber

/-!
# The quadratic Gauss sum inside a cyclotomic field

For an odd prime `p` and a primitive `p`-th root of unity `ζ` in a field `F` containing `ℚ`,
the quadratic Gauss sum
`gaussSum χ ψ = ∑ a, χ a * ζ ^ a`
(with `χ` the Legendre/quadratic character on `ZMod p` and `ψ a = ζ ^ a` the additive
character it generates) has square `χ(-1) * p`, and `χ(-1) = 1` when `p ≡ 1 (mod 4)` and
`-1` when `p ≡ 3 (mod 4)`.  Hence `F` contains a square root of `p* = ±p`: this is the
classical fact that the quadratic subfield of `ℚ(ζ_p)` is `ℚ(√(p*))`.

The proof is the standard one (`gaussSum_sq` from Mathlib, plus `quadraticChar_neg_one`).
-/

set_option linter.style.haveILetI false

namespace NK.Chebotarev

open AddChar MulChar

theorem QuadraticGaussSumInCyclotomic (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {F : Type*}
    [Field F] [Algebra ℚ F] (ζ : F) (hζ : IsPrimitiveRoot ζ p) :
    ∃ x : F, x ^ 2 = ((if p % 4 = 1 then (1 : ℚ) else -1) * (p : ℚ)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : CharZero F := algebraRat.charZero F
  -- `p` is odd, so `ZMod p` has odd characteristic
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp)
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  -- the additive character `a ↦ ζ ^ a`
  let ψ : AddChar (ZMod p) F := AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).1 hζ).1
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  -- the quadratic character `ZMod p → F`, obtained from the Legendre symbol
  let χ : MulChar (ZMod p) F := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom F)
  have hχne : χ ≠ 1 := by
    rw [MulChar.ringHomComp_ne_one_iff Int.cast_injective]
    exact quadraticChar_ne_one hchar
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  refine ⟨gaussSum χ ψ, ?_⟩
  rw [gaussSum_sq hχne hχq hψ]
  -- the value of the quadratic character at `-1` only depends on `p % 4`
  have hχval : χ (-1) = ((if p % 4 = 1 then 1 else -1 : ℤ) : F) := by
    simp only [χ, MulChar.ringHomComp_apply]
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four,
      if_neg (by rw [hodd]; norm_num)]
    norm_num
  rw [hχval, ZMod.card, Rat.cast_natCast]
  congr 1
  by_cases h : p % 4 = 1 <;> simp [h]

end NK.Chebotarev
