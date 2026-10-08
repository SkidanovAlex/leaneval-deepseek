/-
# `GaloisField 2 0` has two elements

Mathlib defines `GaloisField p n` as the splitting field of `X ^ p ^ n - X` over `ZMod p`,
and proves `Nat.card (GaloisField p n) = p ^ n` only under the side condition `n ≠ 0`
(`GaloisField.card`): for `n = 0` the polynomial `X ^ p ^ 0 - X = X ^ 1 - X` is the *zero*
polynomial, so the general formula `p ^ 0 = 1` does not apply.  The degenerate field
`GaloisField 2 0` is nevertheless the base field `ZMod 2`, hence has `2` elements — the
case `n = 0` of the Suzuki/unitary construction, where `GF(2^(2·0)) = GF(2)`.

The proof is a single observation.  `SplittingField.algEquivSplittingFieldAux` identifies
`GaloisField 2 0 = SplittingField (X ^ 2 ^ 0 - X)` with `SplittingFieldAux f.natDegree f`,
and `f.natDegree = 0` here, while `SplittingFieldAux 0 f` is by construction the base field
itself (`SplittingFieldAuxAux` returns `⟨K, _, _⟩` at `n = 0`, and the recursion is
definitional).  So the above equivalence composed with the reflexivity isomorphism of
`ZMod 2` gives a ring isomorphism `GaloisField 2 0 ≃+* ZMod 2`, and cardinalities agree.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.GaloisField

open Polynomial

/-- `GaloisField 2 0` is the splitting field of the zero polynomial `X ^ 2 ^ 0 - X` over
`ZMod 2`; since a polynomial of degree `0` has splitting field the base field itself, this
is (canonically) `ZMod 2`. -/
private noncomputable def galoisFieldTwoZeroEquivZModTwo : GaloisField 2 0 ≃+* ZMod 2 :=
  (Polynomial.SplittingField.algEquivSplittingFieldAux
      (X ^ 2 ^ 0 - X : (ZMod 2)[X])).toRingEquiv.trans
    (by
      have h : (X ^ 2 ^ 0 - X : (ZMod 2)[X]).natDegree = 0 := by simp
      rw [h]
      exact RingEquiv.refl _)

/-- The degenerate Galois field `GF(2^0) = GF(2)` has two elements. -/
theorem card_zero : Nat.card (GaloisField 2 0) = 2 := by
  rw [Nat.card_congr galoisFieldTwoZeroEquivZModTwo.toEquiv, Nat.card_eq_fintype_card,
    ZMod.card]

end Work.PSU3.GaloisField
