/-
# The five linear forms of which the degenerate quintic is the product

`hζ : IsPrimitiveRoot ζ 5` gives `ζ ^ 5 = 1` and `ζ ≠ 1`, hence
`1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0` (multiply `ζ - 1` by the sum).

The product only involves `x 0, x 3, x 4`; the coefficient of `x 0 ^ a * x 3 ^ b * x 4 ^ c`
(`a + b + c = 5`) is the mixed elementary symmetric function of the pairs
`(c_j, d_j) = (ζ ^ j, B * ζ ^ (3 * j))`, and it equals `B ^ c * ∑ j, ζ ^ (j * (b + 3 * c))`,
which is `5 * B ^ c` when `5 ∣ b + 3 * c` and `0` otherwise.  The only `(a,b,c)` with
`a + b + c = 5` and `b + 3 * c ≡ 0 (mod 5)` are `(5,0,0)`, `(2,2,1)`, `(1,1,3)`, `(0,5,0)`,
`(0,0,5)`, giving the five coefficients `1, 5 * B, -5 * B ^ 3, 1, B ^ 5`.

FORMAL ROUTE.  `Fin.prod_univ_five` expands the product into the five factors
`(x0 + x3 + B x4)`, `(x0 + ζ x3 + B ζ^3 x4)`, …; the exponents `ζ ^ 6`, `ζ ^ 9`, `ζ ^ 12` are
reduced with `ζ ^ 5 = 1`.  The resulting identity is the universal one
`(a+b+c)(a+bz+cz^3)(a+bz^2+cz)(a+bz^3+cz^4)(a+bz^4+cz^2) = a^5+b^5+c^5+5a^2b^2c-5abc^3`
for `z` a root of `z^4+z^3+z^2+z+1` (`goodDiscFactorAux`), proved by exhibiting the cofactor
of `z^4+z^3+z^2+z+1` and checking it with `ring`.  Since the product's five factors are each
equal (by commutativity) to the corresponding factor of the universal identity with
`c := B * x 4`, an intermediate `ring` rewrite bridges the two.
-/
import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwCensus

/-- Universal form of the identity: for `z` with `z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0`
(equivalently a primitive fifth root of unity in a field), the product of the five linear forms
`a + b z ^ k + c z ^ (3 k)` (`k = 0,…,4`) equals `a ^ 5 + b ^ 5 + c ^ 5 + 5 a ^ 2 b ^ 2 c - 5 a b c ^ 3`.

The product is reduced modulo `z ^ 4 + z ^ 3 + z ^ 2 + z + 1`; the displayed cofactor is the
explicit quotient of the difference by that relation. -/
lemma goodDiscFactorAux {A : Type*} [CommRing A] (a b c z : A)
    (h : z ^(4:ℕ) + z ^(3:ℕ) + z ^(2:ℕ) + z + 1 = 0) :
    (a + b + c) * (a + b * z + c * z ^(3:ℕ)) * (a + b * z ^(2:ℕ) + c * z) *
        (a + b * z ^(3:ℕ) + c * z ^(4:ℕ)) * (a + b * z ^(4:ℕ) + c * z ^(2:ℕ))
      = a ^(5:ℕ) + b ^(5:ℕ) + c ^(5:ℕ) + 5 * a ^(2:ℕ) * b ^(2:ℕ) * c - 5 * a * b * c ^(3:ℕ) := by
  have hcert :
      (a + b + c) * (a + b * z + c * z ^(3:ℕ)) * (a + b * z ^(2:ℕ) + c * z) *
          (a + b * z ^(3:ℕ) + c * z ^(4:ℕ)) * (a + b * z ^(4:ℕ) + c * z ^(2:ℕ))
        - (a ^(5:ℕ) + b ^(5:ℕ) + c ^(5:ℕ) + 5 * a ^(2:ℕ) * b ^(2:ℕ) * c - 5 * a * b * c ^(3:ℕ))
      = (z ^(4:ℕ) + z ^(3:ℕ) + z ^(2:ℕ) + z + 1) *
        (-b^(5:ℕ) - c^(5:ℕ) + b*a^(4:ℕ) + c*a^(4:ℕ) + z*b^(5:ℕ) + z*c^(5:ℕ) + b^(5:ℕ)*z^(6:ℕ) + c^(5:ℕ)*z^(6:ℕ) - b^(5:ℕ)*z^(5:ℕ) - c^(5:ℕ)*z^(5:ℕ)
          + a*b^(4:ℕ)*z^(6:ℕ) + a*c^(4:ℕ)*z^(6:ℕ) + b*c^(4:ℕ)*z^(8:ℕ) + c*b^(4:ℕ)*z^(8:ℕ) + z*a^(3:ℕ)*b^(2:ℕ) + z*a^(3:ℕ)*c^(2:ℕ)
          + a^(2:ℕ)*b^(3:ℕ)*z^(3:ℕ) + a^(2:ℕ)*b^(3:ℕ)*z^(5:ℕ) + a^(2:ℕ)*c^(3:ℕ)*z^(3:ℕ) + a^(2:ℕ)*c^(3:ℕ)*z^(5:ℕ) + a^(3:ℕ)*b^(2:ℕ)*z^(3:ℕ) + a^(3:ℕ)*c^(2:ℕ)*z^(3:ℕ)
          + b^(2:ℕ)*c^(3:ℕ)*z^(7:ℕ) + b^(2:ℕ)*c^(3:ℕ)*z^(9:ℕ) + b^(3:ℕ)*c^(2:ℕ)*z^(7:ℕ) + b^(3:ℕ)*c^(2:ℕ)*z^(9:ℕ) - 5*c*a^(2:ℕ)*b^(2:ℕ) + 5*a*b*c^(3:ℕ)
          + a*b*c^(3:ℕ)*z^(4:ℕ) + a*b*c^(3:ℕ)*z^(7:ℕ) + a*b*c^(3:ℕ)*z^(8:ℕ) + a*c*b^(3:ℕ)*z^(6:ℕ) + a*c*b^(3:ℕ)*z^(8:ℕ)
          + a*b^(2:ℕ)*c^(2:ℕ)*z^(4:ℕ) + a*b^(2:ℕ)*c^(2:ℕ)*z^(5:ℕ) + a*b^(2:ℕ)*c^(2:ℕ)*z^(9:ℕ) + b*c*a^(3:ℕ)*z^(2:ℕ) + b*c*a^(3:ℕ)*z^(4:ℕ)
          + b*a^(2:ℕ)*c^(2:ℕ)*z^(2:ℕ) + b*a^(2:ℕ)*c^(2:ℕ)*z^(3:ℕ) + b*a^(2:ℕ)*c^(2:ℕ)*z^(7:ℕ) + c*a^(2:ℕ)*b^(2:ℕ)*z^(2:ℕ) + c*a^(2:ℕ)*b^(2:ℕ)*z^(3:ℕ)
          + c*a^(2:ℕ)*b^(2:ℕ)*z^(4:ℕ) - a*b^(2:ℕ)*c^(2:ℕ)*z^(8:ℕ) - b*a^(2:ℕ)*c^(2:ℕ)*z^(6:ℕ) - 5*a*b*z*c^(3:ℕ) - 2*a*b*c^(3:ℕ)*z^(6:ℕ)
          + 2*a*c*b^(3:ℕ)*z^(5:ℕ) + 2*a*b^(2:ℕ)*c^(2:ℕ)*z^(6:ℕ) + 2*a*b^(2:ℕ)*c^(2:ℕ)*z^(7:ℕ) + 2*b*c*z*a^(3:ℕ) + 2*b*a^(2:ℕ)*c^(2:ℕ)*z^(4:ℕ)
          + 2*b*a^(2:ℕ)*c^(2:ℕ)*z^(5:ℕ) + 2*c*a^(2:ℕ)*b^(2:ℕ)*z^(6:ℕ) + 4*a*b*c^(3:ℕ)*z^(5:ℕ) + 5*c*z*a^(2:ℕ)*b^(2:ℕ)) := by
    first | refl_ring1 | ring
  rw [h, zero_mul] at hcert
  exact sub_eq_zero.mp hcert

theorem GoodDiscFactor {A : Type*} [Field A] (B ζ : A) (hζ : IsPrimitiveRoot ζ 5) (x : Fin 5 → A) :
    (∏ j : Fin 5, (x 0 + ζ ^ (j : ℕ) * x 3 + B * ζ ^ (3 * (j : ℕ)) * x 4))
      = x 0 ^(5:ℕ) + 5 * B * x 0 ^(2:ℕ) * x 3 ^(2:ℕ) * x 4 - 5 * B ^(3:ℕ) * x 0 * x 3 * x 4 ^(3:ℕ)
        + x 3 ^(5:ℕ) + B ^(5:ℕ) * x 4 ^(5:ℕ) := by
  have h5 : ζ ^(5:ℕ) = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  -- `1 + ζ + ζ^2 + ζ^3 + ζ^4 = 0`, because `(ζ - 1) * (⋯) = ζ^5 - 1 = 0` and `ζ ≠ 1`.
  have hΦ : ζ ^(4:ℕ) + ζ ^(3:ℕ) + ζ ^(2:ℕ) + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ ^(4:ℕ) + ζ ^(3:ℕ) + ζ ^(2:ℕ) + ζ + 1) = 0 := by
      have e : (ζ - 1) * (ζ ^(4:ℕ) + ζ ^(3:ℕ) + ζ ^(2:ℕ) + ζ + 1) = ζ ^(5:ℕ) - 1 := by ring
      rw [e, h5, sub_self]
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hζ1
    · exact h1
  -- reduction of the higher powers of `ζ` appearing in the third factor of each term
  have h6 : ζ ^(6:ℕ) = ζ := by
    have h : ζ ^(6:ℕ) = ζ ^(5:ℕ) * ζ := by ring
    rw [h, h5, one_mul]
  have h9 : ζ ^(9:ℕ) = ζ ^(4:ℕ) := by
    have h : ζ ^(9:ℕ) = ζ ^(5:ℕ) * ζ ^(4:ℕ) := by ring
    rw [h, h5, one_mul]
  have h12 : ζ ^(12:ℕ) = ζ ^(2:ℕ) := by
    have h : ζ ^(12:ℕ) = (ζ ^(5:ℕ)) ^(2:ℕ) * ζ ^(2:ℕ) := by ring
    rw [h, h5]; ring
  rw [Fin.prod_univ_five]
  norm_num
  rw [h6, h9, h12]
  have hkey := goodDiscFactorAux (x 0) (x 3) (B * x 4) ζ hΦ
  rw [show (x 0 + x 3 + B * x 4) * (x 0 + ζ * x 3 + B * ζ ^(3:ℕ) * x 4) *
          (x 0 + ζ ^(2:ℕ) * x 3 + B * ζ * x 4) * (x 0 + ζ ^(3:ℕ) * x 3 + B * ζ ^(4:ℕ) * x 4) *
          (x 0 + ζ ^(4:ℕ) * x 3 + B * ζ ^(2:ℕ) * x 4)
        = (x 0 + x 3 + B * x 4) * (x 0 + x 3 * ζ + (B * x 4) * ζ ^(3:ℕ)) *
          (x 0 + x 3 * ζ ^(2:ℕ) + (B * x 4) * ζ) * (x 0 + x 3 * ζ ^(3:ℕ) + (B * x 4) * ζ ^(4:ℕ)) *
          (x 0 + x 3 * ζ ^(4:ℕ) + (B * x 4) * ζ ^(2:ℕ)) from by ring]
  rw [hkey]
  first | refl_ring1 | ring

end Work.MotK.TwCensus
