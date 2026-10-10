import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.aszDpQuad` — a monic quadratic in `X₀` inside the AS residual chart ideal

For `K` a field of characteristic `5`, `a b g : K` with `a² - ab - b² ≠ 0`, `g ∉ ℘(K)` and
`a b ≠ 0`, the ideal `ZIAS a b g = span (range (zcubAS a b g))` of the AS (`Artin--Schreier`)
Crauder--Katz residual chart contains an element of the form

  `X₀² + l(X₁,X₂)·X₀ + A(X₁,X₂)`

with `l, A ∈ K[X₁,X₂]`.

## The proof (a two-generator certificate)

Write `F k := zcubAS a b g k`.  Each `F k` is a polynomial in `X₀` over `K[X₁,X₂]`; group it as

  `F k = Q k · X₀² + L k · X₀ + A k`        (`Q k, L k, A k ∈ K[X₁,X₂]`).

`F 2` and `F 4` have `X₀`-degree `2`, and with

* `α := -a⁴ + a³b + ab³ + b⁴`,   `β := 2a⁴ + a³b - 2a²b² - ab³ + 2b⁴`

one computes (this is the identity `aszQu_ident` below, verified by `ring` over `ℤ`)

  `Q 2 = -2α·X₁ + β`,      `Q 4 = β·X₁`,

so that

  `β·F 2 + 2α·F 4 = β²·X₀² + (β·L 2 + 2α·L 4)·X₀ + (β·A 2 + 2α·A 4)`.

Since `β = 2(a+2b)⁴` in characteristic `5` and `a + 2b ≠ 0` (else `a² - ab - b² = 5b² = 0`),
`β ≠ 0`, so dividing the element `β·F 2 + 2α·F 4 ∈ ZIAS a b g` by the nonzero *scalar* `β²` gives
the required monic quadratic.  Note that `α` is *not* needed to be nonzero: only `β` is divided by.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

/-- `α = -a⁴ + a³b + ab³ + b⁴`. -/
noncomputable def aszQuAlpha (a b : K) : K := -a^(4:ℕ) + a^(3:ℕ)*b + a*b^(3:ℕ) + b^(4:ℕ)

/-- `β = 2a⁴ + a³b - 2a²b² - ab³ + 2b⁴`; in characteristic `5` it is `2(a+2b)⁴`. -/
noncomputable def aszQuBeta (a b : K) : K := 2*a^(4:ℕ) + a^(3:ℕ)*b - 2*a^(2:ℕ)*b^(2:ℕ) - a*b^(3:ℕ) + 2*b^(4:ℕ)

/-- The `X₀`-coefficient `L 2` of `zcubAS a b g 2` (variables `X 0 = X₁`, `X 1 = X₂`). -/
noncomputable def aszQuL2 (a b g : K) : MvPolynomial (Fin 2) K :=
    C (-a^(4:ℕ) + 2 * a^(3:ℕ) * b + a^(2:ℕ) * b^(2:ℕ) - 2 * a * b^(3:ℕ) - b^(4:ℕ)) * (X 0) * (X 1)
    + C (2 * a^(4:ℕ) * g + a^(3:ℕ) * b * g - 2 * a^(2:ℕ) * b^(2:ℕ) * g - a * b^(3:ℕ) * g + 2 * b^(4:ℕ) * g) * (X 1)^(2:ℕ)
    + C (a^(4:ℕ) - a^(3:ℕ) * b - a * b^(3:ℕ) - b^(4:ℕ)) * (X 1)

/-- The `X₀`-free part `A 2` of `zcubAS a b g 2`. -/
noncomputable def aszQuA2 (a b g : K) : MvPolynomial (Fin 2) K :=
    C (-2 * a^(4:ℕ) + a^(2:ℕ) * b^(2:ℕ) - 2 * b^(4:ℕ)) * (X 0)^(3:ℕ)
    + C (2 * a^(4:ℕ) * g + a^(3:ℕ) * b * g - 2 * a^(2:ℕ) * b^(2:ℕ) * g - a * b^(3:ℕ) * g + 2 * b^(4:ℕ) * g) * (X 0)^(2:ℕ) * (X 1)
    + C (2 * a^(4:ℕ) + 2 * a^(3:ℕ) * b + 2 * a * b^(3:ℕ) - 2 * b^(4:ℕ)) * (X 0) * (X 1)^(2:ℕ)
    + C (2 * a^(4:ℕ) + a^(3:ℕ) * b - 2 * a^(2:ℕ) * b^(2:ℕ) - a * b^(3:ℕ) + 2 * b^(4:ℕ)) * (X 0)
    + C (2 * a^(4:ℕ) * g - 2 * a^(3:ℕ) * b * g - 2 * a * b^(3:ℕ) * g - 2 * b^(4:ℕ) * g) * (X 1)^(3:ℕ)
    + C (-a^(4:ℕ) - 2 * a^(2:ℕ) * b^(2:ℕ) - b^(4:ℕ)) * (X 1)^(2:ℕ)

/-- The `X₀`-coefficient `L 4` of `zcubAS a b g 4`. -/
noncomputable def aszQuL4 (a b g : K) : MvPolynomial (Fin 2) K :=
    C (-a^(4:ℕ) + a^(3:ℕ) * b + a * b^(3:ℕ) + b^(4:ℕ)) * (X 0) * (X 1)
    + C (-a^(4:ℕ) + 2 * a^(3:ℕ) * b + a^(2:ℕ) * b^(2:ℕ) - 2 * a * b^(3:ℕ) - b^(4:ℕ)) * (X 1)

/-- The `X₀`-free part `A 4` of `zcubAS a b g 4`. -/
noncomputable def aszQuA4 (a b g : K) : MvPolynomial (Fin 2) K :=
    C (-2 * a^(4:ℕ) + 2 * a^(3:ℕ) * b + 2 * a * b^(3:ℕ) + 2 * b^(4:ℕ)) * (X 0)^(3:ℕ)
    + C (2 * a^(4:ℕ) + a^(3:ℕ) * b - 2 * a^(2:ℕ) * b^(2:ℕ) - a * b^(3:ℕ) + 2 * b^(4:ℕ)) * (X 0)^(2:ℕ)
    + C (2 * a^(4:ℕ) + a^(3:ℕ) * b - 2 * a^(2:ℕ) * b^(2:ℕ) - a * b^(3:ℕ) + 2 * b^(4:ℕ)) * (X 0) * (X 1)^(2:ℕ)
    + C (-a^(4:ℕ) * g + 2 * a^(3:ℕ) * b * g + a^(2:ℕ) * b^(2:ℕ) * g - 2 * a * b^(3:ℕ) * g - b^(4:ℕ) * g) * (X 1)^(3:ℕ)
    + C (-2 * a^(4:ℕ) + 2 * a^(3:ℕ) * b + 2 * a * b^(3:ℕ) + 2 * b^(4:ℕ)) * (X 1)^(2:ℕ)

/-- The `X₀`-coefficient of `β·zcubAS a b g 2 + 2α·zcubAS a b g 4`. -/
noncomputable def aszQuLt (a b g : K) : MvPolynomial (Fin 2) K :=
  C (aszQuBeta a b) * aszQuL2 a b g + C (2 * aszQuAlpha a b) * aszQuL4 a b g

/-- The `X₀`-free part of `β·zcubAS a b g 2 + 2α·zcubAS a b g 4`. -/
noncomputable def aszQuAt (a b g : K) : MvPolynomial (Fin 2) K :=
  C (aszQuBeta a b) * aszQuA2 a b g + C (2 * aszQuAlpha a b) * aszQuA4 a b g

/-- **The certificate identity.**  The combination `β·F 2 + 2α·F 4` of two generators of
`ZIAS a b g` is a quadratic in `X₀` over `K[X₁,X₂]` with `X₀²`-coefficient `β²`. -/
theorem aszQu_ident (a b g : K) :
    C (aszQuBeta a b) * zcubAS a b g 2 + C (2 * aszQuAlpha a b) * zcubAS a b g 4
      = C ((aszQuBeta a b)^(2:ℕ)) * (X 0 : MvPolynomial (Fin 3) K)^(2:ℕ)
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuLt a b g) * X 0
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuAt a b g) := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [zcubAS, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    aszQuAlpha, aszQuBeta, aszQuLt, aszQuAt, aszQuL2, aszQuA2, aszQuL4, aszQuA4,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    map_natCast, map_intCast, MvPolynomial.rename_C, MvPolynomial.rename_X]
  rw [h0, h1]
  first | refl_ring1 | ring

/-- `β = 2(a+2b)⁴` in characteristic `5` (the difference is `-5·(3a³b + 10a²b² + 13ab³ + 6b⁴)`). -/
theorem aszQuBeta_eq (a b : K) : aszQuBeta a b = 2 * (a + 2 * b) ^(4:ℕ) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h : aszQuBeta a b - 2 * (a + 2 * b) ^(4:ℕ)
      = -(5 : K) * (3 * a ^(3:ℕ) * b + 10 * a ^(2:ℕ) * b ^(2:ℕ) + 13 * a * b ^(3:ℕ) + 6 * b ^(4:ℕ)) := by
    simp only [aszQuBeta]
    first | refl_ring1 | ring
  rw [h5, neg_zero, zero_mul, sub_eq_zero] at h
  exact h

theorem aszDpQuad (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^(2:ℕ) - a * b - b ^(2:ℕ) ≠ 0) (hg : ¬ ∃ c : K, c ^(5:ℕ) - c = g) (hab : a * b ≠ 0) :
    ∃ (l A : MvPolynomial (Fin 2) K),
      (MvPolynomial.X 0 ^(2:ℕ)
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A ∈ Work.MotAS.ZIAS a b g) := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  -- `a + 2b ≠ 0` and `β ≠ 0`
  have h2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have hfac : a ^(2:ℕ) - a * b - b ^(2:ℕ) = (a + 2 * b) * (a - 3 * b) + 5 * b ^(2:ℕ) := by ring
    rw [h, zero_mul, zero_add] at hfac
    rw [hfac, h5, zero_mul]
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h32 : (3 : K) * 2 = 1 := by
      have h : (3 : K) * 2 - 1 = (5 : K) * 1 := by ring
      rwa [h5, mul_one, sub_eq_zero] at h
    rw [h2, mul_zero] at h32
    exact one_ne_zero h32.symm
  have hbeta : aszQuBeta a b ≠ 0 := by
    rw [aszQuBeta_eq a b]
    exact mul_ne_zero h2ne (pow_ne_zero 4 h2b)
  -- the two-generator certificate lies in the ideal
  have hG : C (aszQuBeta a b) * zcubAS a b g 2 + C (2 * aszQuAlpha a b) * zcubAS a b g 4
      ∈ ZIAS a b g := by
    have h2 : zcubAS a b g 2 ∈ ZIAS a b g :=
      Ideal.subset_span (Set.mem_range_self (2 : Fin 5))
    have h4 : zcubAS a b g 4 ∈ ZIAS a b g :=
      Ideal.subset_span (Set.mem_range_self (4 : Fin 5))
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h4)
  have hident := aszQu_ident (K := K) a b g
  -- the scalar `β⁻²`
  have hc : C ((aszQuBeta a b) ^(2:ℕ))⁻¹ * C ((aszQuBeta a b) ^(2:ℕ))
      = (1 : MvPolynomial (Fin 3) K) := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero 2 hbeta), map_one]
  have hr : ∀ p : MvPolynomial (Fin 2) K,
      MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (C ((aszQuBeta a b) ^(2:ℕ))⁻¹ * p)
        = C ((aszQuBeta a b) ^(2:ℕ))⁻¹ * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) p := by
    intro p
    rw [map_mul, MvPolynomial.rename_C]
  have key : C ((aszQuBeta a b) ^(2:ℕ))⁻¹
        * (C ((aszQuBeta a b) ^(2:ℕ)) * (X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuLt a b g) * X 0
            + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuAt a b g))
      = (X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)
        + (C ((aszQuBeta a b) ^(2:ℕ))⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuLt a b g)) * X 0
        + C ((aszQuBeta a b) ^(2:ℕ))⁻¹
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (aszQuAt a b g) := by
    rw [mul_add, mul_add, ← mul_assoc (C ((aszQuBeta a b) ^(2:ℕ))⁻¹) (C ((aszQuBeta a b) ^(2:ℕ)))
      ((X 0 : MvPolynomial (Fin 3) K) ^(2:ℕ)), hc, one_mul]
    first | refl_ring1 | ring
  refine ⟨C ((aszQuBeta a b) ^(2:ℕ))⁻¹ * aszQuLt a b g,
    C ((aszQuBeta a b) ^(2:ℕ))⁻¹ * aszQuAt a b g, ?_⟩
  rw [hr (aszQuLt a b g), hr (aszQuAt a b g), ← key, ← hident]
  exact Ideal.mul_mem_left _ _ hG

end Work.MotAS
