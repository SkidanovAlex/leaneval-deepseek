import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZpgI4W4NonZeroDiv`

`zpgW4 a b h` is a non-zero-divisor modulo the chart ideal `zpgI4 a b h` of the twisted Klein
curve.

The five chart quadrics `zpgQ a b h k` have leading monomials (`X 0 = y₁, X 1 = y₂, X 2 = y₃`,
`X 3 = y₄`)

  `X 0 ^ 2, X 0 * X 1, X 1 ^ 2, X 1 * X 2, X 2 ^ 2`

— none of which involves `X 3`.  Consequently the quotient `B = K[X₀..X₃] ⧸ zpgI4 a b h` is
generated, as a module over `K[X 3]`, by the five standard monomials
`1, X 0, X 1, X 2, X 0 * X 2`, and (being torsion-free over the PID `K[X 3]`, since no non-zero
polynomial in `X 3` alone can satisfy a relation) it is *free* of rank `5`.  Multiplication by
`zpgW4` is then a `K[X 3]`-linear endomorphism of a free module whose matrix has a non-zero
determinant, hence is injective.

This file contains the elementary reduction identities on which the argument rests.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## Componentwise unfoldings of the five chart quadrics -/

@[simp] theorem zpgQ_zero (a b h : K) :
    zpgQ a b h 0 = -(C (a*b)) + C (a^(2:ℕ)*h^(2:ℕ)) * X 1 * X 2 - C (b^(2:ℕ)*h^(2:ℕ)) * X 0 * X 3 := rfl

@[simp] theorem zpgQ_one (a b h : K) :
    zpgQ a b h 1 = -(C (a*b)) * (X 1)^(2:ℕ) + C (a^(2:ℕ)) * X 3 - C (b^(2:ℕ)) * X 0 * X 2 := rfl

@[simp] theorem zpgQ_two (a b h : K) :
    zpgQ a b h 2 = -(C (a*b*h^(2:ℕ))) * (X 3)^(2:ℕ) + C (a^(2:ℕ)) * X 0 * X 1 - C (b^(2:ℕ)) * X 2 := rfl

@[simp] theorem zpgQ_three (a b h : K) :
    zpgQ a b h 3 = -(C (a*b)) * (X 0)^(2:ℕ) + C (a^(2:ℕ)*h^(2:ℕ)) * X 2 * X 3 - C (b^(2:ℕ)) * X 1 := rfl

@[simp] theorem zpgQ_four (a b h : K) :
    zpgQ a b h 4 = -(C (a*b*h^(2:ℕ))) * (X 2)^(2:ℕ) + C (a^(2:ℕ)) * X 0 - C (b^(2:ℕ)*h^(2:ℕ)) * X 1 * X 3 := rfl

/-- If a scalar multiple `C c * f` of `f` lies in the chart ideal, then so does `f`
(division by the non-zero constant `c`). -/
theorem mem_of_C_mul_mem (a b h c : K) (hc : c ≠ 0) {f : MvPolynomial (Fin 4) K}
    (hmem : (C c : MvPolynomial (Fin 4) K) * f ∈ zpgI4 a b h) : f ∈ zpgI4 a b h := by
  have : f = (C c⁻¹ : MvPolynomial (Fin 4) K) * (C c * f) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hmem

/-- The five spanning monomials `1, X₀, X₁, X₂, X₀X₂`. -/
noncomputable def zpgStdM {K : Type} [CommSemiring K] : Fin 5 → MvPolynomial (Fin 4) K :=
  ![1, X 0, X 1, X 2, X 0 * X 2]

/-- The coefficient embedding `K[X₃] → K[X₀,X₁,X₂,X₃]` (`X i ↦ X 3`, the unique variable). -/
noncomputable def zpgEmb (K : Type) [CommSemiring K] :
    MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.rename (fun _ => (3 : Fin 4))

/-- **The multiplication matrix of `zpgW4`** in the spanning monomials `1, X₀, X₁, X₂, X₀X₂`
over `K[X₃]`; the `i`-th column expands `zpgW4 * (zpgStdM i)` (see `zpgWMat_mul`). -/
noncomputable def zpgWMat (a b h : K) : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 1) K) :=
  !![0, C (a^(2:ℕ)*b^(2:ℕ)*h^(4:ℕ)) * (X 0)^(3:ℕ), C (b^(5:ℕ)*h^(2:ℕ)/a) * (X 0)^(2:ℕ), C (a^(2:ℕ)*b^(2:ℕ)) * X 0,
      C (b*(a^(5:ℕ)-b^(5:ℕ))/(a^(2:ℕ)*h^(2:ℕ)));
    C (-((a^(5:ℕ)-b^(5:ℕ))/b)), 0, 0, C (a*b^(3:ℕ)*h^(2:ℕ)) * (X 0)^(2:ℕ),
      C (-((a^(10:ℕ)-3*a^(5:ℕ)*b^(5:ℕ)+b^(10:ℕ))/(a^(3:ℕ)*b^(3:ℕ)))) * X 0;
    C (a^(3:ℕ)*b*h^(2:ℕ)) * X 0, C ((a^(5:ℕ)-b^(5:ℕ))/a), 0, 0, C (h^(2:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))/b) * (X 0)^(2:ℕ);
    0, C (-(a*h^(2:ℕ)*(a^(5:ℕ)-2*b^(5:ℕ))/b^(2:ℕ))) * X 0, C (-(b*(a^(5:ℕ)-b^(5:ℕ))/a^(2:ℕ))), 0,
      C (a^(2:ℕ)*b^(2:ℕ)*h^(4:ℕ)) * (X 0)^(3:ℕ);
    0, 0, C (-(a^(2:ℕ)*b^(2:ℕ)*h^(2:ℕ))) * X 0, C (-((a^(5:ℕ)-b^(5:ℕ))/b)), 0]

/-- **Reduction 1** (`zpgQ 3`): `X₀²` reduces modulo `zpgI4` to a `K[X₃]`-combination of
`X₂`, `X₁`. -/
theorem red_zero_sq (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (X 0 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a*h^(2:ℕ)/b) * X 2 * X 3 - C (b/a) * X 1) ∈ zpgI4 a b h := by
  have hq : zpgQ a b h 3 ∈ zpgI4 a b h := Ideal.subset_span ⟨3, rfl⟩
  have h1 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (a*b) = -1 := by
    rw [← map_mul, show (-(a*b))⁻¹ * (a*b) = -1 from by
      rw [inv_neg, neg_mul, inv_mul_cancel₀ (mul_ne_zero ha hb)], map_neg, map_one]
  have h2 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (a^(2:ℕ)*h^(2:ℕ)) = - C (a*h^(2:ℕ)/b) := by
    rw [← map_mul, show (-(a*b))⁻¹ * (a^(2:ℕ)*h^(2:ℕ)) = -(a*h^(2:ℕ)/b) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have h3 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (b^(2:ℕ)) = - C (b/a) := by
    rw [← map_mul, show (-(a*b))⁻¹ * (b^(2:ℕ)) = -(b/a) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have key : (X 0 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a*h^(2:ℕ)/b) * X 2 * X 3 - C (b/a) * X 1)
      = C ((-(a*b))⁻¹) * zpgQ a b h 3 := by
    rw [show zpgQ a b h 3 = -(C (a*b)) * (X 0)^(2:ℕ) + C (a^(2:ℕ)*h^(2:ℕ)) * X 2 * X 3 - C (b^(2:ℕ)) * X 1 from rfl]
    simp only [mul_add, mul_sub, mul_neg, neg_mul, ← mul_assoc]
    rw [h1, h2, h3]
    refl_ring1
  rw [key]
  exact Ideal.mul_mem_left _ _ hq

/-- **Reduction 2** (`zpgQ 2`): `X₀X₁` reduces modulo `zpgI4` to a combination of `X₂`, `X₃²`. -/
theorem red_zero_one (a b h : K) (ha : a ≠ 0) :
    (X 0 * X 1 : MvPolynomial (Fin 4) K)
      - (C (b^(2:ℕ)/a^(2:ℕ)) * X 2 + C (b*h^(2:ℕ)/a) * (X 3)^(2:ℕ)) ∈ zpgI4 a b h := by
  have hq : zpgQ a b h 2 ∈ zpgI4 a b h := Ideal.subset_span ⟨2, rfl⟩
  have h1 : (C ((a^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (a*b*h^(2:ℕ)) = C (b*h^(2:ℕ)/a) := by
    rw [← map_mul, show (a^(2:ℕ))⁻¹ * (a*b*h^(2:ℕ)) = b*h^(2:ℕ)/a from by field_simp]
  have h2 : (C ((a^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (a^(2:ℕ)) = 1 := by
    rw [← map_mul, show (a^(2:ℕ))⁻¹ * a^(2:ℕ) = 1 from by field_simp, map_one]
  have h3 : (C ((a^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (b^(2:ℕ)) = C (b^(2:ℕ)/a^(2:ℕ)) := by
    rw [← map_mul, show (a^(2:ℕ))⁻¹ * b^(2:ℕ) = b^(2:ℕ)/a^(2:ℕ) from by field_simp]
  have key : (X 0 * X 1 : MvPolynomial (Fin 4) K)
      - (C (b^(2:ℕ)/a^(2:ℕ)) * X 2 + C (b*h^(2:ℕ)/a) * (X 3)^(2:ℕ))
      = C ((a^(2:ℕ))⁻¹) * zpgQ a b h 2 := by
    rw [show zpgQ a b h 2
      = -(C (a*b*h^(2:ℕ))) * (X 3)^(2:ℕ) + C (a^(2:ℕ)) * X 0 * X 1 - C (b^(2:ℕ)) * X 2 from rfl]
    simp only [mul_add, mul_sub, mul_neg, neg_mul, ← mul_assoc]
    rw [h1, h2, h3]
    refl_ring1
  rw [key]
  exact Ideal.mul_mem_left _ _ hq

/-- **Reduction 3** (`zpgQ 1`): `X₁²` reduces modulo `zpgI4` to a combination of `X₃`, `X₀X₂`. -/
theorem red_one_sq (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (X 1 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a/b) * X 3 - C (b/a) * X 0 * X 2) ∈ zpgI4 a b h := by
  have hq : zpgQ a b h 1 ∈ zpgI4 a b h := Ideal.subset_span ⟨1, rfl⟩
  have h1 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (a*b) = -1 := by
    rw [← map_mul, show (-(a*b))⁻¹ * (a*b) = -1 from by
      rw [inv_neg, neg_mul, inv_mul_cancel₀ (mul_ne_zero ha hb)], map_neg, map_one]
  have h2 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (a^(2:ℕ)) = - C (a/b) := by
    rw [← map_mul, show (-(a*b))⁻¹ * (a^(2:ℕ)) = -(a/b) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have h3 : (C ((-(a*b))⁻¹) : MvPolynomial (Fin 4) K) * C (b^(2:ℕ)) = - C (b/a) := by
    rw [← map_mul, show (-(a*b))⁻¹ * (b^(2:ℕ)) = -(b/a) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have key : (X 1 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a/b) * X 3 - C (b/a) * X 0 * X 2)
      = C ((-(a*b))⁻¹) * zpgQ a b h 1 := by
    rw [show zpgQ a b h 1 = -(C (a*b)) * (X 1)^(2:ℕ) + C (a^(2:ℕ)) * X 3 - C (b^(2:ℕ)) * X 0 * X 2 from rfl]
    simp only [mul_add, mul_sub, mul_neg, neg_mul, ← mul_assoc]
    rw [h1, h2, h3]
    refl_ring1
  rw [key]
  exact Ideal.mul_mem_left _ _ hq

/-- **Reduction 4** (`zpgQ 0`): `X₁X₂` reduces modulo `zpgI4` to a constant plus a multiple of
`X₀X₃`. -/
theorem red_one_two (a b h : K) (ha : a ≠ 0) (hh : h ≠ 0) :
    (X 1 * X 2 : MvPolynomial (Fin 4) K)
      - (C (b/(a*h^(2:ℕ))) + C (b^(2:ℕ)/a^(2:ℕ)) * X 0 * X 3) ∈ zpgI4 a b h := by
  have hq : zpgQ a b h 0 ∈ zpgI4 a b h := Ideal.subset_span ⟨0, rfl⟩
  have h1 : (C ((a^(2:ℕ)*h^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (a*b) = C (b/(a*h^(2:ℕ))) := by
    rw [← map_mul, show (a^(2:ℕ)*h^(2:ℕ))⁻¹ * (a*b) = b/(a*h^(2:ℕ)) from by field_simp]
  have h2 : (C ((a^(2:ℕ)*h^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (a^(2:ℕ)*h^(2:ℕ)) = 1 := by
    rw [← map_mul, show (a^(2:ℕ)*h^(2:ℕ))⁻¹ * (a^(2:ℕ)*h^(2:ℕ)) = 1 from by field_simp, map_one]
  have h3 : (C ((a^(2:ℕ)*h^(2:ℕ))⁻¹) : MvPolynomial (Fin 4) K) * C (b^(2:ℕ)*h^(2:ℕ)) = C (b^(2:ℕ)/a^(2:ℕ)) := by
    rw [← map_mul, show (a^(2:ℕ)*h^(2:ℕ))⁻¹ * (b^(2:ℕ)*h^(2:ℕ)) = b^(2:ℕ)/a^(2:ℕ) from by field_simp]
  have key : (X 1 * X 2 : MvPolynomial (Fin 4) K)
      - (C (b/(a*h^(2:ℕ))) + C (b^(2:ℕ)/a^(2:ℕ)) * X 0 * X 3)
      = C ((a^(2:ℕ)*h^(2:ℕ))⁻¹) * zpgQ a b h 0 := by
    rw [show zpgQ a b h 0
      = -(C (a*b)) + C (a^(2:ℕ)*h^(2:ℕ)) * X 1 * X 2 - C (b^(2:ℕ)*h^(2:ℕ)) * X 0 * X 3 from rfl]
    simp only [mul_add, mul_sub, mul_neg, neg_mul, ← mul_assoc]
    rw [h1, h2, h3]
    refl_ring1
  rw [key]
  exact Ideal.mul_mem_left _ _ hq

/-- **Reduction 5** (`zpgQ 4`): `X₂²` reduces modulo `zpgI4` to a combination of `X₀`, `X₁X₃`. -/
theorem red_two_sq (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    (X 2 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a/(b*h^(2:ℕ))) * X 0 - C (b/a) * X 1 * X 3) ∈ zpgI4 a b h := by
  have hq : zpgQ a b h 4 ∈ zpgI4 a b h := Ideal.subset_span ⟨4, rfl⟩
  have h1 : (C ((-(a*b*h^(2:ℕ)))⁻¹) : MvPolynomial (Fin 4) K) * C (a*b*h^(2:ℕ)) = -1 := by
    rw [← map_mul, show (-(a*b*h^(2:ℕ)))⁻¹ * (a*b*h^(2:ℕ)) = -1 from by
      rw [inv_neg, neg_mul,
        inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero 2 hh))], map_neg, map_one]
  have h2 : (C ((-(a*b*h^(2:ℕ)))⁻¹) : MvPolynomial (Fin 4) K) * C (a^(2:ℕ)) = - C (a/(b*h^(2:ℕ))) := by
    rw [← map_mul, show (-(a*b*h^(2:ℕ)))⁻¹ * (a^(2:ℕ)) = -(a/(b*h^(2:ℕ))) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have h3 : (C ((-(a*b*h^(2:ℕ)))⁻¹) : MvPolynomial (Fin 4) K) * C (b^(2:ℕ)*h^(2:ℕ)) = - C (b/a) := by
    rw [← map_mul, show (-(a*b*h^(2:ℕ)))⁻¹ * (b^(2:ℕ)*h^(2:ℕ)) = -(b/a) from by
      rw [inv_neg, neg_mul]; congr 1; field_simp, map_neg]
  have key : (X 2 : MvPolynomial (Fin 4) K)^(2:ℕ)
      - (C (a/(b*h^(2:ℕ))) * X 0 - C (b/a) * X 1 * X 3)
      = C ((-(a*b*h^(2:ℕ)))⁻¹) * zpgQ a b h 4 := by
    rw [show zpgQ a b h 4
      = -(C (a*b*h^(2:ℕ))) * (X 2)^(2:ℕ) + C (a^(2:ℕ)) * X 0 - C (b^(2:ℕ)*h^(2:ℕ)) * X 1 * X 3 from rfl]
    simp only [mul_add, mul_sub, mul_neg, neg_mul, ← mul_assoc]
    rw [h1, h2, h3]
    refl_ring1
  rw [key]
  exact Ideal.mul_mem_left _ _ hq

/-- **Assembly (main argument).**  Assume that

* the five standard monomials `1, X₀, X₁, X₂, X₀X₂` span `zpgI4` over `K[X₃]` (`hSpan`),
* they are linearly independent modulo `zpgI4` (`hInd`),
* `zpgWMat` is the multiplication matrix of `zpgW4` on them (`hMul`),
* its determinant is non-zero (`hDet`).

Then `zpgW4` is a non-zero-divisor modulo `zpgI4`. -/
theorem ZpgI4W4NonZeroDiv_of (K : Type) [Field K] (a b h : K)
    (hSpan : ∀ f : MvPolynomial (Fin 4) K, ∃ g : Fin 5 → MvPolynomial (Fin 1) K,
      f - (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i) ∈ zpgI4 a b h)
    (hInd : ∀ g : Fin 5 → MvPolynomial (Fin 1) K,
      (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i) ∈ zpgI4 a b h → ∀ i, g i = 0)
    (hMul : ∀ i : Fin 5, zpgW4 a b h * zpgStdM (K := K) i
      - (∑ j : Fin 5, zpgEmb K (zpgWMat (K := K) a b h j i) * zpgStdM (K := K) j)
        ∈ zpgI4 a b h)
    (hDet : (zpgWMat (K := K) a b h).det ≠ 0)
    (u : MvPolynomial (Fin 4) K) (hu : zpgW4 a b h * u ∈ zpgI4 a b h) :
    u ∈ zpgI4 a b h := by
  classical
  obtain ⟨g, hg⟩ := hSpan u
  -- Step 1: `zpgW4 * (Σ gᵢ Sᵢ) ∈ I`.
  have hW : zpgW4 a b h * (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i)
      ∈ zpgI4 a b h := by
    have hsplit : (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i)
        = u - (u - ∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i) := by abel
    rw [hsplit, mul_sub]
    exact Ideal.sub_mem _ hu (Ideal.mul_mem_left _ _ hg)
  -- Step 2a: the same expression, written with the `zpgW4` factor distributed.
  have hW' : (∑ i : Fin 5, zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i))
      ∈ zpgI4 a b h := by
    have heq : zpgW4 a b h * (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i)
        = ∑ i : Fin 5, zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      refl_ring1
    rw [← heq]
    exact hW
  -- Step 2b: replace each `W * Sᵢ` by its matrix expansion.
  have hcomb : ∀ i : Fin 5, zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i)
      - (∑ j : Fin 5, zpgEmb K (g i * zpgWMat (K := K) a b h j i) * zpgStdM (K := K) j)
      ∈ zpgI4 a b h := by
    intro i
    have hred := Ideal.mul_mem_left (zpgI4 a b h) (zpgEmb K (g i)) (hMul i)
    have heq : zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i
          - (∑ j : Fin 5, zpgEmb K (zpgWMat (K := K) a b h j i) * zpgStdM (K := K) j))
        = zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i)
          - (∑ j : Fin 5, zpgEmb K (g i * zpgWMat (K := K) a b h j i)
              * zpgStdM (K := K) j) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul]
      refl_ring1
    rwa [heq] at hred
  -- Step 2c: sum over `i` and collect the coefficients.
  have hsum2 : (∑ j : Fin 5, zpgEmb K (∑ i : Fin 5, g i * zpgWMat (K := K) a b h j i)
      * zpgStdM (K := K) j) ∈ zpgI4 a b h := by
    have h2 : (∑ i : Fin 5, (zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i)
        - (∑ j : Fin 5, zpgEmb K (g i * zpgWMat (K := K) a b h j i)
            * zpgStdM (K := K) j))) ∈ zpgI4 a b h :=
      Ideal.sum_mem _ fun i _ => hcomb i
    have h3 : (∑ i : Fin 5, (zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i)
        - (∑ j : Fin 5, zpgEmb K (g i * zpgWMat (K := K) a b h j i)
            * zpgStdM (K := K) j)))
        = (∑ i : Fin 5, zpgEmb K (g i) * (zpgW4 a b h * zpgStdM (K := K) i))
          - (∑ j : Fin 5, zpgEmb K (∑ i : Fin 5, g i * zpgWMat (K := K) a b h j i)
              * zpgStdM (K := K) j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← map_sum]
    rw [h3] at h2
    simpa using Ideal.sub_mem _ hW' h2
  -- Step 3: the coefficients of the reduced combination vanish.
  have hvec : ∀ j : Fin 5, (∑ i : Fin 5, zpgWMat (K := K) a b h j i * g i) = 0 := by
    intro j
    have hcoeff := hInd (fun i => ∑ i' : Fin 5, g i' * zpgWMat (K := K) a b h i i') hsum2 j
    calc (∑ i : Fin 5, zpgWMat (K := K) a b h j i * g i)
        = ∑ i : Fin 5, g i * zpgWMat (K := K) a b h j i := by
          apply Finset.sum_congr rfl
          intro i _
          refl_ring1
      _ = 0 := hcoeff
  -- Step 4: `zpgWMat *ᵥ g = 0` with `det ≠ 0` forces `g = 0`.
  have hg0 : g = 0 := by
    have hmv : (zpgWMat (K := K) a b h).mulVec g = 0 := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      exact hvec j
    refine Matrix.mulVec_injective_of_det_ne_zero hDet ?_
    rw [hmv, Matrix.mulVec_zero]
  -- Step 5: conclude.
  have hzero : (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hg0]
    simp
  rw [hzero, sub_zero] at hg
  exact hg

/-- The `Finset`-sum of the five standard monomials is the explicit expansion appearing in the
statements of the companion lemmas. -/
theorem zpgSum_eq {K : Type} [CommSemiring K] (g : Fin 5 → MvPolynomial (Fin 1) K) :
    (∑ i : Fin 5, zpgEmb K (g i) * zpgStdM (K := K) i)
      = zpgEmb K (g 0) + zpgEmb K (g 1) * (X 0 : MvPolynomial (Fin 4) K)
        + zpgEmb K (g 2) * X 1 + zpgEmb K (g 3) * X 2 + zpgEmb K (g 4) * (X 0 * X 2) := by
  simp only [Fin.sum_univ_five, zpgStdM, zpgEmb, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, mul_one]

end Work.MotK.TGen
