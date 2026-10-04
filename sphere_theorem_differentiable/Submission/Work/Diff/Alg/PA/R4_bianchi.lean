import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second Bianchi identity (algebraic form) for `R4`

For an algebraic curvature tensor `R` (antisymmetry in the first pair, symmetry of the two pairs,
first Bianchi identity, see `Submission.Diff.Alg.IsAlgCurv`) the cyclic sum
`R4 R x y z w + R4 R y z x w + R4 R z x y w` vanishes. This is the algebraic Bianchi identity
(`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`) in fully covariant form: since `R4 R x y z w` equals
`⟪R(x,y)z, w⟫` for the curvature tensor and `R k l m n` is antisymmetric in `(m,n)`, the cyclic sum
of `⟪R(x,y)z,w⟫` is the contraction of the first Bianchi identity with `x ⊗ y ⊗ z ⊗ w`.

The proof is pure index gymnastics: unfold `R4` into the four-fold sum, cyclically rename the
indices in the second and third terms (`sum4_cycle`, `sum4_cycle2`), and apply the componentwise
first Bianchi identity `R i j k l + R j k i l + R k i j l = 0` under the sum.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Splitting a sum of three sums: `(∑ f) + (∑ g) + (∑ h) = ∑ (f + g + h)`. -/
theorem sum3_add_eq {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ i, f i) + (∑ i, g i) + (∑ i, h i) = ∑ i, (f i + g i + h i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- `R4 R y z x w` in the standard index pattern. -/
theorem R4_cycle₁ (R : Curv4 n) (x y z w : Fin n → ℝ) :
    R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * x i * y j * z k * w l := by
  calc R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * y i * z j * x k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * y j * z k * x i * w l := sum4_cycle _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * x i * y j * z k * w l := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring

/-- `R4 R z x y w` in the standard index pattern. -/
theorem R4_cycle₂ (R : Curv4 n) (x y z w : Fin n → ℝ) :
    R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * x i * y j * z k * w l := by
  calc R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * z i * x j * y k * w l := rfl
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * z k * x i * y j * w l := sum4_cycle2 _
    _ = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * x i * y j * z k * w l := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring

/-- Cyclic-form Bianchi identity for an algebraic curvature tensor:
`R4 R x y z w + R4 R y z x w + R4 R z x y w = 0`. -/
theorem R4_bianchi (n : ℕ) (R : Curv4 n) (hR : IsAlgCurv R) (x y z w : Fin n → ℝ) :
    R4 R x y z w + R4 R y z x w + R4 R z x y w = 0 := by
  have h1 : R4 R x y z w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * x i * y j * z k * w l := rfl
  -- the componentwise first Bianchi identity, contracted with `x ⊗ y ⊗ z ⊗ w`
  have hz : ∀ i j k l : Fin n,
      R i j k l * x i * y j * z k * w l + R j k i l * x i * y j * z k * w l
        + R k i j l * x i * y j * z k * w l = 0 := by
    intro i j k l
    calc R i j k l * x i * y j * z k * w l + R j k i l * x i * y j * z k * w l
          + R k i j l * x i * y j * z k * w l
        = (R i j k l + R j k i l + R k i j l) * (x i * y j * z k * w l) := by ring
      _ = 0 := by rw [hR.2.2 i j k l, zero_mul]
  rw [h1, R4_cycle₁ R x y z w, R4_cycle₂ R x y z w]
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [sum3_add_eq]
  exact Finset.sum_eq_zero (fun l _ => hz i j k l)

end Work.Diff.Alg.PA
