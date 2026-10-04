import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The algebraic Bianchi identity for `R4`

For an algebraic curvature tensor `R : Curv4 n` (antisymmetry in the first pair, symmetry of the
two pairs, first Bianchi identity — see `Submission.Diff.Alg.IsAlgCurv`) and arbitrary vectors
`x y z w : Fin n → ℝ` the cyclic sum of the fully covariant curvature vanishes:

`R4 R x y z w + R4 R y z x w + R4 R z x y w = 0`.

This is the algebraic Bianchi identity `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0` in fully covariant form:
`R4 R x y z w` is the contraction `∑ Rᵢⱼₖₗ xᵢ yⱼ zₖ wₗ` of the components with `x ⊗ y ⊗ z ⊗ w`, and
the componentwise identity `Rᵢⱼₖₗ + Rⱼₖᵢₗ + Rₖᵢⱼₗ = 0` propagates through the contraction because
`R4` is multilinear. Concretely, the cyclic renamings `sum4_cycle` and `sum4_cycle2` of the
four-fold sum put the second and third terms into the index pattern of the first one, after which
the three sums are combined term by term and each term vanishes by the Bianchi hypothesis.

Nothing here uses the symmetries `R j i k l = - R i j k l` or `R k l i j = R i j k l`: only the
third conjunct of `IsAlgCurv` is needed.
-/

namespace Work.Diff.Alg.Q2PB

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary reorderings of a four-fold sum

All four are instances of `Finset.sum_comm` (the swap of two adjacent binders), read as an index
renaming; only the first three indices are ever cycled, the fourth slot is a spectator. -/

/-- Swap the first two summation indices of a four-fold sum. -/
theorem sum4_swap12 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j i k l := by
  rw [Finset.sum_comm]

/-- Swap the second and third summation indices of a four-fold sum. -/
theorem sum4_swap23 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- Cyclically permute the first three summation indices, `(i,j,k) ↦ (j,k,i)`. -/
theorem sum4_cycle (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F j k i l := by
  rw [sum4_swap23 F]
  exact sum4_swap12 (fun i j k l => F i k j l)

/-- Cyclically permute the first three summation indices, `(i,j,k) ↦ (k,i,j)`. -/
theorem sum4_cycle2 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, F i j k l) = ∑ i, ∑ j, ∑ k, ∑ l, F k i j l := by
  rw [sum4_cycle F]
  exact sum4_cycle (fun i j k l => F j k i l)

/-- Splitting a sum of three sums: `(∑ f) + (∑ g) + (∑ h) = ∑ (f + g + h)`. -/
theorem sum3_add_eq {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ i, f i) + (∑ i, g i) + (∑ i, h i) = ∑ i, (f i + g i + h i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-! ## The Bianchi identity -/

theorem r4_bianchi {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (x y z w : Fin n → ℝ) :
    Submission.Diff.Alg.R4 R x y z w + Submission.Diff.Alg.R4 R y z x w
      + Submission.Diff.Alg.R4 R z x y w = 0 := by
  -- the componentwise first Bianchi identity, contracted with `x ⊗ y ⊗ z ⊗ w`
  have hz : ∀ i j k l : Fin n,
      R i j k l * x i * y j * z k * w l + R j k i l * x i * y j * z k * w l
        + R k i j l * x i * y j * z k * w l = 0 := by
    intro i j k l
    linear_combination (x i * y j * z k * w l) * hR.2.2 i j k l
  -- `R4` unfolded, and the two cyclic renaming steps
  have h1 : R4 R x y z w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * x i * y j * z k * w l := rfl
  have h2 : R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l * x i * y j * z k * w l := by
    rw [show R4 R y z x w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * y i * z j * x k * w l from rfl,
      sum4_cycle]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  have h3 : R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l * x i * y j * z k * w l := by
    rw [show R4 R z x y w = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * z i * x j * y k * w l from rfl,
      sum4_cycle2]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  rw [h1, h2, h3, sum3_add_eq]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [sum3_add_eq]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [sum3_add_eq]
  exact Finset.sum_eq_zero fun l _ => hz i j k l

end Work.Diff.Alg.Q2PB
