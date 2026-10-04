import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Rot2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Kulkarni–Nomizu product is natural under `rot`

`Work.Diff.Alg.Pinch.knProd` is the Kulkarni–Nomizu product
`(A ∧ B)ᵢⱼₖₗ = AᵢₖBⱼₗ − AᵢₗBⱼₖ − AⱼₖBᵢₗ + AⱼₗBᵢₖ`, while
`Submission.Diff.Alg.rot A` is the fourfold change of frame
`rot A R i j k l = ∑ a b c d, Aᵢₐ Aⱼᵦ Aₖ_c Aₗ_d R a b c d`
and `Work.Diff.Alg.Pinch.rot2 A` is the `(0,2)`-tensor companion `rot2 A M i j = ∑ a b, Aᵢₐ Aⱼᵦ M a b`.

The main result, `Work.Diff.Alg.Pinch.rot_knProd`, is that `rot` is an algebra automorphism for the
Kulkarni–Nomizu product: `rot A (knProd X Y) = knProd (rot2 A X) (rot2 A Y)`.  No hypothesis on `A`
is needed: the identity is purely multilinear in the entries of `A`.

## Route

Write `tp X Y i j k l = Xᵢₖ Yⱼₗ` (the "transversal product") and let `sw12`, `sw34` be the index
permutations `(i,j,k,l) ↦ (j,i,k,l)`, `(i,j,k,l) ↦ (i,j,l,k)`.  Then

* `knProd_eq_tp` : `knProd X Y = tp X Y − sw34 (tp X Y) − sw12 (tp X Y) + sw12 (sw34 (tp X Y))`;
* `rot_tp` : `rot A (tp X Y) = tp (rot2 A X) (rot2 A Y)` — here the fourfold sum factors into the
  product of the two double sums `rot2 A X i k` and `rot2 A Y j l` (`sum4_block` reorders the
  summation variables, `sum_mul_sum4` factors the block `∑a∑c ∑b∑d` into a product);
* `rot_sw12`, `rot_sw34` : `rot` commutes with the index permutations;
* `rot_knProd_aux` : the combination of the above on the decomposition, and the main theorem follows
  by rewriting the decomposition on both sides.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The "transversal product" `tp X Y i j k l = Xᵢₖ Yⱼₗ`: the first term of the Kulkarni–Nomizu
product, with `X` acting on the index pair `(i,k)` and `Y` on `(j,l)`. -/
noncomputable def tp (X Y : Fin n → Fin n → ℝ) : Curv4 n := fun i j k l => X i k * Y j l

/-- The index permutation `(i,j,k,l) ↦ (j,i,k,l)` on a `4`-index array. -/
noncomputable def sw12 (R : Curv4 n) : Curv4 n := fun i j k l => R j i k l

/-- The index permutation `(i,j,k,l) ↦ (i,j,l,k)` on a `4`-index array. -/
noncomputable def sw34 (R : Curv4 n) : Curv4 n := fun i j k l => R i j l k

/-! ## Elementary sum manipulations -/

/-- Swap the two inner summation variables of a nested fourfold sum. -/
lemma sum4_block (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := by
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_comm

/-- The block `∑ a ∑ c ∑ b ∑ d` of a product of two functions of two variables is the product of
the two block sums. -/
lemma sum_mul_sum4 (P Q : Fin n → Fin n → ℝ) :
    (∑ a, ∑ c, ∑ b, ∑ d, P a c * Q b d)
      = (∑ a, ∑ c, P a c) * (∑ b, ∑ d, Q b d) := by
  have h1 : ∀ a, (∑ c, ∑ b, ∑ d, P a c * Q b d)
      = (∑ c, P a c) * (∑ b, ∑ d, Q b d) := by
    intro a
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
  calc (∑ a, ∑ c, ∑ b, ∑ d, P a c * Q b d)
      = ∑ a, (∑ c, P a c) * (∑ b, ∑ d, Q b d) :=
        Finset.sum_congr rfl (fun a _ => h1 a)
    _ = (∑ a, ∑ c, P a c) * (∑ b, ∑ d, Q b d) := by rw [← Finset.sum_mul]

/-! ## The transversal product -/

/-- `rot` of the transversal product: the fourfold sum factors as the product of the two `rot2`
transforms. -/
lemma rot_tp (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Fin n → Fin n → ℝ) :
    Submission.Diff.Alg.rot A (tp X Y) = fun i j k l => rot2 A X i k * rot2 A Y j l := by
  funext i j k l
  simp only [Submission.Diff.Alg.rot, tp, rot2]
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * (X a c * Y b d))
        = ∑ a, ∑ b, ∑ c, ∑ d,
            (A i a * A k c * X a c) * (A j b * A l d * Y b d) from by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      ring]
  rw [sum4_block (fun a b c d => (A i a * A k c * X a c) * (A j b * A l d * Y b d))]
  rw [sum_mul_sum4 (fun a c => A i a * A k c * X a c) (fun b d => A j b * A l d * Y b d)]

/-! ## `rot` commutes with the index permutations -/

lemma rot_sw12 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    Submission.Diff.Alg.rot A (sw12 R) = sw12 (Submission.Diff.Alg.rot A R) := by
  funext i j k l
  simp only [Submission.Diff.Alg.rot, sw12]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

lemma rot_sw34 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    Submission.Diff.Alg.rot A (sw34 R) = sw34 (Submission.Diff.Alg.rot A R) := by
  funext i j k l
  simp only [Submission.Diff.Alg.rot, sw34]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## The Kulkarni–Nomizu product as a combination of transversal products -/

/-- The Kulkarni–Nomizu product decomposed into transversal products and index permutations. -/
lemma knProd_eq_tp (X Y : Fin n → Fin n → ℝ) :
    knProd X Y = tp X Y - sw34 (tp X Y) - sw12 (tp X Y) + sw12 (sw34 (tp X Y)) := by
  funext i j k l
  simp only [knProd, tp, sw12, sw34, Pi.sub_apply, Pi.add_apply]

/-- `rot` applied to the Kulkarni–Nomizu combination of a single `4`-index array. -/
lemma rot_knProd_aux (A : Matrix (Fin n) (Fin n) ℝ) (T : Curv4 n) :
    Submission.Diff.Alg.rot A (T - sw34 T - sw12 T + sw12 (sw34 T))
      = Submission.Diff.Alg.rot A T - sw34 (Submission.Diff.Alg.rot A T)
        - sw12 (Submission.Diff.Alg.rot A T) + sw12 (sw34 (Submission.Diff.Alg.rot A T)) := by
  rw [rot_add_lin, rot_sub_lin, rot_sub_lin, rot_sw34, rot_sw12, rot_sw12, rot_sw34]

/-! ## The main theorem -/

/-- The Kulkarni–Nomizu product is natural under the change of frame `rot`:
`rot A (knProd X Y) = knProd (rot2 A X) (rot2 A Y)`.  Orthogonality of `A` is not needed. -/
theorem rot_knProd (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Fin n → Fin n → ℝ) :
    Submission.Diff.Alg.rot A (Work.Diff.Alg.Pinch.knProd X Y)
      = Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.rot2 A X) (Work.Diff.Alg.Pinch.rot2 A Y) := by
  rw [knProd_eq_tp X Y, knProd_eq_tp (rot2 A X) (rot2 A Y), rot_knProd_aux, rot_tp]
  rfl

end Work.Diff.Alg.Pinch
