import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `(0,2)`-tensor action of `O(n)`, and linearity of `rot`

`Submission.Diff.Alg.rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d` is the
change of orthonormal frame `e'_i = ∑_a A i a e_a` on a `4`-index curvature array.

A `(0,2)`-tensor `M` transforms by *two* copies of `A` rather than one, and it is convenient to
have a separate name for that:

`rot2 A M i j = ∑ a b, A i a * A j b * M a b`.

For `R : Curv4 n` the Ricci-type contractions of `rot A R` are obtained by applying `rot2 A` to the
corresponding contractions of `R` (`ric (rot A R) = rot2 A (ric R)`, `ric0 (rot A R) = rot2 A (ric0 R)`,
`ric0sq (rot A R) = rot2 A (ric0sq R)`), and the scalar contractions (`scalAlg`, `ric0Frob2`) are
invariant; these facts are what make the Böhm–Wilking difference tensor `D_{a,b}` equivariant under
`O(n)` (`Work.Diff.Alg.Pinch.Dtensor_rot`).

This module contains only the definition and the elementary linearity lemmas for `rot` and `rot2`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The action of `A` on `(0,2)`-tensors by two-sided multiplication, `(rot2 A M)ᵢⱼ = ∑_{a b} Aᵢₐ Aⱼᵦ Mₐᵦ`. -/
noncomputable def rot2 (A : Matrix (Fin n) (Fin n) ℝ) (M : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ a, ∑ b, A i a * A j b * M a b

/-! ## Linearity of `rot2` -/

lemma rot2_add (A : Matrix (Fin n) (Fin n) ℝ) (M N : Fin n → Fin n → ℝ) :
    rot2 A (M + N) = rot2 A M + rot2 A N := by
  funext i j
  simp only [rot2, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma rot2_sub (A : Matrix (Fin n) (Fin n) ℝ) (M N : Fin n → Fin n → ℝ) :
    rot2 A (M - N) = rot2 A M - rot2 A N := by
  funext i j
  simp only [rot2, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rot2_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (M : Fin n → Fin n → ℝ) :
    rot2 A (c • M) = c • rot2 A M := by
  funext i j
  simp only [rot2, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

/-! ## Linearity of `rot` -/

lemma rot_add_lin (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Curv4 n) :
    rot A (X + Y) = rot A X + rot A Y := by
  funext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma rot_sub_lin (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Curv4 n) :
    rot A (X - Y) = rot A X - rot A Y := by
  funext i j k l
  simp only [rot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rot_smul_lin (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (X : Curv4 n) :
    rot A (c • X) = c • rot A X := by
  funext i j k l
  simp only [rot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

end Work.Diff.Alg.Pinch
