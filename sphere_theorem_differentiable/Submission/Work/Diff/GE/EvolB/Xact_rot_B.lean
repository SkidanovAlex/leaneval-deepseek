import Mathlib
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.GE.react.Q_rot
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.EvolB

/-!
# `O(n)`-equivariance of the Uhlenbeck Ricci-action term `Xact`

`Work.Diff.Evol.Xact R i j k l = ∑ p, (ricArr R i p * R p j k l + ricArr R j p * R i p k l
   + ricArr R k p * R i j p l + ricArr R l p * R i j k p)`

(`Submission/Work/Diff/Evol/Calc.lean`), with `ricArr R i j = ∑ a, R a i a j` the Ricci contraction.
Since `Xact` is a contraction of the `(0,2)`-tensor `ricArr R` with `R` in one index, it is a
`(0,4)`-tensor expression and therefore commutes with the orthogonal action
`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`.

**Proof route.**  All index manipulations are already available (sorry-free) in
`Submission/Work/Diff/GE/react/RotKit.lean`:

* `ricArr_rot` — `ricArr (rot A R) i p = ∑ e, A p e * (∑ c, A i c * ricArr R c e)`;
* `contract_Avec` — `∑ p, (∑ e, A p e * u e) * (∑ a, A p a * v a) = ∑ e, u e * v e`;
* `rot_apply_factor`, `rot_apply_factor2/3/4` — `rot` with three of the four sums factored out, so
  that the contraction index can be fed to `contract_Avec`;
* `sum3_*`, `sum4_*` — the nested-sum reorderings.

Write both sides out (four summands each, one per Ricci slot), push the `ricArr_rot` rewrite into each
summand, recognise the contraction `∑ p (∑ e A p e u e) * (∑ a A p a v a)` and use `contract_Avec`,
then reorder the remaining sums (`sum3_*`/`sum4_*`/`Finset.sum_comm`) to match the four summands of
`rot A (Xact R)`.

(There are `sorry`ed stubs `Work.Diff.GE.react.Xact_rot` and `Work.Diff.GE.react.Xact_rot_clean` with
the same statement; they are not yours to edit.  Prove this copy.)

**Status: proved, self-contained.**  The proof below follows exactly the route above: `Xact` is split
into its four Ricci-action slots `XA_B … XD_B` (`Xact_eq_slots_B`), each slot is transformed
pointwise into the `rot`-normal form supplied by `rot_apply_factor{,2,3,4}` (`slotA_pt_B … slotD_pt_B`,
each a `contract_Avec` contraction followed by the nested-sum reorderings `sum_mul_swap_B` and
`sum4_rot_B`), and the four equivariance statements are reassembled with the additivity `rot_add_B`
of `rot`.  Every helper is `private`, so this module cannot clash with the sibling files of the
family.
-/

open Finset Matrix
open Submission.Diff.Alg
open Work.Diff.Evol

variable {n : ℕ}

/-! ## Two elementary reorderings and additivity of `rot` -/

/-- Rotate a fourfold sum: the outermost summation index moves to the back. -/
private theorem sum4_rot_B (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Work.Diff.GE.react.sum4_swap12, Work.Diff.GE.react.sum4_swap23,
    Work.Diff.GE.react.sum4_swap34]

/-- The two summations of a product `(∑ c, G c e) * W e` commute. -/
private theorem sum_mul_swap_B (G : Fin n → Fin n → ℝ) (W : Fin n → ℝ) :
    (∑ e, (∑ c, G c e) * W e) = ∑ c, ∑ e, G c e * W e := by
  rw [show (∑ e, (∑ c, G c e) * W e) = ∑ e, ∑ c, G c e * W e from by
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_mul]]
  exact Finset.sum_comm

/-- `rot A` is additive in the tensor argument. -/
private theorem rot_add_B (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S + T) = rot A S + rot A T := by
  ext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## The four Ricci-action slots of `Xact` -/

/-- The first Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R i p * R p j k l`. -/
private noncomputable def XA_B (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R i p * R p j k l

/-- The second Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R j p * R i p k l`. -/
private noncomputable def XB_B (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R j p * R i p k l

/-- The third Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R k p * R i j p l`. -/
private noncomputable def XC_B (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R k p * R i j p l

/-- The fourth Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R l p * R i j k p`. -/
private noncomputable def XD_B (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R l p * R i j k p

/-- `Xact` is the sum of its four Ricci-action slots. -/
private theorem Xact_eq_slots_B (R : Curv4 n) :
    Xact R = XA_B R + XB_B R + XC_B R + XD_B R := by
  ext i j k l
  simp only [XA_B, XB_B, XC_B, XD_B, Xact, Pi.add_apply, Finset.sum_add_distrib]

/-! ## The four slot lemmas (pointwise) -/

/-- The first slot: `∑ p, ricArr (rot A R) i p * rot A R p j k l` is the `p`-contraction of the
`(0,2)`-tensor `A · ricArr R · Aᵀ` with the suitably `rot`-transformed curvature, as produced by
`rot_apply_factor`. -/
private theorem slotA_pt_B (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) i p * rot A R p j k l)
      = ∑ a, A i a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d
          * (∑ p, ricArr R a p * R p b c d)) := by
  have h1 : ∀ p, ricArr (rot A R) i p * rot A R p j k l
      = (∑ e, A p e * (∑ c, A i c * ricArr R c e))
        * (∑ a, A p a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)) := by
    intro p
    rw [Work.Diff.GE.react.ricArr_rot A hA R i p, Work.Diff.GE.react.rot_apply_factor A R p j k l]
  calc ∑ p, ricArr (rot A R) i p * rot A R p j k l
      = ∑ p, (∑ e, A p e * (∑ c, A i c * ricArr R c e))
            * (∑ a, A p a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A i c * ricArr R c e)
            * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R e b c d) :=
        Work.Diff.GE.react.contract_Avec A hA (fun e => ∑ c, A i c * ricArr R c e)
          (fun a => ∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)
    _ = ∑ c, A i c * (∑ e, ricArr R c e
            * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R e b c d)) := by
        rw [sum_mul_swap_B (fun c e => A i c * ricArr R c e)
              (fun e => ∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R e b c d)]
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = ∑ a, A i a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d
          * (∑ p, ricArr R a p * R p b c d)) := by
        apply Finset.sum_congr rfl; intro c _
        rw [show (∑ e, ricArr R c e * (∑ b, ∑ c', ∑ d, A j b * A k c' * A l d * R e b c' d))
              = ∑ b, ∑ c', ∑ d, A j b * A k c' * A l d
                  * (∑ p, ricArr R c p * R p b c' d) from by
          rw [show (∑ e, ricArr R c e * (∑ b, ∑ c', ∑ d, A j b * A k c' * A l d * R e b c' d))
                = ∑ e, ∑ b, ∑ c', ∑ d,
                    ricArr R c e * (A j b * A k c' * A l d * R e b c' d) from by
              simp only [Finset.mul_sum]]
          rw [show (∑ b, ∑ c', ∑ d, A j b * A k c' * A l d
                  * (∑ p, ricArr R c p * R p b c' d))
                = ∑ b, ∑ c', ∑ d, ∑ p,
                    A j b * A k c' * A l d * (ricArr R c p * R p b c' d) from by
              simp only [Finset.mul_sum]]
          rw [sum4_rot_B (fun e b c' d => ricArr R c e * (A j b * A k c' * A l d * R e b c' d))]
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c' _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The second slot. -/
private theorem slotB_pt_B (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) j p * rot A R i p k l)
      = ∑ b, A j b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d
          * (∑ p, ricArr R b p * R a p c d)) := by
  have h1 : ∀ p, ricArr (rot A R) j p * rot A R i p k l
      = (∑ e, A p e * (∑ c, A j c * ricArr R c e))
        * (∑ b, A p b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)) := by
    intro p
    rw [Work.Diff.GE.react.ricArr_rot A hA R j p, Work.Diff.GE.react.rot_apply_factor2 A R i p k l]
  calc ∑ p, ricArr (rot A R) j p * rot A R i p k l
      = ∑ p, (∑ e, A p e * (∑ c, A j c * ricArr R c e))
            * (∑ b, A p b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A j c * ricArr R c e)
            * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d) :=
        Work.Diff.GE.react.contract_Avec A hA (fun e => ∑ c, A j c * ricArr R c e)
          (fun b => ∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)
    _ = ∑ b, A j b * (∑ e, ricArr R b e
            * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d)) := by
        rw [sum_mul_swap_B (fun c e => A j c * ricArr R c e)
              (fun e => ∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d)]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = ∑ b, A j b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d
          * (∑ p, ricArr R b p * R a p c d)) := by
        apply Finset.sum_congr rfl; intro b _
        rw [show (∑ e, ricArr R b e * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d))
              = ∑ a, ∑ c, ∑ d, A i a * A k c * A l d
                  * (∑ p, ricArr R b p * R a p c d) from by
          rw [show (∑ e, ricArr R b e * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d))
                = ∑ e, ∑ a, ∑ c, ∑ d,
                    ricArr R b e * (A i a * A k c * A l d * R a e c d) from by
              simp only [Finset.mul_sum]]
          rw [show (∑ a, ∑ c, ∑ d, A i a * A k c * A l d
                  * (∑ p, ricArr R b p * R a p c d))
                = ∑ a, ∑ c, ∑ d, ∑ p,
                    A i a * A k c * A l d * (ricArr R b p * R a p c d) from by
              simp only [Finset.mul_sum]]
          rw [sum4_rot_B (fun e a c d => ricArr R b e * (A i a * A k c * A l d * R a e c d))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The third slot. -/
private theorem slotC_pt_B (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) k p * rot A R i j p l)
      = ∑ c, A k c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d
          * (∑ p, ricArr R c p * R a b p d)) := by
  have h1 : ∀ p, ricArr (rot A R) k p * rot A R i j p l
      = (∑ e, A p e * (∑ c, A k c * ricArr R c e))
        * (∑ c, A p c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)) := by
    intro p
    rw [Work.Diff.GE.react.ricArr_rot A hA R k p, Work.Diff.GE.react.rot_apply_factor3 A R i j p l]
  calc ∑ p, ricArr (rot A R) k p * rot A R i j p l
      = ∑ p, (∑ e, A p e * (∑ c, A k c * ricArr R c e))
            * (∑ c, A p c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A k c * ricArr R c e)
            * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d) :=
        Work.Diff.GE.react.contract_Avec A hA (fun e => ∑ c, A k c * ricArr R c e)
          (fun c => ∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)
    _ = ∑ c, A k c * (∑ e, ricArr R c e
            * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d)) := by
        rw [sum_mul_swap_B (fun c e => A k c * ricArr R c e)
              (fun e => ∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d)]
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = ∑ c, A k c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d
          * (∑ p, ricArr R c p * R a b p d)) := by
        apply Finset.sum_congr rfl; intro c _
        rw [show (∑ e, ricArr R c e * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d))
              = ∑ a, ∑ b, ∑ d, A i a * A j b * A l d
                  * (∑ p, ricArr R c p * R a b p d) from by
          rw [show (∑ e, ricArr R c e * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d))
                = ∑ e, ∑ a, ∑ b, ∑ d,
                    ricArr R c e * (A i a * A j b * A l d * R a b e d) from by
              simp only [Finset.mul_sum]]
          rw [show (∑ a, ∑ b, ∑ d, A i a * A j b * A l d
                  * (∑ p, ricArr R c p * R a b p d))
                = ∑ a, ∑ b, ∑ d, ∑ p,
                    A i a * A j b * A l d * (ricArr R c p * R a b p d) from by
              simp only [Finset.mul_sum]]
          rw [sum4_rot_B (fun e a b d => ricArr R c e * (A i a * A j b * A l d * R a b e d))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The fourth slot. -/
private theorem slotD_pt_B (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) l p * rot A R i j k p)
      = ∑ d, A l d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c
          * (∑ p, ricArr R d p * R a b c p)) := by
  have h1 : ∀ p, ricArr (rot A R) l p * rot A R i j k p
      = (∑ e, A p e * (∑ c, A l c * ricArr R c e))
        * (∑ d, A p d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)) := by
    intro p
    rw [Work.Diff.GE.react.ricArr_rot A hA R l p, Work.Diff.GE.react.rot_apply_factor4 A R i j k p]
  calc ∑ p, ricArr (rot A R) l p * rot A R i j k p
      = ∑ p, (∑ e, A p e * (∑ c, A l c * ricArr R c e))
            * (∑ d, A p d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A l c * ricArr R c e)
            * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e) :=
        Work.Diff.GE.react.contract_Avec A hA (fun e => ∑ c, A l c * ricArr R c e)
          (fun d => ∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)
    _ = ∑ d, A l d * (∑ e, ricArr R d e
            * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e)) := by
        rw [sum_mul_swap_B (fun c e => A l c * ricArr R c e)
              (fun e => ∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e)]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = ∑ d, A l d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c
          * (∑ p, ricArr R d p * R a b c p)) := by
        apply Finset.sum_congr rfl; intro d _
        rw [show (∑ e, ricArr R d e * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e))
              = ∑ a, ∑ b, ∑ c, A i a * A j b * A k c
                  * (∑ p, ricArr R d p * R a b c p) from by
          rw [show (∑ e, ricArr R d e * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e))
                = ∑ e, ∑ a, ∑ b, ∑ c,
                    ricArr R d e * (A i a * A j b * A k c * R a b c e) from by
              simp only [Finset.mul_sum]]
          rw [show (∑ a, ∑ b, ∑ c, A i a * A j b * A k c
                  * (∑ p, ricArr R d p * R a b c p))
                = ∑ a, ∑ b, ∑ c, ∑ p,
                    A i a * A j b * A k c * (ricArr R d p * R a b c p) from by
              simp only [Finset.mul_sum]]
          rw [sum4_rot_B (fun e a b c => ricArr R d e * (A i a * A j b * A k c * R a b c e))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-! ## The four slot lemmas (as `rot`-equivariance of the slot arrays) -/

/-- The first slot of `Xact` is `O(n)`-equivariant. -/
private theorem Xact_rot_slotA_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XA_B (rot A R) = rot A (XA_B R) := by
  intro A hA R
  ext i j k l
  rw [Work.Diff.GE.react.rot_apply_factor A (XA_B R) i j k l]
  exact slotA_pt_B A hA R i j k l

/-- The second slot of `Xact` is `O(n)`-equivariant. -/
private theorem Xact_rot_slotB_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XB_B (rot A R) = rot A (XB_B R) := by
  intro A hA R
  ext i j k l
  rw [Work.Diff.GE.react.rot_apply_factor2 A (XB_B R) i j k l]
  exact slotB_pt_B A hA R i j k l

/-- The third slot of `Xact` is `O(n)`-equivariant. -/
private theorem Xact_rot_slotC_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XC_B (rot A R) = rot A (XC_B R) := by
  intro A hA R
  ext i j k l
  rw [Work.Diff.GE.react.rot_apply_factor3 A (XC_B R) i j k l]
  exact slotC_pt_B A hA R i j k l

/-- The fourth slot of `Xact` is `O(n)`-equivariant. -/
private theorem Xact_rot_slotD_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XD_B (rot A R) = rot A (XD_B R) := by
  intro A hA R
  ext i j k l
  rw [Work.Diff.GE.react.rot_apply_factor4 A (XD_B R) i j k l]
  exact slotD_pt_B A hA R i j k l

/-! ## The target -/

theorem Xact_rot_B (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Submission.Diff.Alg.Curv4 n,
      Work.Diff.Evol.Xact (Submission.Diff.Alg.rot A R)
        = Submission.Diff.Alg.rot A (Work.Diff.Evol.Xact R) := by
  intro A hA R
  rw [Xact_eq_slots_B (R := rot A R), Xact_eq_slots_B (R := R)]
  rw [Xact_rot_slotA_B n A hA R, Xact_rot_slotB_B n A hA R, Xact_rot_slotC_B n A hA R,
    Xact_rot_slotD_B n A hA R]
  simp only [rot_add_B]

end Work.Diff.GE.EvolB
