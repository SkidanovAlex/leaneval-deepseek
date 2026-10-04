import Mathlib
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.GE.react.RotKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of the Uhlenbeck correction `Xact` (`Work.Diff.GE.react.Xact_rot_clean`)

`Work.Diff.Evol.Xact` is the Uhlenbeck-frame correction of the curvature evolution of a Ricci flow:
in fixed vectors the frame motion contributes the four Ricci-action terms
`Xact R i j k l = ∑ p (ricArr R i p * R p j k l + ricArr R j p * R i p k l
                       + ricArr R k p * R i j p l + ricArr R l p * R i j k p)`
(`Work.Diff.Evol.Calc`), where `ricArr R i p = ∑ a, R a i a p` is the Ricci contraction.

`Submission.Diff.Alg.rot A` is the action of an orthogonal change of frame `A` on curvature
arrays, `rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`.  Everything is
built from the Euclidean metric alone, so `Xact` commutes with that action:

  `Xact (rot A R) = rot A (Xact R)`  for every `A ∈ O(n)` and every `R : Curv4 n`.

This is the `Xact` half of the `O(n)`-equivariance of the reaction map `rmReact = Q - Xact`
(see `Submission/Work/Diff/GE/react/rmReact_rot.lean` and `Q_rot.lean` for the `Q` half); it is
what makes the maximum principle and the pinching sets of the Ricci-flow proof `O(n)`-invariant.

## Route

`Xact` is a sum of four *single-index contractions* `∑ p ricArr R ? p * R … p …`.  Both factors
have the contracted index `p` in the same slot, so the contraction is transported by the
orthogonality of `A` (`Work.Diff.GE.react.contract_Avec`, i.e. `∑ p (∑ e A p e u e)(∑ a A p a v a)
= ∑ e u e v e`) after the two structural inputs

* `ricArr_rot` (`RotKit`): `ricArr (rot A R) i p = ∑ e A p e * (∑ c A i c * ricArr R c e)`,
  i.e. the Ricci contraction transforms as a `(0,2)`-tensor;
* `rot_apply_factor{,2,3,4}` (`RotKit`): the definition of `rot`, with the summation slot of the
  contracted index `p` factored out of the `A p ·` factor.

The remaining bookkeeping is elementary: after `contract_Avec` one has to commute the two
summations (`sum_mul_swap`) and to move the `p`-sum out of the three slots that carry the
`A`-entries (`sum4_rot`, a rotation of a fourfold sum, proved from `sum4_swap12/23/34`).  The four
"slots" of `Xact` are handled separately by `slotA_pt … slotD_pt` (with `XA, XB, XC, XD` the four
slot arrays) and reassembled by the additivity `rot_add` of `rot`.

The two delegated siblings `Submission/Work/Diff/GE/react/Xact_slot{A,B}.lean` state the first two
slot lemmas in the `rot A`-normal form (no `Xact`); the slot lemmas below are purely pointwise and
prove the same content.
-/

namespace Work.Diff.GE.react

open Finset Matrix
open Submission.Diff.Alg
open Work.Diff.Evol

variable {n : ℕ}

/-! ## Two elementary reorderings and additivity of `rot` -/

/-- Rotate a fourfold sum: the outermost summation index goes to the back. -/
theorem sum4_rot (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [sum4_swap12, sum4_swap23, sum4_swap34]

/-- The two summations of a product `(∑ c, G c e) * W e` commute. -/
theorem sum_mul_swap (G : Fin n → Fin n → ℝ) (W : Fin n → ℝ) :
    (∑ e, (∑ c, G c e) * W e) = ∑ c, ∑ e, G c e * W e := by
  rw [show (∑ e, (∑ c, G c e) * W e) = ∑ e, ∑ c, G c e * W e from by
      apply Finset.sum_congr rfl; intro e _
      rw [Finset.sum_mul]]
  exact Finset.sum_comm

/-- `rot A` is additive in the tensor argument. -/
theorem rot_add (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S + T) = rot A S + rot A T := by
  ext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## The four Ricci-action slots of `Xact` -/

/-- The first Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R i p * R p j k l`. -/
noncomputable def XA (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R i p * R p j k l

/-- The second Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R j p * R i p k l`. -/
noncomputable def XB (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R j p * R i p k l

/-- The third Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R k p * R i j p l`. -/
noncomputable def XC (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R k p * R i j p l

/-- The fourth Ricci-action slot of `Xact`: `(i j k l) ↦ ∑ p, ricArr R l p * R i j k p`. -/
noncomputable def XD (R : Curv4 n) : Curv4 n := fun i j k l => ∑ p, ricArr R l p * R i j k p

/-- `Xact` is the sum of its four Ricci-action slots. -/
theorem Xact_eq_slots (R : Curv4 n) : Xact R = XA R + XB R + XC R + XD R := by
  ext i j k l
  simp only [XA, XB, XC, XD, Xact, Pi.add_apply, Finset.sum_add_distrib]

/-! ## The four slot lemmas (pointwise) -/

/-- The first slot: `∑ p, ricArr (rot A R) i p * rot A R p j k l` is the `p`-contraction of the
`(0,2)`-tensor `A · ricArr R · Aᵀ` with the suitably `rot`-transformed curvature, as produced by
`rot_apply_factor`. -/
theorem slotA_pt (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) i p * rot A R p j k l)
      = ∑ a, A i a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d
          * (∑ p, ricArr R a p * R p b c d)) := by
  have h1 : ∀ p, ricArr (rot A R) i p * rot A R p j k l
      = (∑ e, A p e * (∑ c, A i c * ricArr R c e))
        * (∑ a, A p a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)) := by
    intro p
    rw [ricArr_rot A hA R i p, rot_apply_factor A R p j k l]
  calc ∑ p, ricArr (rot A R) i p * rot A R p j k l
      = ∑ p, (∑ e, A p e * (∑ c, A i c * ricArr R c e))
            * (∑ a, A p a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A i c * ricArr R c e)
            * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R e b c d) :=
        contract_Avec A hA (fun e => ∑ c, A i c * ricArr R c e)
          (fun a => ∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d)
    _ = ∑ c, A i c * (∑ e, ricArr R c e
            * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R e b c d)) := by
        rw [sum_mul_swap (fun c e => A i c * ricArr R c e)
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
          rw [sum4_rot (fun e b c' d => ricArr R c e * (A j b * A k c' * A l d * R e b c' d))]
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c' _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The second slot. -/
theorem slotB_pt (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) j p * rot A R i p k l)
      = ∑ b, A j b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d
          * (∑ p, ricArr R b p * R a p c d)) := by
  have h1 : ∀ p, ricArr (rot A R) j p * rot A R i p k l
      = (∑ e, A p e * (∑ c, A j c * ricArr R c e))
        * (∑ b, A p b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)) := by
    intro p
    rw [ricArr_rot A hA R j p, rot_apply_factor2 A R i p k l]
  calc ∑ p, ricArr (rot A R) j p * rot A R i p k l
      = ∑ p, (∑ e, A p e * (∑ c, A j c * ricArr R c e))
            * (∑ b, A p b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A j c * ricArr R c e)
            * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d) :=
        contract_Avec A hA (fun e => ∑ c, A j c * ricArr R c e)
          (fun b => ∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d)
    _ = ∑ b, A j b * (∑ e, ricArr R b e
            * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a e c d)) := by
        rw [sum_mul_swap (fun c e => A j c * ricArr R c e)
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
          rw [sum4_rot (fun e a c d => ricArr R b e * (A i a * A k c * A l d * R a e c d))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The third slot. -/
theorem slotC_pt (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) k p * rot A R i j p l)
      = ∑ c, A k c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d
          * (∑ p, ricArr R c p * R a b p d)) := by
  have h1 : ∀ p, ricArr (rot A R) k p * rot A R i j p l
      = (∑ e, A p e * (∑ c, A k c * ricArr R c e))
        * (∑ c, A p c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)) := by
    intro p
    rw [ricArr_rot A hA R k p, rot_apply_factor3 A R i j p l]
  calc ∑ p, ricArr (rot A R) k p * rot A R i j p l
      = ∑ p, (∑ e, A p e * (∑ c, A k c * ricArr R c e))
            * (∑ c, A p c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A k c * ricArr R c e)
            * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d) :=
        contract_Avec A hA (fun e => ∑ c, A k c * ricArr R c e)
          (fun c => ∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d)
    _ = ∑ c, A k c * (∑ e, ricArr R c e
            * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b e d)) := by
        rw [sum_mul_swap (fun c e => A k c * ricArr R c e)
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
          rw [sum4_rot (fun e a b d => ricArr R c e * (A i a * A j b * A l d * R a b e d))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro d _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-- The fourth slot. -/
theorem slotD_pt (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i j k l : Fin n) :
    (∑ p, ricArr (rot A R) l p * rot A R i j k p)
      = ∑ d, A l d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c
          * (∑ p, ricArr R d p * R a b c p)) := by
  have h1 : ∀ p, ricArr (rot A R) l p * rot A R i j k p
      = (∑ e, A p e * (∑ c, A l c * ricArr R c e))
        * (∑ d, A p d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)) := by
    intro p
    rw [ricArr_rot A hA R l p, rot_apply_factor4 A R i j k p]
  calc ∑ p, ricArr (rot A R) l p * rot A R i j k p
      = ∑ p, (∑ e, A p e * (∑ c, A l c * ricArr R c e))
            * (∑ d, A p d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)) :=
        Finset.sum_congr rfl fun p _ => h1 p
    _ = ∑ e, (∑ c, A l c * ricArr R c e)
            * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e) :=
        contract_Avec A hA (fun e => ∑ c, A l c * ricArr R c e)
          (fun d => ∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d)
    _ = ∑ d, A l d * (∑ e, ricArr R d e
            * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c e)) := by
        rw [sum_mul_swap (fun c e => A l c * ricArr R c e)
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
          rw [sum4_rot (fun e a b c => ricArr R d e * (A i a * A j b * A k c * R a b c e))]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro p _
          ring]

/-! ## The four slot lemmas (as `rot`-equivariance of the slot arrays) -/

/-- The first slot of `Xact` is `O(n)`-equivariant. -/
theorem Xact_rot_slotA (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XA (rot A R) = rot A (XA R) := by
  intro A hA R
  ext i j k l
  rw [rot_apply_factor A (XA R) i j k l]
  exact slotA_pt A hA R i j k l

/-- The second slot of `Xact` is `O(n)`-equivariant. -/
theorem Xact_rot_slotB (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XB (rot A R) = rot A (XB R) := by
  intro A hA R
  ext i j k l
  rw [rot_apply_factor2 A (XB R) i j k l]
  exact slotB_pt A hA R i j k l

/-- The third slot of `Xact` is `O(n)`-equivariant. -/
theorem Xact_rot_slotC (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XC (rot A R) = rot A (XC R) := by
  intro A hA R
  ext i j k l
  rw [rot_apply_factor3 A (XC R) i j k l]
  exact slotC_pt A hA R i j k l

/-- The fourth slot of `Xact` is `O(n)`-equivariant. -/
theorem Xact_rot_slotD (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Curv4 n,
      XD (rot A R) = rot A (XD R) := by
  intro A hA R
  ext i j k l
  rw [rot_apply_factor4 A (XD R) i j k l]
  exact slotD_pt A hA R i j k l

/-! ## The target -/

theorem Xact_rot_clean (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R : Submission.Diff.Alg.Curv4 n,
      Work.Diff.Evol.Xact (Submission.Diff.Alg.rot A R)
        = Submission.Diff.Alg.rot A (Work.Diff.Evol.Xact R) := by
  intro A hA R
  rw [Xact_eq_slots (R := rot A R), Xact_eq_slots (R := R)]
  rw [Xact_rot_slotA n A hA R, Xact_rot_slotB n A hA R, Xact_rot_slotC n A hA R,
    Xact_rot_slotD n A hA R]
  simp only [rot_add]

end Work.Diff.GE.react
