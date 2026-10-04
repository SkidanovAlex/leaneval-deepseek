import Mathlib
import Submission.Work.Diff.GE.react.RotKit
import Submission.Work.Diff.GE.rot_contract

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of Hamilton's reaction term `Q` (`Work.Diff.GE.react.Q_rot`)

`Submission.Diff.Alg.rot A` is the action of an orthogonal change of frame `A` on curvature arrays
(`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`), and `Q` is Hamilton's
quadratic reaction term of the Ricci flow,
`Q R i j k l = ∑ p q (R i j p q * R k l p q + 2 R i p k q * R j p l q - 2 R i p l q * R j p k q)`.
Both are built from the Euclidean metric alone, hence commute: `Q (rot A R) = rot A (Q R)`.

The proof is index bookkeeping, and it is what makes the maximum principle / pinching sets of the
Ricci-flow proof `O(n)`-invariant.

* Split `Q` into its three double contractions (`qrot_Q_split`), each of which is a *contraction*
  of two copies of `R`;
* The first contraction has its contracted indices in the last two slots of both factors, so it is
  transported directly by the core identity `Work.Diff.GE.rot_contract` (column orthogonality of
  `A`, no algebraic hypothesis on `R`);
* In the second and third terms the two factors have their free index pairs in *different* slots.
  Swapping the middle two indices of `R` (`qrotSwapMid`) brings them to the standard pattern, and
  the resulting sums are re-indexed (`qrot_E2_eq_P2`, `qrot_E3_eq_P3`) by fourfold sum
  reorderings (`sum4_swap23`, `sum4_swap34` from `RotKit`).

The helper lemmas below live in this file (under `qrot_`-prefixed names) so that this module is
self-contained apart from the two sorry-free imports above.
-/

namespace Work.Diff.GE.react

open Finset Matrix
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## Splitting finite sums along `f + 2 * g - 2 * h` -/

/-- One-dimensional linearity splitting, used for `Q`'s three terms. -/
theorem qrot_sum_split1 {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ i, (f i + 2 * g i - 2 * h i)) = (∑ i, f i) + 2 * (∑ i, g i) - 2 * (∑ i, h i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Two-dimensional version. -/
theorem qrot_sum_split2 {ι κ : Type*} [Fintype ι] [Fintype κ] (f g h : ι → κ → ℝ) :
    (∑ i, ∑ j, (f i j + 2 * g i j - 2 * h i j))
      = (∑ i, ∑ j, f i j) + 2 * (∑ i, ∑ j, g i j) - 2 * (∑ i, ∑ j, h i j) := by
  have h1 : ∀ i, (∑ j, (f i j + 2 * g i j - 2 * h i j))
      = (∑ j, f i j) + 2 * (∑ j, g i j) - 2 * (∑ j, h i j) :=
    fun i => qrot_sum_split1 (f i) (g i) (h i)
  rw [show (∑ i, ∑ j, (f i j + 2 * g i j - 2 * h i j))
      = ∑ i, ((∑ j, f i j) + 2 * (∑ j, g i j) - 2 * (∑ j, h i j)) from
    Finset.sum_congr rfl fun i _ => h1 i]
  exact qrot_sum_split1 (fun i => ∑ j, f i j) (fun i => ∑ j, g i j) (fun i => ∑ j, h i j)

/-- Four-dimensional version. -/
theorem qrot_sum_split4 (f g h : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) + 2 * (∑ a, ∑ b, ∑ c, ∑ d, g a b c d)
        - 2 * (∑ a, ∑ b, ∑ c, ∑ d, h a b c d) := by
  have h1 : ∀ a b, (∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = (∑ c, ∑ d, f a b c d) + 2 * (∑ c, ∑ d, g a b c d) - 2 * (∑ c, ∑ d, h a b c d) :=
    fun a b => qrot_sum_split2 (f a b) (g a b) (h a b)
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = ∑ a, ∑ b, ((∑ c, ∑ d, f a b c d) + 2 * (∑ c, ∑ d, g a b c d)
          - 2 * (∑ c, ∑ d, h a b c d)) from by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    exact h1 a b]
  exact qrot_sum_split2 (fun a b => ∑ c, ∑ d, f a b c d) (fun a b => ∑ c, ∑ d, g a b c d)
    (fun a b => ∑ c, ∑ d, h a b c d)

/-! ## `Q` as three double contractions -/

/-- `Q`'s three terms as double contractions over its last index pair. -/
theorem qrot_Q_split (R : Curv4 n) (i j k l : Fin n) :
    Q R i j k l = (∑ p, ∑ q, R i j p q * R k l p q) + 2 * (∑ p, ∑ q, R i p k q * R j p l q)
      - 2 * (∑ p, ∑ q, R i p l q * R j p k q) := by
  have h : Q R i j k l = ∑ p, ∑ q, (R i j p q * R k l p q + 2 * (R i p k q * R j p l q)
      - 2 * (R i p l q * R j p k q)) := by
    simp only [Q]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [h]
  exact qrot_sum_split2 _ _ _

/-! ## Swapping the middle two slots of a 4-tensor -/

/-- `R` with its middle two indices exchanged. -/
def qrotSwapMid (R : Curv4 n) : Curv4 n := fun a b c d => R a c b d

/-- The middle-slot swap of `R` corresponds to swapping the 2nd and 3rd arguments of `rot A R`. -/
theorem qrot_rot_swapMid (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A (qrotSwapMid R) i j k l = rot A R i k j l := by
  simp only [rot, qrotSwapMid]
  rw [sum4_swap23 (fun u v w z => A i u * A j v * A k w * A l z * R u w v z)]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## Re-indexing the middle contractions into `Q`'s index pattern -/

/-- The contracted sum obtained from the rotated middle-slot pattern matches `Q`'s second term. -/
theorem qrot_E2_eq_P2 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A i a * A k b * A j c * A l d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A k b * A j c * A l d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A k c * A j b * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) :=
    sum4_swap23 (fun u v w z =>
      A i u * A k v * A j w * A l z * (∑ p, ∑ q, R u p v q * R w p z q))
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- The contracted sum obtained from the rotated middle-slot pattern matches `Q`'s third term. -/
theorem qrot_E3_eq_P3 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l b * A j c * A k d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p d q * R b p c q) := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l b * A j c * A k d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A l c * A j b * A k d *
          (∑ p, ∑ q, R a p c q * R b p d q) :=
    sum4_swap23 (fun u v w z =>
      A i u * A l v * A j w * A k z * (∑ p, ∑ q, R u p v q * R w p z q))
  have h2 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l c * A j b * A k d *
        (∑ p, ∑ q, R a p c q * R b p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A l d * A j b * A k c *
          (∑ p, ∑ q, R a p d q * R b p c q) :=
    sum4_swap34 (fun u v w z =>
      A i u * A l w * A j v * A k z * (∑ p, ∑ q, R u p w q * R v p z q))
  rw [h1.trans h2]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## The target -/

theorem Q_rot (n : ℕ) :
    ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      ∀ R : Submission.Diff.Alg.Curv4 n,
        Submission.Diff.Alg.Q (Submission.Diff.Alg.rot A R) =
          Submission.Diff.Alg.rot A (Submission.Diff.Alg.Q R) := by
  intro A hA R
  -- Core contraction identity, proved in `Submission/Work/Diff/GE/rot_contract.lean`.
  have hcontr : ∀ (φ ψ : Curv4 n) (i j k l : Fin n),
      (∑ p, ∑ q, rot A φ i j p q * rot A ψ k l p q)
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
            (∑ p, ∑ q, φ a b p q * ψ c d p q) :=
    fun φ ψ i j k l => rot_contract (n := n) A hA φ ψ i j k l
  funext i j k l
  have hT1 : (∑ p, ∑ q, rot A R i j p q * rot A R k l p q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a b p q * R c d p q) :=
    hcontr R R i j k l
  have hT2a : (∑ p, ∑ q, rot A R i p k q * rot A R j p l q)
      = ∑ p, ∑ q, rot A (qrotSwapMid R) i k p q * rot A (qrotSwapMid R) j l p q := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [← qrot_rot_swapMid A R i k p q, ← qrot_rot_swapMid A R j l p q]
  have hT2 : (∑ p, ∑ q, rot A R i p k q * rot A R j p l q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) := by
    rw [hT2a, hcontr (qrotSwapMid R) (qrotSwapMid R) i k j l]
    simp only [qrotSwapMid]
    exact qrot_E2_eq_P2 A R i j k l
  have hT3a : (∑ p, ∑ q, rot A R i p l q * rot A R j p k q)
      = ∑ p, ∑ q, rot A (qrotSwapMid R) i l p q * rot A (qrotSwapMid R) j k p q := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [← qrot_rot_swapMid A R i l p q, ← qrot_rot_swapMid A R j k p q]
  have hT3 : (∑ p, ∑ q, rot A R i p l q * rot A R j p k q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p d q * R b p c q) := by
    rw [hT3a, hcontr (qrotSwapMid R) (qrotSwapMid R) i l j k]
    simp only [qrotSwapMid]
    exact qrot_E3_eq_P3 A R i j k l
  have hQ : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * Q R a b c d)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          ((∑ p, ∑ q, R a b p q * R c d p q) + 2 * (∑ p, ∑ q, R a p c q * R b p d q)
            - 2 * (∑ p, ∑ q, R a p d q * R b p c q)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    rw [qrot_Q_split R a b c d]
  have hQ2 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
        ((∑ p, ∑ q, R a b p q * R c d p q) + 2 * (∑ p, ∑ q, R a p c q * R b p d q)
          - 2 * (∑ p, ∑ q, R a p d q * R b p c q)))
      = (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
            (∑ p, ∑ q, R a b p q * R c d p q))
        + 2 * (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
            (∑ p, ∑ q, R a p c q * R b p d q))
        - 2 * (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
            (∑ p, ∑ q, R a p d q * R b p c q)) := by
    rw [show (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          ((∑ p, ∑ q, R a b p q * R c d p q) + 2 * (∑ p, ∑ q, R a p c q * R b p d q)
            - 2 * (∑ p, ∑ q, R a p d q * R b p c q)))
        = ∑ a, ∑ b, ∑ c, ∑ d,
            (A i a * A j b * A k c * A l d * (∑ p, ∑ q, R a b p q * R c d p q)
              + 2 * (A i a * A j b * A k c * A l d * (∑ p, ∑ q, R a p c q * R b p d q))
              - 2 * (A i a * A j b * A k c * A l d * (∑ p, ∑ q, R a p d q * R b p c q))) from by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      ring]
    exact qrot_sum_split4 _ _ _
  rw [qrot_Q_split (rot A R) i j k l, hT1, hT2, hT3,
    show rot A (Q R) i j k l
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * Q R a b c d from rfl,
    hQ, hQ2]

end Work.Diff.GE.react
