import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.GE.rot_contract

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of Hamilton's quadratic curvature term `Q`

Hamilton's reaction term `Q` (`Submission.Diff.Alg.Q`) is built from the Euclidean metric by
contracting two curvature tensors, so it commutes with the change of orthonormal frame `rot A`
(`A` orthogonal).  This is the identity `Q (rot A R) = rot A (Q R)` used to make the maximum
principle and the pinching sets of the Ricci-flow proof `O(n)`-invariant.

The proof is index bookkeeping.  Write `Q`'s three terms as double contractions and expand:

* `Q R i j k l = (∑ p q, R i j p q * R k l p q) + 2 * (∑ p q, R i p k q * R j p l q)
    - 2 * (∑ p q, R i p l q * R j p k q)` (`rotQ_Q_split`);
* the first contraction is transported by `rot` thanks to the general lemma
  `Work.Diff.GE.rot_contract` (column orthogonality `∑ p, A p c * A p c' = δ` of `A`, packaged as
  `rotQ_sum_orthogonal`, contracts the two `p`-sums);
* the second and third contractions have their two free index pairs in *different slots* of `R`;
  swapping the middle two indices of `R` (`rotQ_swapMid`) turns them into the standard pattern, and
  the resulting sums are re-indexed (`rotQ_E2_eq_P2`, `rotQ_E3_eq_P3`) using the four-fold sum
  reorderings `sum4_swap23`, `sum4_swap34` of `Work.Diff.Alg.Q2P`.
-/

namespace Work.Diff.GE

open Finset Matrix
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## Column orthogonality of an orthogonal matrix -/

/-- The columns of an orthogonal matrix are orthonormal: `∑ p, A p c * A p c' = δ_{c c'}`. -/
theorem rotQ_sum_orthogonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (c c' : Fin n) :
    ∑ p, A p c * A p c' = if c = c' then 1 else 0 := by
  have h : Aᵀ * A = 1 := Iff.mp (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)) hA
  have h1 : (Aᵀ * A) c c' = ∑ p, A p c * A p c' := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.transpose_apply]
  rw [← h1, h, Matrix.one_apply]

/-! ## Splitting finite sums along `f + 2 * g - 2 * h` -/

/-- One-dimensional version of the linearity splitting used for `Q`'s three terms. -/
theorem rotQ_sum_split1 {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ i, (f i + 2 * g i - 2 * h i)) = (∑ i, f i) + 2 * (∑ i, g i) - 2 * (∑ i, h i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Two-dimensional version. -/
theorem rotQ_sum_split2 {ι κ : Type*} [Fintype ι] [Fintype κ] (f g h : ι → κ → ℝ) :
    (∑ i, ∑ j, (f i j + 2 * g i j - 2 * h i j))
      = (∑ i, ∑ j, f i j) + 2 * (∑ i, ∑ j, g i j) - 2 * (∑ i, ∑ j, h i j) := by
  have h1 : ∀ i, (∑ j, (f i j + 2 * g i j - 2 * h i j))
      = (∑ j, f i j) + 2 * (∑ j, g i j) - 2 * (∑ j, h i j) :=
    fun i => rotQ_sum_split1 (f i) (g i) (h i)
  rw [show (∑ i, ∑ j, (f i j + 2 * g i j - 2 * h i j))
      = ∑ i, ((∑ j, f i j) + 2 * (∑ j, g i j) - 2 * (∑ j, h i j)) from
    Finset.sum_congr rfl fun i _ => h1 i]
  exact rotQ_sum_split1 (fun i => ∑ j, f i j) (fun i => ∑ j, g i j) (fun i => ∑ j, h i j)

/-- Four-dimensional version. -/
theorem rotQ_sum_split4 (f g h : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) + 2 * (∑ a, ∑ b, ∑ c, ∑ d, g a b c d)
        - 2 * (∑ a, ∑ b, ∑ c, ∑ d, h a b c d) := by
  have h1 : ∀ a b, (∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = (∑ c, ∑ d, f a b c d) + 2 * (∑ c, ∑ d, g a b c d) - 2 * (∑ c, ∑ d, h a b c d) :=
    fun a b => rotQ_sum_split2 (f a b) (g a b) (h a b)
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, (f a b c d + 2 * g a b c d - 2 * h a b c d))
      = ∑ a, ∑ b, ((∑ c, ∑ d, f a b c d) + 2 * (∑ c, ∑ d, g a b c d)
          - 2 * (∑ c, ∑ d, h a b c d)) from by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    exact h1 a b]
  exact rotQ_sum_split2 (fun a b => ∑ c, ∑ d, f a b c d) (fun a b => ∑ c, ∑ d, g a b c d)
    (fun a b => ∑ c, ∑ d, h a b c d)

/-- `Q`'s three terms as double contractions over its last index pair. -/
theorem rotQ_Q_split (R : Curv4 n) (i j k l : Fin n) :
    Q R i j k l = (∑ p, ∑ q, R i j p q * R k l p q) + 2 * (∑ p, ∑ q, R i p k q * R j p l q)
      - 2 * (∑ p, ∑ q, R i p l q * R j p k q) := by
  have h : Q R i j k l = ∑ p, ∑ q, (R i j p q * R k l p q + 2 * (R i p k q * R j p l q)
      - 2 * (R i p l q * R j p k q)) := by
    simp only [Q]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [h]
  exact rotQ_sum_split2 _ _ _

/-! ## Swapping the middle two slots of a 4-tensor -/

/-- `R` with its middle two indices exchanged. -/
def rotQ_swapMid (R : Curv4 n) : Curv4 n := fun a b c d => R a c b d

/-- `rot` is `O(n)`-equivariant; the middle-slot swap of `R` corresponds to swapping the 2nd and
3rd arguments of `rot A R`. -/
theorem rotQ_rot_swapMid (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A (rotQ_swapMid R) i j k l = rot A R i k j l := by
  simp only [rot, rotQ_swapMid]
  rw [Work.Diff.Alg.Q2P.sum4_swap23
    (fun u v w z => A i u * A j v * A k w * A l z * R u w v z)]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## Re-indexing the middle contraction into `Q`'s index pattern -/

/-- The contracted sum obtained from the rotated middle-slot pattern matches `Q`'s second term. -/
theorem rotQ_E2_eq_P2 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A i a * A k b * A j c * A l d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A k b * A j c * A l d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A k c * A j b * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) :=
    Work.Diff.Alg.Q2P.sum4_swap23 (fun u v w z =>
      A i u * A k v * A j w * A l z * (∑ p, ∑ q, R u p v q * R w p z q))
  rw [h1]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- The contracted sum obtained from the rotated middle-slot pattern matches `Q`'s third term. -/
theorem rotQ_E3_eq_P3 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l b * A j c * A k d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p d q * R b p c q) := by
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l b * A j c * A k d *
        (∑ p, ∑ q, R a p b q * R c p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A l c * A j b * A k d *
          (∑ p, ∑ q, R a p c q * R b p d q) :=
    Work.Diff.Alg.Q2P.sum4_swap23 (fun u v w z =>
      A i u * A l v * A j w * A k z * (∑ p, ∑ q, R u p v q * R w p z q))
  have h2 : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A l c * A j b * A k d *
        (∑ p, ∑ q, R a p c q * R b p d q))
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A l d * A j b * A k c *
          (∑ p, ∑ q, R a p d q * R b p c q) :=
    Work.Diff.Alg.Q2P.sum4_swap34 (fun u v w z =>
      A i u * A l w * A j v * A k z * (∑ p, ∑ q, R u p w q * R v p z q))
  rw [h1.trans h2]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- The three contracted sums appearing in `Q`'s definition, for the rotated tensor `rot A R`. -/
theorem rot_Q {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Submission.Diff.Alg.Q (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (Submission.Diff.Alg.Q R) := by
  -- General contraction identity for `rot` (proved in `Submission/Work/Diff/GE/rot_contract.lean`).
  have hcontr : ∀ (φ ψ : Curv4 n) (i j k l : Fin n),
      (∑ p, ∑ q, rot A φ i j p q * rot A ψ k l p q)
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
            (∑ p, ∑ q, φ a b p q * ψ c d p q) := by
    intro φ ψ i j k l
    exact rot_contract A hA φ ψ i j k l

  funext i j k l
  -- the first contraction: straight from `hcontr`
  have hT1 : (∑ p, ∑ q, rot A R i j p q * rot A R k l p q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a b p q * R c d p q) :=
    hcontr R R i j k l
  -- the second contraction: move to the middle-slot pattern and re-index
  have hT2a : (∑ p, ∑ q, rot A R i p k q * rot A R j p l q)
      = ∑ p, ∑ q, rot A (rotQ_swapMid R) i k p q * rot A (rotQ_swapMid R) j l p q := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [← rotQ_rot_swapMid A R i k p q, ← rotQ_rot_swapMid A R j l p q]
  have hT2 : (∑ p, ∑ q, rot A R i p k q * rot A R j p l q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p c q * R b p d q) := by
    rw [hT2a, hcontr (rotQ_swapMid R) (rotQ_swapMid R) i k j l]
    simp only [rotQ_swapMid]
    exact rotQ_E2_eq_P2 A R i j k l
  -- the third contraction
  have hT3a : (∑ p, ∑ q, rot A R i p l q * rot A R j p k q)
      = ∑ p, ∑ q, rot A (rotQ_swapMid R) i l p q * rot A (rotQ_swapMid R) j k p q := by
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    rw [← rotQ_rot_swapMid A R i l p q, ← rotQ_rot_swapMid A R j k p q]
  have hT3 : (∑ p, ∑ q, rot A R i p l q * rot A R j p k q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, R a p d q * R b p c q) := by
    rw [hT3a, hcontr (rotQ_swapMid R) (rotQ_swapMid R) i l j k]
    simp only [rotQ_swapMid]
    exact rotQ_E3_eq_P3 A R i j k l
  -- the right-hand side: expand `rot A` applied to the three pieces of `Q R`
  have hQ : (∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * Q R a b c d)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          ((∑ p, ∑ q, R a b p q * R c d p q) + 2 * (∑ p, ∑ q, R a p c q * R b p d q)
            - 2 * (∑ p, ∑ q, R a p d q * R b p c q)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    rw [rotQ_Q_split R a b c d]
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
    exact rotQ_sum_split4 _ _ _
  rw [rotQ_Q_split (rot A R) i j k l, hT1, hT2, hT3,
    show rot A (Q R) i j k l
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * Q R a b c d from rfl,
    hQ, hQ2]

end Work.Diff.GE
