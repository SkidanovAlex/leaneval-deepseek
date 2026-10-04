import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.scal_rot_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar curvature contraction `N2` under a change of frame

For an invertible matrix `A` and any `R : Curv4 n`, the contraction

`N2 (A * Aᵀ) (rot A R) = ∑ i a j b (A Aᵀ)⁻¹ i a (A Aᵀ)⁻¹ j b (rot A R) i j a b`

is the scalar curvature of `R` in the frame `e'_i = ∑_a A i a e_a` (whose Gram matrix is the
`symmetric positive definite `A Aᵀ`), so it equals `scalAlg R`.

The proof replaces the inverse Gram matrix by `Bᵀ * B`, `B = A⁻¹` (`A Aᵀ` invertible since `det A`
is a unit), and then uses the matrix identity of `Work.Diff.GE.scal_rot_defs`:

`Dc N (rot A R) = Dc (Aᵀ * N * A) R`   (`Dc_rot`),

which for `N = Bᵀ * B` reads `Dc (Bᵀ * B) (rot A R) = Dc ((B * A)ᵀ * (B * A)) R = Dc 1 R`, and
`Dc 1 R = scalAlg R` (`Dc_one`).  Both are pure finite-sum identities; the only tool needed is the
elementary reordering of multiple finite sums (`swap1_4`, `swap2_4`, `factor_sum4`).
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace ScalRotAux

/-! ### Elementary reorderings of finite sums over a common finite index type -/

/-- A single sum may be moved in front of four nested sums. -/
lemma swap1_4 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ a, ∑ b, ∑ c, ∑ d, g i a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, g i a b c d := by
  rw [Finset.sum_comm]; congr 1 with a
  rw [Finset.sum_comm]; congr 1 with b
  rw [Finset.sum_comm]; congr 1 with c
  rw [Finset.sum_comm]

/-- A block of two nested sums may be moved in front of four nested sums. -/
lemma swap2_4 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ i', ∑ k1, ∑ k2, ∑ k3, ∑ k4, f i i' k1 k2 k3 k4)
      = ∑ k1, ∑ k2, ∑ k3, ∑ k4, ∑ i, ∑ i', f i i' k1 k2 k3 k4 := by
  have h1 : (∑ i, ∑ i', ∑ k1, ∑ k2, ∑ k3, ∑ k4, f i i' k1 k2 k3 k4)
          = ∑ i, ∑ k1, ∑ k2, ∑ k3, ∑ k4, ∑ i', f i i' k1 k2 k3 k4 := by
    refine Finset.sum_congr rfl fun i _ => swap1_4 (fun i' k1 k2 k3 k4 => f i i' k1 k2 k3 k4)
  rw [h1]
  exact swap1_4 (fun i k1 k2 k3 k4 => ∑ i', f i i' k1 k2 k3 k4)

/-- A constant factor may be pulled out of four nested sums. -/
lemma sum4_mul_const {ι : Type*} [Fintype ι] (p q : ι → ι → ℝ) (r : ℝ) :
    (∑ i, ∑ a, ∑ j, ∑ b, p i a * q j b) * r = ∑ i, ∑ a, ∑ j, ∑ b, p i a * q j b * r := by
  rw [Finset.sum_mul]; congr 1 with i
  rw [Finset.sum_mul]; congr 1 with a
  rw [Finset.sum_mul]; congr 1 with j
  rw [Finset.sum_mul]

/-- A product of two double sums is the four-fold sum of the products. -/
lemma sum4_mul_sum4 {ι : Type*} [Fintype ι] (p q : ι → ι → ℝ) :
    (∑ i, ∑ a, p i a) * (∑ j, ∑ b, q j b) = ∑ i, ∑ a, ∑ j, ∑ b, p i a * q j b := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]

/-- A four-fold sum of a product of two independent factors and a constant is the product of the
partial sums. -/
lemma factor_sum4 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) (p q : ι → ι → ℝ) (r : ℝ)
    (h : ∀ i a j b, f i a j b = p i a * q j b * r) :
    (∑ i, ∑ a, ∑ j, ∑ b, f i a j b) = (∑ i, ∑ a, p i a) * (∑ j, ∑ b, q j b) * r := by
  have h1 : (∑ i, ∑ a, ∑ j, ∑ b, f i a j b) = ∑ i, ∑ a, ∑ j, ∑ b, p i a * q j b * r := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => h i a j b
  rw [h1, ← sum4_mul_const p q r, ← sum4_mul_sum4 p q]

/-- The entries of the transported matrix `Aᵀ * N * A` as a contraction. -/
lemma entry_eq {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℝ) (c e : Fin n) :
    (∑ i, ∑ a, N i a * A i c * A a e) = (Matrix.transpose A * N * A) c e := by
  rw [show (Matrix.transpose A * N * A) c e
      = ∑ j, (∑ j_1, A j_1 c * N j_1 j) * A j e from by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end ScalRotAux

/-! ### The two contraction identities -/

/-- `Dc` is invariant under a change of frame, with the matrix transported by `Aᵀ (·) A`. -/
theorem Dc_rot {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    Dc N (rot A R) = Dc (Matrix.transpose A * N * A) R := by
  calc Dc N (rot A R)
      = ∑ i, ∑ a, ∑ j, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
          N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f) := by
        simp only [Dc, rot, Finset.mul_sum]
    _ = ∑ c, ∑ d, ∑ e, ∑ f, ∑ i, ∑ a, ∑ j, ∑ b,
          N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f) := by
        have h1 : (∑ i, ∑ a, ∑ j, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
              N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f))
            = ∑ i, ∑ a, ∑ c, ∑ d, ∑ e, ∑ f, ∑ j, ∑ b,
              N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
          exact ScalRotAux.swap2_4 (fun j b c d e f =>
            N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f))
        rw [h1]
        exact ScalRotAux.swap2_4 (fun i a c d e f => ∑ j, ∑ b,
          N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f))
    _ = ∑ c, ∑ d, ∑ e, ∑ f, (∑ i, ∑ a, N i a * A i c * A a e) *
          (∑ j, ∑ b, N j b * A j d * A b f) * R c d e f := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
        exact ScalRotAux.factor_sum4 (fun i a j b =>
            N i a * N j b * (A i c * A j d * A a e * A b f * R c d e f))
          (fun i a => N i a * A i c * A a e) (fun j b => N j b * A j d * A b f)
          (R c d e f) (fun i a j b => by ring)
    _ = ∑ c, ∑ d, ∑ e, ∑ f, (Matrix.transpose A * N * A) c e *
          (Matrix.transpose A * N * A) d f * R c d e f := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
        rw [← ScalRotAux.entry_eq A N c e, ← ScalRotAux.entry_eq A N d f]
    _ = Dc (Matrix.transpose A * N * A) R := by
        rw [Dc]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]

/-- `Dc` with the identity matrix is the scalar curvature. -/
theorem Dc_one {n : ℕ} (R : Curv4 n) :
    Dc (1 : Matrix (Fin n) (Fin n) ℝ) R = scalAlg R := by
  simp only [Dc, scalAlg, Matrix.one_apply]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s3 _ => ?_
  simp only [ite_mul, one_mul, zero_mul, mul_ite]
  simp

/-- The contraction `N2 (A * Aᵀ)` of the rotated tensor is the scalar curvature. -/
theorem scal_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (R : Curv4 n) :
    N2 (A * Matrix.transpose A) (rot A R) = scalAlg R := by
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hG : (A * Matrix.transpose A)⁻¹ = Matrix.transpose A⁻¹ * A⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹ A (Matrix.transpose A), hBA, Matrix.one_mul,
      ← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have hM : Matrix.transpose A * (Matrix.transpose A⁻¹ * A⁻¹) * A = 1 := by
    have h1 : Matrix.transpose A * Matrix.transpose A⁻¹ = 1 := by
      rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
    calc Matrix.transpose A * (Matrix.transpose A⁻¹ * A⁻¹) * A
        = (Matrix.transpose A * Matrix.transpose A⁻¹) * (A⁻¹ * A) := by noncomm_ring
      _ = 1 := by rw [h1, hBA, Matrix.one_mul]
  rw [N2_eq_Dc, hG, Dc_rot A (Matrix.transpose A⁻¹ * A⁻¹) R, hM, Dc_one]

end Work.Diff.GE
