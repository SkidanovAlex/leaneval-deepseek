import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonal invariance of the full contraction of a curvature tensor

For a matrix `A` acting on `ℝⁿ` by `e'_i = ∑_a A i a e_a` the induced action on 4-index tensors is
`rot A R i j k l = ∑ A i a A j b A k c A l d R a b c d` (`Submission.Diff.Alg.rot`).

This module proves that for `A ∈ O(n)` the completely contracted form `R4` is invariant:
`∑ᵢⱼₖₗ (Aα)ᵢ (Aβ)ⱼ (Aγ)ₖ (Aδ)ₗ (rot A R)ᵢⱼₖₗ = ∑_{abcd} α_a β_b γ_c δ_d R_{abcd}`.

The proof is a two-slot contraction.  Contracting the last two slots of `rot A R i j k l` against
`Aγ`, `Aδ` reduces (by the orthogonality relation `∑ᵢ A i a A i a' = δ_{a a'}`) to the two-slot
contraction of `γ`, `δ`, and the resulting two-slot expression is again contracted against `Aα`,
`Aβ` the same way.
-/

namespace Work.Diff.Alg

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Entry form of the orthogonality relation `∑ᵢ A i a A i a' = δ_{a a'}`. -/
theorem orth_entry {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (a a' : Fin n) : ∑ i, A i a * A i a' = if a = a' then 1 else 0 := by
  have hAA : A.transpose * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hA
  have h := congrFun (congrFun hAA a) a'
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- One-slot contraction: a rotated vector pairs with the rotation matrix to give back the original
vector, `∑ᵢ (A u)ᵢ A i a = u a`. -/
theorem collapse_vec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (u : Fin n → ℝ) (a : Fin n) : ∑ i, (A.mulVec u) i * A i a = u a := by
  have horth := orth_entry hA
  calc ∑ i, (A.mulVec u) i * A i a
      = ∑ i, (∑ b, A i b * u b) * A i a := rfl
    _ = ∑ i, ∑ b, A i b * u b * A i a := by simp only [Finset.sum_mul]
    _ = ∑ b, ∑ i, A i b * u b * A i a := by rw [Finset.sum_comm]
    _ = ∑ b, (∑ i, A i b * A i a) * u b := by
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro i _
          ring
    _ = ∑ b, (if b = a then 1 else 0) * u b := by simp only [horth]
    _ = u a := by
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq']
          simp

/-- Factor a constant out of a two-fold sum of products. -/
theorem sum2_mul (f g : Fin n → ℝ) (c : ℝ) :
    (∑ i, ∑ j, f i * g j * c) = (∑ i, f i) * (∑ j, g j) * c := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Push a constant inside a two-fold sum. -/
theorem mul_sum2 (x : ℝ) (G : Fin n → Fin n → ℝ) :
    x * (∑ a, ∑ b, G a b) = ∑ a, ∑ b, x * G a b := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]

/-- Two-slot contraction: the pairing of `u ⊗ v` with a matrix `M` is invariant under an orthogonal
change of frame. -/
theorem collapse2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (M : Fin n → Fin n → ℝ) (u v : Fin n → ℝ) :
    (∑ i, ∑ j, (A.mulVec u) i * (A.mulVec v) j * (∑ a, ∑ b, A i a * A j b * M a b))
      = ∑ a, ∑ b, u a * v b * M a b := by
  have hu : ∀ a, ∑ i, (A.mulVec u) i * A i a = u a := collapse_vec hA u
  have hv : ∀ b, ∑ j, (A.mulVec v) j * A j b = v b := collapse_vec hA v
  calc ∑ i, ∑ j, (A.mulVec u) i * (A.mulVec v) j * (∑ a, ∑ b, A i a * A j b * M a b)
      = ∑ i, ∑ j, ∑ a, ∑ b,
          ((A.mulVec u) i * A i a) * ((A.mulVec v) j * A j b) * M a b := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [mul_sum2]
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          ring
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
          ((A.mulVec u) i * A i a) * ((A.mulVec v) j * A j b) * M a b :=
          Q2P.block_swap (fun i j a b => ((A.mulVec u) i * A i a) * ((A.mulVec v) j * A j b) * M a b)
    _ = ∑ a, ∑ b, (∑ i, (A.mulVec u) i * A i a) * (∑ j, (A.mulVec v) j * A j b) * M a b := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          exact sum2_mul (fun i => (A.mulVec u) i * A i a) (fun j => (A.mulVec v) j * A j b) (M a b)
    _ = ∑ a, ∑ b, u a * v b * M a b := by simp only [hu, hv]

/-- The last two slots of `rot A R i j k l` contract against `Aγ`, `Aδ` to the two-slot contraction
of `γ`, `δ`. -/
theorem rot2_inner {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (γ δ : Fin n → ℝ) (a b : Fin n) :
    (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * (∑ c, ∑ d, A k c * A l d * R a b c d))
      = ∑ c, ∑ d, γ c * δ d * R a b c d := by
  have hcg : ∀ c, ∑ k, (A.mulVec γ) k * A k c = γ c := collapse_vec hA γ
  have hcd : ∀ d, ∑ l, (A.mulVec δ) l * A l d = δ d := collapse_vec hA δ
  calc ∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * (∑ c, ∑ d, A k c * A l d * R a b c d)
      = ∑ k, ∑ l, ∑ c, ∑ d,
          (A.mulVec γ) k * (A.mulVec δ) l * (A k c * (A l d * R a b c d)) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [mul_sum2]
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          ring
    _ = ∑ c, ∑ d, ∑ k, ∑ l,
          (A.mulVec γ) k * (A.mulVec δ) l * (A k c * (A l d * R a b c d)) :=
          Q2P.block_swap
            (fun k l c d => (A.mulVec γ) k * (A.mulVec δ) l * (A k c * (A l d * R a b c d)))
    _ = ∑ c, ∑ d, (∑ k, (A.mulVec γ) k * A k c) * (∑ l, (A.mulVec δ) l * A l d) * R a b c d := by
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          have h : (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * (A k c * (A l d * R a b c d)))
                 = ∑ k, ∑ l, ((A.mulVec γ) k * A k c) * ((A.mulVec δ) l * A l d) * R a b c d := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro l _
            ring
          exact h.trans (sum2_mul (fun k => (A.mulVec γ) k * A k c)
            (fun l => (A.mulVec δ) l * A l d) (R a b c d))
    _ = ∑ c, ∑ d, γ c * δ d * R a b c d := by simp only [hcg, hcd]

/-- Contracting the last two slots of `rot A R i j k l` against `Aγ`, `Aδ`, re-expanded in the
original frame. -/
theorem rot_contract2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (γ δ : Fin n → ℝ) (i j : Fin n) :
    (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l)
      = ∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, γ c * δ d * R a b c d) := by
  have hrot : ∀ k l, rot A R i j k l
      = ∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d) := by
    intro k l
    rw [rot]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    ring
  have step1 : (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l)
      = ∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
          (∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hrot k l]
  have step2 : (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
          (∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)))
      = ∑ k, ∑ l, ∑ a, ∑ b, (A.mulVec γ) k * (A.mulVec δ) l *
          (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)) := by
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    exact mul_sum2 ((A.mulVec γ) k * (A.mulVec δ) l)
      (fun a b => A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d))
  have step3 : (∑ k, ∑ l, ∑ a, ∑ b, (A.mulVec γ) k * (A.mulVec δ) l *
          (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)))
      = ∑ a, ∑ b, ∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
          (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)) :=
    Q2P.block_swap (fun k l a b => (A.mulVec γ) k * (A.mulVec δ) l *
      (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)))
  have step4 : (∑ a, ∑ b, ∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
          (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)))
      = ∑ a, ∑ b, A i a * A j b *
          (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
            (∑ c, ∑ d, A k c * A l d * R a b c d)) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    have h : (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
            (A i a * A j b * (∑ c, ∑ d, A k c * A l d * R a b c d)))
          = ∑ k, ∑ l, (A i a * A j b) * ((A.mulVec γ) k * (A.mulVec δ) l *
            (∑ c, ∑ d, A k c * A l d * R a b c d)) := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      ring
    exact h.trans (mul_sum2 (A i a * A j b)
      (fun k l => (A.mulVec γ) k * (A.mulVec δ) l * (∑ c, ∑ d, A k c * A l d * R a b c d))).symm
  have step5 : (∑ a, ∑ b, A i a * A j b *
          (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l *
            (∑ c, ∑ d, A k c * A l d * R a b c d)))
      = ∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, γ c * δ d * R a b c d) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [rot2_inner hA R γ δ a b]
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

/-- **Orthogonal invariance of the four-fold contraction.**  For `A ∈ O(n)` the completely
contracted quartic form `R4` of the rotated curvature tensor equals that of the original tensor. -/
theorem rot_contract4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n)
    (α β γ δ : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        Matrix.mulVec A α i * Matrix.mulVec A β j * Matrix.mulVec A γ k
          * Matrix.mulVec A δ l * Submission.Diff.Alg.rot A R i j k l)
      = ∑ a, ∑ b, ∑ c, ∑ d, α a * β b * γ c * δ d * R a b c d := by
  have hK : ∀ i j : Fin n,
      (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l)
        = ∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, γ c * δ d * R a b c d) :=
    fun i j => rot_contract2 hA R γ δ i j
  have step1 : (∑ i, ∑ j, ∑ k, ∑ l, (A.mulVec α) i * (A.mulVec β) j * (A.mulVec γ) k
        * (A.mulVec δ) l * rot A R i j k l)
      = ∑ i, ∑ j, (A.mulVec α) i * (A.mulVec β) j *
          (∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, γ c * δ d * R a b c d)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hfac : (∑ k, ∑ l, (A.mulVec α) i * (A.mulVec β) j * (A.mulVec γ) k
            * (A.mulVec δ) l * rot A R i j k l)
          = (A.mulVec α) i * (A.mulVec β) j *
            (∑ k, ∑ l, (A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l) := by
      have h : (∑ k, ∑ l, (A.mulVec α) i * (A.mulVec β) j * (A.mulVec γ) k
              * (A.mulVec δ) l * rot A R i j k l)
            = ∑ k, ∑ l, ((A.mulVec α) i * (A.mulVec β) j) *
                ((A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        ring
      exact h.trans (mul_sum2 ((A.mulVec α) i * (A.mulVec β) j)
        (fun k l => (A.mulVec γ) k * (A.mulVec δ) l * rot A R i j k l)).symm
    rw [hfac, hK i j]
  have step2 : (∑ i, ∑ j, (A.mulVec α) i * (A.mulVec β) j *
          (∑ a, ∑ b, A i a * A j b * (∑ c, ∑ d, γ c * δ d * R a b c d)))
      = ∑ a, ∑ b, α a * β b * (∑ c, ∑ d, γ c * δ d * R a b c d) :=
    collapse2 hA (fun a b => ∑ c, ∑ d, γ c * δ d * R a b c d) α β
  have step3 : (∑ a, ∑ b, α a * β b * (∑ c, ∑ d, γ c * δ d * R a b c d))
      = ∑ a, ∑ b, ∑ c, ∑ d, α a * β b * γ c * δ d * R a b c d := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [mul_sum2]
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  exact step1.trans (step2.trans step3)

end Work.Diff.Alg
