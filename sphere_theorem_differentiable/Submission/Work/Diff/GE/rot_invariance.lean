import Mathlib
import Submission.Work.Diff.GE.rot_frobsq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-!
# Orthogonal invariance of the frame functionals of a curvature tensor

`scalAlg`, `frobSq`, `ricSq` and `frobSqTF` are the scalar functionals of a curvature array `R`
(`|Rm|²`, `|Ric|²`, `scal`, and the squared distance to the constant-curvature line) computed in an
*orthonormal* frame.  Changing to another orthonormal frame acts on the components by
`rot A R i j k l = ∑ Aᵢₐ Aⱼᵦ Aₖ_c Aₗ_d R a b c d` with `A ∈ O(n)`, and `rot_invariance` says that
each of the four functionals is unchanged: this is the statement that these norms do not depend on
the choice of orthonormal frame.

The proofs all rest on the single row-orthogonality identity

* `col_sum` : `(Aᵀ A) a c = ∑ i, A i a * A i c = if a = c then 1 else 0`,

i.e. that the columns of an orthogonal matrix are orthonormal, combined with Fubini for finite
sums.  `collapse_k` is the atomic "one index is contracted against two columns of `A`" step;
`sum_sq_orth2` is the two-index version of "orthogonal matrices preserve sums of squares"
(equivalently `∑ᵢ (A *ᵥ v)ᵢ² = ∑ᵢ vᵢ²`, cf. `sum_sq_mulVec` in `rot_frobsq`).  The `frobSq`
conjunct is imported from `Work.Diff.GE.rot_frobsq`, where it is proved via the fourfold Kronecker
matrix `A ⊗ A ⊗ A ⊗ A`.
-/

variable {n : ℕ}

/-- The columns of an orthogonal matrix are orthonormal. -/
private lemma col_sum (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1) :
    ∀ a c : Fin n, ∑ i, A i a * A i c = if a = c then 1 else 0 := by
  intro a c
  have h := congr_fun (congr_fun hA a) c
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- Collapsing a Kronecker delta in a double sum. -/
private lemma sum_ite_diag (X : Fin n → Fin n → ℝ) :
    ∑ b, ∑ d, (if b = d then 1 else 0) * X b d = ∑ b, X b b := by
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd; simp [Ne.symm hd]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The atomic contraction step: two indices of a sum contracted against two columns of an
orthogonal matrix collapse to the diagonal. -/
private lemma collapse_k (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1)
    (X : Fin n → Fin n → ℝ) :
    ∑ k, ∑ a, ∑ c, (A k a * A k c) * X a c = ∑ a, X a a := by
  have hcol := col_sum A hA
  calc ∑ k, ∑ a, ∑ c, (A k a * A k c) * X a c
      = ∑ a, ∑ k, ∑ c, (A k a * A k c) * X a c := Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ k, (A k a * A k c) * X a c :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ a, ∑ c, (∑ k, A k a * A k c) * X a c := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ c, (if a = c then 1 else 0) * X a c := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
          rw [hcol a c]
    _ = ∑ a, X a a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_eq_single a]
          · simp
          · intro c _ hc; simp [Ne.symm hc]
          · intro h; exact absurd (Finset.mem_univ a) h

/-- An orthogonal matrix preserves the sum of squares of the two-index array
`(a,b) ↦ ∑ᵢ ∑ⱼ A i a * A j b * M a b`. -/
private lemma sum_sq_orth2 (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose * A = 1)
    (M : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (∑ a, ∑ b, A i a * A j b * M a b)^2 = ∑ a, ∑ b, M a b^2 := by
  have hcol := col_sum A hA
  have key : ∀ i j : Fin n, (∑ a, ∑ b, A i a * A j b * M a b)
      = ∑ a, A i a * (∑ b, A j b * M a b) := by
    intro i j
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have sso : ∀ (g : Fin n → ℝ), ∑ i, (∑ a, A i a * g a)^2 = ∑ a, g a^2 := by
    intro g
    calc ∑ i, (∑ a, A i a * g a)^2
        = ∑ i, ∑ a, ∑ b, (A i a * A i b) * (g a * g b) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [pow_two, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            refine Finset.sum_congr rfl (fun b _ => ?_)
            ring
      _ = ∑ a, ∑ b, (∑ i, A i a * A i b) * (g a * g b) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [Finset.sum_mul]
      _ = ∑ a, ∑ b, (if a = b then 1 else 0) * (g a * g b) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [hcol a b]
      _ = ∑ a, g a^2 := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.sum_eq_single a]
            · simp [pow_two]
            · intro b _ hb; simp [Ne.symm hb]
            · intro h; exact absurd (Finset.mem_univ a) h
  calc ∑ i, ∑ j, (∑ a, ∑ b, A i a * A j b * M a b)^2
      = ∑ i, ∑ j, (∑ a, A i a * (∑ b, A j b * M a b))^2 := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [key i j]
    _ = ∑ j, ∑ i, (∑ a, A i a * (∑ b, A j b * M a b))^2 := Finset.sum_comm
    _ = ∑ j, ∑ a, (∑ b, A j b * M a b)^2 := by
          refine Finset.sum_congr rfl (fun j _ => sso (fun a => ∑ b, A j b * M a b))
    _ = ∑ a, ∑ j, (∑ b, A j b * M a b)^2 := Finset.sum_comm
    _ = ∑ a, ∑ b, M a b^2 := by
          refine Finset.sum_congr rfl (fun a _ => sso (fun b => M a b))

/-- `scalAlg` is invariant under an orthogonal change of frame. -/
private lemma scalAlg_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    scalAlg (rot A R) = scalAlg R := by
  have hAA : A.transpose * A = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  have hcol := col_sum A hAA
  calc scalAlg (rot A R)
      = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ d,
          (A i a * A i c) * (A j b * A j d) * R a b c d := by
          rw [scalAlg]
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          simp only [rot]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          ring
    _ = ∑ i, ∑ a, ∑ c, ∑ j, ∑ b, ∑ d,
          (A i a * A i c) * (A j b * A j d) * R a b c d := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          calc ∑ j, ∑ a, ∑ b, ∑ c, ∑ d, (A i a * A i c) * (A j b * A j d) * R a b c d
              = ∑ a, ∑ j, ∑ b, ∑ c, ∑ d,
                  (A i a * A i c) * (A j b * A j d) * R a b c d := Finset.sum_comm
            _ = ∑ a, ∑ b, ∑ j, ∑ c, ∑ d,
                  (A i a * A i c) * (A j b * A j d) * R a b c d :=
                  Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
            _ = ∑ a, ∑ c, ∑ j, ∑ b, ∑ d,
                  (A i a * A i c) * (A j b * A j d) * R a b c d := by
                  refine Finset.sum_congr rfl (fun a _ => ?_)
                  calc ∑ b, ∑ j, ∑ c, ∑ d, (A i a * A i c) * (A j b * A j d) * R a b c d
                      = ∑ b, ∑ c, ∑ j, ∑ d,
                          (A i a * A i c) * (A j b * A j d) * R a b c d :=
                          Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
                    _ = ∑ c, ∑ b, ∑ j, ∑ d,
                          (A i a * A i c) * (A j b * A j d) * R a b c d := Finset.sum_comm
                    _ = ∑ c, ∑ j, ∑ b, ∑ d,
                          (A i a * A i c) * (A j b * A j d) * R a b c d :=
                          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = ∑ i, ∑ a, ∑ c, (A i a * A i c) *
          (∑ j, ∑ b, ∑ d, (A j b * A j d) * R a b c d) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
    _ = ∑ a, (∑ j, ∑ b, ∑ d, (A j b * A j d) * R a b a d) :=
          collapse_k A hAA (fun a c => ∑ j, ∑ b, ∑ d, (A j b * A j d) * R a b c d)
    _ = ∑ a, ∑ b, R a b a b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          calc ∑ j, ∑ b, ∑ d, (A j b * A j d) * R a b a d
              = ∑ b, ∑ j, ∑ d, (A j b * A j d) * R a b a d := Finset.sum_comm
            _ = ∑ b, ∑ d, ∑ j, (A j b * A j d) * R a b a d :=
                  Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
            _ = ∑ b, ∑ d, (∑ j, A j b * A j d) * R a b a d := by
                  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
                  rw [Finset.sum_mul]
            _ = ∑ b, ∑ d, (if b = d then 1 else 0) * R a b a d := by
                  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
                  rw [hcol b d]
            _ = ∑ b, R a b a b := sum_ite_diag (fun b d => R a b a d)
    _ = scalAlg R := by rw [scalAlg]

/-- `ricSq` is invariant under an orthogonal change of frame. -/
private lemma ricSq_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ricSq (rot A R) = ricSq R := by
  have hAA : A.transpose * A = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  have hric : ∀ i j : Fin n, (∑ k, rot A R k i k j)
      = ∑ b, ∑ d, A i b * A j d * (∑ a, R a b a d) := by
    intro i j
    calc ∑ k, rot A R k i k j
        = ∑ k, ∑ a, ∑ b, ∑ c, ∑ d,
            (A k a * A k c) * (A i b * A j d * R a b c d) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [rot]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
            ring
      _ = ∑ k, ∑ a, ∑ c, ∑ b, ∑ d,
            (A k a * A k c) * (A i b * A j d * R a b c d) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
            exact Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ c, (A k a * A k c) *
            (∑ b, ∑ d, A i b * A j d * R a b c d) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
              Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ a, (∑ b, ∑ d, A i b * A j d * R a b a d) :=
            collapse_k A hAA (fun a c => ∑ b, ∑ d, A i b * A j d * R a b c d)
      _ = ∑ b, ∑ d, A i b * A j d * (∑ a, R a b a d) := by
            calc ∑ a, ∑ b, ∑ d, A i b * A j d * R a b a d
                = ∑ b, ∑ a, ∑ d, A i b * A j d * R a b a d := Finset.sum_comm
              _ = ∑ b, ∑ d, ∑ a, A i b * A j d * R a b a d :=
                    Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
              _ = ∑ b, ∑ d, A i b * A j d * (∑ a, R a b a d) := by
                    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
                    rw [Finset.mul_sum]
  calc ricSq (rot A R)
      = ∑ i, ∑ j, (∑ b, ∑ d, A i b * A j d * (∑ a, R a b a d))^2 := by
          rw [ricSq]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hric i j]
    _ = ∑ b, ∑ d, (∑ a, R a b a d)^2 := sum_sq_orth2 A hAA (fun b d => ∑ a, R a b a d)
    _ = ricSq R := by rw [ricSq]

/-- The functionals `scalAlg`, `frobSq`, `ricSq`, `frobSqTF` of a curvature array are invariant under
the orthogonal action `rot A` (`A ∈ O(n)`, i.e. `AᵀA = 1`; `rot A R i j k l = ∑ AᵢₐAⱼᵦAₖ_cAₗ_d R a b c d`).
These are the "norms in an orthonormal frame do not depend on the frame" statements. -/
theorem rot_invariance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    (scalAlg (rot A R) = scalAlg R) ∧ (frobSq (rot A R) = frobSq R) ∧
      (ricSq (rot A R) = ricSq R) ∧ (frobSqTF (rot A R) = frobSqTF R) := by
  have hs := scalAlg_rot A hA R
  have hf := rot_frobsq A hA R
  have hr := ricSq_rot A hA R
  refine ⟨hs, hf, hr, ?_⟩
  rw [frobSqTF, frobSqTF, hf, hs]

end Work.Diff.GE
