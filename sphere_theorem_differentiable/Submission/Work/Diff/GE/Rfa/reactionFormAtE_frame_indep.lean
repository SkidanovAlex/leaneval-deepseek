import Mathlib
import Submission.Work.Diff.GE.Rfa.Defs
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.rot_contract
import Submission.Work.Diff.GE.rot_pair
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame independence of `reactionFormAtE`

`Work.Diff.GE.Rfa.reactionFormAtE F g x e a b c d` is the value `F(Rm)` of the `(0,4)`-tensor
`F (rmFrame g x e)` contracted with the four vectors `a b c d` expanded in the frame `e`.  If `F`
commutes with the orthogonal action `rot` on curvature arrays, this value does not depend on the
*choice* of orthonormal frame `e` at `x`: this is the lemma proved here.

Route.  Two orthonormal frames at `x` differ by an orthogonal matrix `A`
(`Work.Diff.GE.onFrame_orthogonal_change`: `e' i = ∑ j, A i j • e j`), under which the curvature
components transform by `rot A` (`Work.Diff.GE.rmFrame_eq_rot`), and `F` intertwines `rot A`
(hypothesis `hE`).  The remaining step is purely algebraic: for `A ∈ O(n)`, the fourfold contraction
of `rot A X` with the `A`-transformed coefficient vectors is the contraction of `X` with the original
coefficient vectors (`rot_vec_contract` below).  It is proved by writing the coefficient array
`(i,j,k,l) ↦ (∑ a, A i a * B a) * … * (∑ d, A l d * E d)` as `rot A (B ⊗ C ⊗ D ⊗ E)` and using the
orthogonal invariance of the Frobenius pairing of curvature arrays (`Work.Diff.GE.rot_pair`).
-/

namespace Work.Diff.GE.Rfa

open scoped BigOperators
open Submission.Diff Submission.Diff.Alg

/-! ## The algebraic contraction identity -/

variable {n : ℕ}

/-- The rank-one four-tensor `B ⊗ C ⊗ D ⊗ E`. -/
private noncomputable def outer4 (B C D E : Fin n → ℝ) : Curv4 n :=
  fun a b c d => B a * C b * D c * E d

/-- `rot A` is multiplicative on the outer product `B ⊗ C ⊗ D ⊗ E`: the transformed array is the
outer product of the four `A`-transformed coefficient vectors. -/
private theorem rot_outer4 (A : Matrix (Fin n) (Fin n) ℝ) (B C D E : Fin n → ℝ)
    (i j k l : Fin n) :
    rot A (outer4 B C D E) i j k l
      = (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d) := by
  have key : (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * (B a * C b * D c * E d) := by
    have h1 : (∑ a, A i a * B a) * (∑ b, A j b * C b)
        = ∑ a, ∑ b, (A i a * B a) * (A j b * C b) := Finset.sum_mul_sum _ _ _ _
    have h2 : (∑ a, ∑ b, (A i a * B a) * (A j b * C b)) * (∑ c, A k c * D c)
        = ∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul_sum]
    have h3 : (∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c))
          * (∑ d, A l d * E d)
        = ∑ a, ∑ b, ∑ c, ∑ d,
            (A i a * B a) * (A j b * C b) * (A k c * D c) * (A l d * E d) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul_sum]
    rw [h1, h2, h3]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [key]
  simp only [rot, outer4]

/-- **Algebraic contraction identity for `rot`.**  For an orthogonal `A`, contracting `rot A X` with
the four `A`-transformed coefficient vectors is the same as contracting `X` with the original
coefficient vectors. -/
private theorem rot_vec_contract (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (B C D E : Fin n → ℝ) (X : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
          * (∑ d, A l d * E d) * rot A X i j k l)
      = ∑ a, ∑ b, ∑ c, ∑ d, B a * C b * D c * E d * X a b c d := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
        (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
          * (∑ d, A l d * E d) * rot A X i j k l)
      = ∑ i, ∑ j, ∑ k, ∑ l, rot A (outer4 B C D E) i j k l * rot A X i j k l := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [rot_outer4 A B C D E i j k l]
  rw [h1, Work.Diff.GE.rot_pair A hA (outer4 B C D E) X]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  simp only [outer4]

/-! ## Frame independence -/

theorem reactionFormAtE_frame_indep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hE : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    (g : Submission.Diff.SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (he' : Submission.Diff.IsONFrame g x e')
    (a b c d : TangentSpace I x) :
    Work.Diff.GE.Rfa.reactionFormAtE F g x e' a b c d
      = Work.Diff.GE.Rfa.reactionFormAtE F g x e a b c d := by
  obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x e e' he he'
  have hrm : Submission.Diff.rmFrame g x e' = rot A (Submission.Diff.rmFrame g x e) :=
    Work.Diff.GE.rmFrame_eq_rot hLC g x e e' A hAe
  have hF : F (Submission.Diff.rmFrame g x e')
      = rot A (F (Submission.Diff.rmFrame g x e)) := by
    rw [hrm, hE A hA]
  have hinner : ∀ (c : TangentSpace I x) (i : Fin (Module.finrank ℝ E)),
      g.inner x (e' i) c = ∑ j, A i j * g.inner x (e j) c := by
    intro c i
    rw [hAe i]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  simp only [reactionFormAtE]
  rw [hF]
  simp only [hinner]
  exact rot_vec_contract A hA (fun j => g.inner x (e j) a) (fun j => g.inner x (e j) b)
    (fun j => g.inner x (e j) c) (fun j => g.inner x (e j) d)
    (F (Submission.Diff.rmFrame g x e))

end Work.Diff.GE.Rfa
