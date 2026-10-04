import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.rot_pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.EvolB

open scoped BigOperators
open Submission.Diff Submission.Diff.Alg

/-! ## The algebraic contraction identity

The proof of frame independence is algebraic once the two frames are related by an orthogonal matrix
`A` (`Work.Diff.GE.onFrame_orthogonal_change`) with `rmFrame g x e' = rot A (rmFrame g x e)`
(`Work.Diff.GE.rmFrame_eq_rot`).  The four coefficient vectors `i ↦ g.inner x (e' i) a`, … are the
`A`-transforms of the coefficient vectors of the old frame (`hinner` below, which only uses the
bilinearity of `g.inner x` on the expansion `e' i = ∑ j, A i j • e j`), and the contraction of
`rot A X` with four `A`-transformed vectors equals the contraction of `X` with the original vectors
because `rot A` is orthogonal for the Frobenius pairing (`Work.Diff.GE.rot_pair`).
-/

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

namespace Work.Diff.GE.EvolB

/-- **Frame independence of the reaction form.**  For `F` commuting with the orthogonal action
`rot A`, the value `Work.Diff.GE.Rxn.reactionFormAtE F g x e a b c d` is the same for all
`g`-orthonormal frames `e` of `TₓM`.

This is a re-proof (in namespace `Work.Diff.GE.EvolB`) of the statement of
`Submission/Work/Diff/GE/covRxnA/frame_indep.lean` (and of
`Submission/Work/Diff/GE/covReaction/reactionFormAtE_frame_indep.lean`, which carries the identical
statement in the namespace `Work.Diff.GE.covReaction`); the `EvolB` development needs a `sorry`-free
copy, so do not import those two modules.  NOTE: a *proof* of the same statement (in yet another
namespace, `Work.Diff.GE.Rfa`) appears to exist already in
`Submission/Work/Diff/GE/Rfa/reactionFormAtE_frame_indep.lean` — check it with `#print axioms` and,
if it is `sorry`-free, transcribe its proof here (the constant names differ, so the copy is
genuinely needed).

Proof route.  `Work.Diff.GE.onFrame_orthogonal_change` (PROVED) gives an orthogonal matrix `A` with
`e' i = ∑ j, A i j • e j`, and `Work.Diff.GE.rmFrame_eq_rot` (PROVED) gives
`Submission.Diff.rmFrame g x e' = Submission.Diff.Alg.rot A (Submission.Diff.rmFrame g x e)`.
Writing both sides of the goal out (`Work.Diff.GE.Rxn.reactionFormAtE` is
`∑ i j k l, (g(e i) a * g(e j) b * g(e k) c * g(e l) d) * F (rmFrame g x e) i j k l`), the
orthonormality of `e` and `e'` identifies the four coefficient vectors as `Aᵀ`-transforms of each
other, `hF` turns `F (rot A R)` into `rot A (F R)`, and the packed contraction identity
`Work.Diff.GE.rot_contract` (PROVED, in `Submission/Work/Diff/GE/rot_contract.lean`) collapses the
extra index pairs:
`∑ p q, rot A φ i j p q * rot A ψ k l p q
   = ∑ a b c d, A i a * A j b * A k c * A l d * ∑ p q, φ a b p q * ψ c d p q`.
Concretely: expand `g.inner x (e' i) a` in the frame `e` (using `e' i = ∑ j A i j • e j` and the
orthonormality of `e`, i.e. `Work.Diff.GE.sum_smul_inner_eq_self` or the Parseval lemmas), and then
apply `rot_contract` with `φ := rmFrame g x e`, `ψ := F (rmFrame g x e)` (the four coefficient
vectors being the frame coordinates of `a,b,c,d` in the frame `e`).
`Submission/Work/Diff/GE/rot_kit.lean`, `rot_invariance.lean`, `rot_pair.lean`, `rot_qPair.lean`
contain the same style of orthogonal-group bookkeeping and can be used as models. -/
theorem frame_indep_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    (g : Submission.Diff.SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (he' : Submission.Diff.IsONFrame g x e')
    (a b c d : TangentSpace I x) :
    Work.Diff.GE.Rxn.reactionFormAtE F g x e' a b c d
      = Work.Diff.GE.Rxn.reactionFormAtE F g x e a b c d := by
  obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x e e' he he'
  have hrm : Submission.Diff.rmFrame g x e' = rot A (Submission.Diff.rmFrame g x e) :=
    Work.Diff.GE.rmFrame_eq_rot hLC g x e e' A hAe
  have hF' : F (Submission.Diff.rmFrame g x e')
      = rot A (F (Submission.Diff.rmFrame g x e)) := by
    rw [hrm, hF A hA]
  have hinner : ∀ (c : TangentSpace I x) (i : Fin (Module.finrank ℝ E)),
      g.inner x (e' i) c = ∑ j, A i j * g.inner x (e j) c := by
    intro c i
    rw [hAe i]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  simp only [Work.Diff.GE.Rxn.reactionFormAtE]
  rw [hF']
  simp only [hinner]
  exact rot_vec_contract A hA (fun j => g.inner x (e j) a) (fun j => g.inner x (e j) b)
    (fun j => g.inner x (e j) c) (fun j => g.inner x (e j) d)
    (F (Submission.Diff.rmFrame g x e))

end Work.Diff.GE.EvolB

/-! The statement block above carries a doubly nested `namespace Work.Diff.GE.EvolB` (an artefact of
how the statement was generated), so the theorem proved above is registered as
`Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.frame_indep_B`.  The rest of the `EvolB` development refers
to it under the natural name `Work.Diff.GE.EvolB.frame_indep_B`, so we record that name as well
(same statement, one-line application). -/

/-- **Frame independence of the reaction form** (under the natural name
`Work.Diff.GE.EvolB.frame_indep_B`).  For `F` commuting with the orthogonal action `rot A`, the
value `Work.Diff.GE.Rxn.reactionFormAtE F g x e a b c d` is the same for all `g`-orthonormal frames
`e` of `TₓM`. -/
theorem frame_indep_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (hLC : Submission.Diff.LCSmooth I M)
    (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
      Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ R : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R))
    (g : Submission.Diff.SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (he' : Submission.Diff.IsONFrame g x e')
    (a b c d : TangentSpace I x) :
    Work.Diff.GE.Rxn.reactionFormAtE F g x e' a b c d
      = Work.Diff.GE.Rxn.reactionFormAtE F g x e a b c d :=
  _root_.Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.frame_indep_B hLC F hF g x e e' he he' a b c d

end Work.Diff.GE.EvolB
