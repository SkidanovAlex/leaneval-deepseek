import Submission.Realize
import Submission.Eigen

open EquiangularLinesFixedAngle
open Filter
open Matrix
open Unitary
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! Generic-index Gram-matrix realization and line-configuration lemmas.

The results in `Realize.lean` are stated for matrices indexed by `Fin n`.  Here we
repeat the realization pipeline for an arbitrary finite index type `ι`, which is what
we need for configurations indexed by block/sum types (e.g. disjoint unions of graphs).
The ambient space is still `Euc d = EuclideanSpace ℝ (Fin d)`. -/


/-- Summing over all indices equals summing over the subtype where `p` holds, provided
`f` vanishes outside `p`. Generic index type. -/
lemma sum_zero_off_any {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (f : ι → ℝ) (hf : ∀ k : ι, ¬ p k → f k = 0) :
    (∑ k : ι, f k) = ∑ k : {x : ι // p x}, f k.1 := by
  classical
  calc
    (∑ k : ι, f k) = ∑ k ∈ (Finset.univ : Finset ι), (if p k then f k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hp : p k
      · simp [hp]
      · simp [hp, hf k hp]
    _ = ∑ k ∈ (Finset.univ : Finset ι).filter p, f k := by
      rw [Finset.sum_filter]
    _ = ∑ k : {x : ι // p x}, f k.1 := by
      exact Finset.sum_subtype (s := (Finset.univ : Finset ι).filter p)
        (h := fun x => by simp) (f := f)

/-- Entrywise spectral decomposition over an arbitrary finite index type. -/
lemma entrywise_spectral_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i j : ι) :
    A i j = ∑ k : ι, (hA.eigenvalues k) * (hA.eigenvectorBasis k) i
      * (hA.eigenvectorBasis k) j := by
  classical
  conv_lhs => rw [hA.spectral_theorem]
  rw [conjStarAlgAut_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    star_trivial]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- If a Gram realization exists in dimension `r ≤ d`, it exists in dimension `d`.
Generic index type. -/
lemma gram_realize_embed_any {ι : Type*} [Fintype ι] {r d : ℕ} (hrd : r ≤ d)
    (A : Matrix ι ι ℝ)
    (hreal : ∃ v : ι → Euc r, Matrix.gram ℝ v = A) :
    ∃ v : ι → Euc d, Matrix.gram ℝ v = A := by
  classical
  rcases hreal with ⟨v, hv⟩
  refine ⟨fun i => coordExt hrd (v i), ?_⟩
  apply Matrix.ext
  intro i j
  rw [Matrix.gram_apply]
  have hcoord : ⟪coordExt hrd (v i), coordExt hrd (v j)⟫ = ⟪v i, v j⟫ :=
    coordExt_inner hrd (v i) (v j)
  rw [hcoord]
  exact congrArg (fun M : Matrix ι ι ℝ => M i j) hv

/-- Realization of a PSD matrix of rank `r` as a Gram matrix in `𝔼^r`, arbitrary index type. -/
lemma gram_realize_rank_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hP : A.PosSemidef) :
    ∃ v : ι → Euc (A.rank), Matrix.gram ℝ v = A := by
  classical
  have hA : A.IsHermitian := hP.isHermitian
  let σ : ι → ℝ := hA.eigenvalues
  have hσ0 : ∀ k : ι, 0 ≤ σ k := fun k => by
    dsimp [σ]
    exact hP.eigenvalues_nonneg k
  let s := {k : ι // σ k ≠ 0}
  have hs : Fintype.card s = A.rank := by
    dsimp [s, σ]
    exact (hA.rank_eq_card_non_zero_eigs).symm
  let e : s ≃ Fin (A.rank) := (Fintype.equivFin s).trans (finCastEquiv hs)
  let v : ι → Euc (A.rank) := fun i =>
    eucOfFun (fun t : Fin (A.rank) =>
      Real.sqrt (σ (e.symm t).1) * (hA.eigenvectorBasis (e.symm t).1) i)
  refine ⟨v, ?_⟩
  apply Matrix.ext
  intro i j
  calc
    (Matrix.gram ℝ v) i j = ∑ t : Fin (A.rank), (Real.sqrt (σ (e.symm t).1) * (hA.eigenvectorBasis (e.symm t).1) i)
        * (Real.sqrt (σ (e.symm t).1) * (hA.eigenvectorBasis (e.symm t).1) j) := by
          rw [Matrix.gram_apply]
          rw [euclidean_inner_apply]
          rfl
    _ = ∑ t : Fin (A.rank), σ (e.symm t).1 * (hA.eigenvectorBasis (e.symm t).1) i
        * (hA.eigenvectorBasis (e.symm t).1) j := by
          apply Finset.sum_congr rfl
          intro t ht
          have hsq : (Real.sqrt (σ (e.symm t).1)) ^ 2 = σ (e.symm t).1 := by
            rw [Real.sq_sqrt]
            exact hσ0 (e.symm t).1
          ring_nf
          rw [hsq]
          ring
    _ = ∑ k : s, σ k.1 * (hA.eigenvectorBasis k.1) i * (hA.eigenvectorBasis k.1) j := by
          exact Fintype.sum_equiv e.symm
            (fun t : Fin (A.rank) => σ (e.symm t).1 * (hA.eigenvectorBasis (e.symm t).1) i
              * (hA.eigenvectorBasis (e.symm t).1) j)
            (fun k : s => σ k.1 * (hA.eigenvectorBasis k.1) i * (hA.eigenvectorBasis k.1) j) (by
              intro t
              rfl)
    _ = ∑ k : ι, σ k * (hA.eigenvectorBasis k) i * (hA.eigenvectorBasis k) j := by
          exact (sum_zero_off_any (fun k : ι => σ k ≠ 0)
            (fun k : ι => σ k * (hA.eigenvectorBasis k) i * (hA.eigenvectorBasis k) j)
            (by
              intro k hk
              have hz : σ k = 0 := by
                by_contra h
                exact hk h
              simp [hz])).symm
    _ = A i j := by
          rw [entrywise_spectral_any A hA i j]

/-- Realization of a PSD matrix of rank at most `d` as a Gram matrix in `𝔼^d`. -/
lemma gram_realize_any {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (A : Matrix ι ι ℝ) (hP : A.PosSemidef)
    (hr : A.rank ≤ d) : ∃ v : ι → Euc d, Matrix.gram ℝ v = A := by
  classical
  have hreal := gram_realize_rank_any A hP
  exact gram_realize_embed_any hr A hreal

/-- An equiangular family indexed by an arbitrary finite type. -/
def HasLinesAny (α : ℝ) (ι : Type*) [Fintype ι] (d : ℕ) : Prop :=
  ∃ v : ι → Euc d,
    (∀ i : ι, ‖v i‖ = 1) ∧ ∀ ⦃i j : ι⦄, i ≠ j → |⟪v i, v j⟫| = α

/-- A PSD matrix with unit diagonal and off-diagonal entries of absolute value `α`
is the Gram matrix of an equiangular family, indexed by any finite type. -/
lemma lines_of_gram_any {α : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (A : Matrix ι ι ℝ) (hP : A.PosSemidef)
    (hr : A.rank ≤ d) (hdiag : ∀ i : ι, A i i = 1)
    (hoff : ∀ ⦃i j : ι⦄, i ≠ j → |A i j| = α) : HasLinesAny α ι d := by
  classical
  rcases gram_realize_any A hP hr with ⟨v, hv⟩
  refine ⟨v, ?_, ?_⟩
  · intro i
    have hg := congrFun (congrFun hv i) i
    rw [Matrix.gram_apply, real_inner_self_eq_norm_sq, hdiag i] at hg
    have hsq : ‖v i‖ ^ 2 = 1 := hg
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · linarith [norm_nonneg (v i)]
  · intro i j hij
    have hg := congrFun (congrFun hv i) j
    rw [Matrix.gram_apply] at hg
    rw [hg]
    exact hoff hij

/-- From an `ι`-indexed family we get a `Fin (Fintype.card ι)`-indexed family. -/
lemma hasLines_of_hasLinesAny (α : ℝ) (ι : Type*) [Fintype ι] (d : ℕ)
    (h : HasLinesAny α ι d) : HasLines α (Fintype.card ι) d := by
  classical
  rcases h with ⟨v, hvnorm, hvangle⟩
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨fun i => v (e i), ?_, ?_⟩
  · intro i
    exact hvnorm (e i)
  · intro i j hij
    have hne : e i ≠ e j := by
      intro h
      apply hij
      exact e.injective h
    exact hvangle hne

end Submission
