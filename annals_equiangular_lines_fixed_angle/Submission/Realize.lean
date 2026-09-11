import Submission.LowerBounds
import Submission.Eigen

open EquiangularLinesFixedAngle
open Filter
open Matrix
open Unitary
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! Gram-matrix realization of positive semidefinite matrices of bounded rank, and the
isometric coordinate embedding `𝔼^r ↪ 𝔼^d` for `r ≤ d`. -/

/-- The canonical identification of `Fin r` with the coordinates `< r` of `Fin d`. -/
def finLtEquiv {r d : ℕ} (hrd : r ≤ d) : Fin r ≃ {j : Fin d // j.val < r} where
  toFun t := ⟨Fin.castLE hrd t, by simpa using (Fin.castLE hrd t).isLt⟩
  invFun j := ⟨j.1.val, j.2⟩
  left_inv t := by
    apply Fin.ext
    simp
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp

/-- Reindexing: summing over `j : Fin d` with `j.val < r` equals summing over `Fin r`. -/
lemma sum_lt {r d : ℕ} (hrd : r ≤ d) (g : Fin r → ℝ) :
    (∑ t : Fin r, g t) = ∑ j : Fin d, (if h : j.val < r then g ⟨j.val, h⟩ else 0) := by
  classical
  let F : Fin d → ℝ := fun j => if h : j.val < r then g ⟨j.val, h⟩ else 0
  calc
    (∑ t : Fin r, g t) = ∑ s : {j : Fin d // j.val < r}, g ⟨s.1.val, s.2⟩ := by
          exact Fintype.sum_equiv (finLtEquiv hrd) g (fun s : {j : Fin d // j.val < r} => g ⟨s.1.val, s.2⟩) (by
            intro t
            apply congrArg g
            apply Fin.ext
            simp [finLtEquiv])
    _ = ∑ s : {j : Fin d // j.val < r}, F s.1 := by
          apply Finset.sum_congr rfl
          intro s hs
          dsimp [F]
          simp [s.2]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j : Fin d => j.val < r), F j := by
          exact (Finset.sum_subtype (s := (Finset.univ : Finset (Fin d)).filter (fun j : Fin d => j.val < r))
            (h := fun x => by simp [Finset.mem_filter]) (f := F)).symm
    _ = ∑ j : Fin d, F j := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hp : j.val < r
          · simp [hp]
          · simp [F, hp]
    _ = ∑ j : Fin d, (if h : j.val < r then g ⟨j.val, h⟩ else 0) := by
          simp [F]

/-- The coordinate extension map `𝔼^r → 𝔼^d` for `r ≤ d` (append zeros). -/
noncomputable def coordExt {r d : ℕ} (hrd : r ≤ d) : Euc r → Euc d :=
  fun x => eucOfFun (fun j : Fin d => if h : j.val < r then x ⟨j.val, h⟩ else 0)

lemma coordExt_apply {r d : ℕ} (hrd : r ≤ d) (x : Euc r) (j : Fin d) :
    (coordExt hrd x) j = (if h : j.val < r then x ⟨j.val, h⟩ else 0) := rfl

/-- The coordinate extension is an isometric embedding. -/
lemma coordExt_inner {r d : ℕ} (hrd : r ≤ d) (x y : Euc r) :
    ⟪coordExt hrd x, coordExt hrd y⟫ = ⟪x, y⟫ := by
  classical
  rw [euclidean_inner_apply]
  rw [euclidean_inner_apply]
  -- sum over Fin d of product of ifs = sum over j.val < r of x y
  calc
    (∑ j : Fin d, (coordExt hrd x) j * (coordExt hrd y) j)
        = ∑ j : Fin d, (if h : j.val < r then x ⟨j.val, h⟩ * y ⟨j.val, h⟩ else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [coordExt_apply, coordExt_apply]
          by_cases h : j.val < r <;> simp [h]
    _ = ∑ t : Fin r, x t * y t := by
          rw [← sum_lt hrd (fun t : Fin r => x t * y t)]

/-- If a Gram realization exists in dimension `r ≤ d`, it exists in dimension `d`. -/
lemma gram_realize_embed {n r d : ℕ} (hrd : r ≤ d) (A : Matrix (Fin n) (Fin n) ℝ)
    (hreal : ∃ v : Fin n → Euc r, Matrix.gram ℝ v = A) :
    ∃ v : Fin n → Euc d, Matrix.gram ℝ v = A := by
  classical
  rcases hreal with ⟨v, hv⟩
  refine ⟨fun i => coordExt hrd (v i), ?_⟩
  apply Matrix.ext
  intro i j
  rw [Matrix.gram_apply]
  have hcoord : ⟪coordExt hrd (v i), coordExt hrd (v j)⟫ = ⟪v i, v j⟫ :=
    coordExt_inner hrd (v i) (v j)
  rw [hcoord]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hv

/-- Summing over all indices equals summing over the subtype where `p` holds, provided
`f` vanishes outside `p`. -/
lemma sum_zero_off {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℝ)
    (hf : ∀ k : Fin n, ¬ p k → f k = 0) :
    (∑ k : Fin n, f k) = ∑ k : {x : Fin n // p x}, f k.1 := by
  classical
  calc
    (∑ k : Fin n, f k) = ∑ k ∈ (Finset.univ : Finset (Fin n)), (if p k then f k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hp : p k
      · simp [hp]
      · simp [hp, hf k hp]
    _ = ∑ k ∈ (Finset.univ : Finset (Fin n)).filter p, f k := by
      rw [Finset.sum_filter]
    _ = ∑ k : {x : Fin n // p x}, f k.1 := by
      exact Finset.sum_subtype (s := (Finset.univ : Finset (Fin n)).filter p)
        (h := fun x => by simp) (f := f)

/-- Equivalence between `Fin a` and `Fin b` from an equality of the sizes. -/
def finCastEquiv {a b : ℕ} (h : a = b) : Fin a ≃ Fin b where
  toFun t := ⟨t.1, by simpa [h] using t.2⟩
  invFun t := ⟨t.1, by simpa [← h] using t.2⟩
  left_inv t := by
    apply Fin.ext
    rfl
  right_inv t := by
    apply Fin.ext
    rfl

/-- Realization of a positive semidefinite matrix of rank `r` as a Gram matrix in `𝔼^r`. -/
lemma gram_realize_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hP : A.PosSemidef) :
    ∃ v : Fin n → Euc (A.rank), Matrix.gram ℝ v = A := by
  classical
  have hA : A.IsHermitian := hP.isHermitian
  let σ : Fin n → ℝ := hA.eigenvalues
  have hσ0 : ∀ k : Fin n, 0 ≤ σ k := fun k => by
    dsimp [σ]
    exact hP.eigenvalues_nonneg k
  let s : Type := {k : Fin n // σ k ≠ 0}
  have hs : Fintype.card s = A.rank := by
    dsimp [s, σ]
    exact (hA.rank_eq_card_non_zero_eigs).symm
  let e : s ≃ Fin (A.rank) := (Fintype.equivFin s).trans (finCastEquiv hs)
  let v : Fin n → Euc (A.rank) := fun i =>
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
    _ = ∑ k : Fin n, σ k * (hA.eigenvectorBasis k) i * (hA.eigenvectorBasis k) j := by
          exact (sum_zero_off (fun k : Fin n => σ k ≠ 0)
            (fun k : Fin n => σ k * (hA.eigenvectorBasis k) i * (hA.eigenvectorBasis k) j)
            (by
              intro k hk
              have hz : σ k = 0 := by
                by_contra h
                exact hk h
              simp [hz])).symm
    _ = A i j := by
          rw [entrywise_spectral A hA i j]

/-- Realization of a positive semidefinite matrix of rank at most `d` as a Gram matrix in
`𝔼^d`. -/
lemma gram_realize {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hP : A.PosSemidef)
    (hr : A.rank ≤ d) : ∃ v : Fin n → Euc d, Matrix.gram ℝ v = A := by
  classical
  have hreal := gram_realize_rank A hP
  exact gram_realize_embed hr A hreal


/-- A positive semidefinite matrix with unit diagonal and off-diagonal entries of absolute
value `α` is the Gram matrix of an equiangular configuration of unit vectors. -/
lemma lines_of_gram {α : ℝ} {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hP : A.PosSemidef)
    (hr : A.rank ≤ d) (hdiag : ∀ i : Fin n, A i i = 1)
    (hoff : ∀ ⦃i j : Fin n⦄, i ≠ j → |A i j| = α) : HasLines α n d := by
  classical
  rcases gram_realize A hP hr with ⟨v, hv⟩
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

end Submission
