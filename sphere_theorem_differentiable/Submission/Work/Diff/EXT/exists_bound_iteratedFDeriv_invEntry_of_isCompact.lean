import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounds for the iterated derivatives of the entries of the matrix inverse on compacts

If `T` is a compact set of matrices on which the determinant does not vanish, then for every
order `k` the iterated derivatives (of order `≤ k`) of the entries `A ↦ (A⁻¹) i j` are uniformly
bounded on `T`.

The proof uses Cramer's rule `A⁻¹ = (det A)⁻¹ • adjugate A`: the determinant and the adjugate
entries are polynomial (hence smooth) functions of the entries, and `(det A)⁻¹` is smooth on the
open set `{det ≠ 0}`.  Smoothness gives continuity of the iterated derivatives of order `≤ k` on
that open set, and a continuous function on a compact set is bounded.
-/

namespace Work.Diff.EXT

open Matrix

/-- The determinant, as a function of the entries of the matrix, is smooth. -/
private lemma contDiff_det_ofFun (n : ℕ) :
    ContDiff ℝ ⊤ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  have h : (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det)
      = fun A => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i := by
    funext A; rw [Matrix.det_apply']; rfl
  rw [h]
  fun_prop

/-- The matrix obtained from `A` by replacing the `j`-th row by the `i`-th unit vector
(expressed directly on the function space `Fin n → Fin n → ℝ`, so that it is a `Pi`-type). -/
private def updRowFun (n : ℕ) (i j : Fin n) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  Function.update A j (Pi.single i 1)

/-- Replacing a row of a matrix by a fixed row is a smooth function of the matrix. -/
private lemma contDiff_updRowFun (n : ℕ) (i j : Fin n) :
    ContDiff ℝ ⊤ (updRowFun n i j) := by
  rw [contDiff_pi]
  intro k
  rw [contDiff_pi]
  intro l
  by_cases hk : k = j
  · have hfun : (fun x : Fin n → Fin n → ℝ => updRowFun n i j x k l)
        = fun _ : Fin n → Fin n → ℝ => (Pi.single i (1:ℝ) : Fin n → ℝ) l := by
      funext x
      simp only [updRowFun, Function.update_apply]
      exact congrArg (fun f : Fin n → ℝ => f l) (if_pos hk)
    rw [hfun]
    exact contDiff_const
  · have hfun : (fun x : Fin n → Fin n → ℝ => updRowFun n i j x k l) = fun x => x k l := by
      funext x
      simp only [updRowFun, Function.update_apply]
      exact congrArg (fun f : Fin n → ℝ => f l) (if_neg hk)
    rw [hfun]
    fun_prop

/-- Every entry of the adjugate is a smooth function of the entries of the matrix. -/
private lemma contDiff_adjugate_entry (n : ℕ) (i j : Fin n) :
    ContDiff ℝ ⊤ (fun A : Fin n → Fin n → ℝ => (Matrix.of A).adjugate i j) := by
  have h : ContDiff ℝ ⊤ (fun A : Fin n → Fin n → ℝ => (Matrix.of (updRowFun n i j A)).det) :=
    (contDiff_det_ofFun n).comp (contDiff_updRowFun n i j)
  have hfun : (fun A : Fin n → Fin n → ℝ => (Matrix.of (updRowFun n i j A)).det)
      = fun A => (Matrix.of A).adjugate i j := by
    funext A
    rw [Matrix.adjugate_apply]
    rfl
  rw [hfun] at h
  exact h

/-- The set of matrices with non-vanishing determinant is open. -/
private lemma isOpen_det_ne_zero (n : ℕ) :
    IsOpen {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} := by
  have hc : Continuous (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) :=
    (contDiff_det_ofFun n).continuous
  have hset : {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0}
      = {A : Fin n → Fin n → ℝ | (Matrix.of A).det = 0}ᶜ := by
    ext A; simp
  rw [hset]
  exact (isClosed_eq hc continuous_const).isOpen_compl

/-- Each entry of the inverse is a smooth function on the set of invertible matrices. -/
private lemma contDiffOn_invEntry (n : ℕ) (i j : Fin n) :
    ContDiffOn ℝ ⊤ (fun A : Fin n → Fin n → ℝ => (Matrix.of A)⁻¹ i j)
      {A | (Matrix.of A).det ≠ 0} := by
  have hdet := contDiff_det_ofFun n
  have hadj := contDiff_adjugate_entry n i j
  have h1 : ContDiffOn ℝ ⊤ (fun A : Fin n → Fin n → ℝ => ((Matrix.of A).det)⁻¹)
      {A | (Matrix.of A).det ≠ 0} :=
    (hdet.contDiffOn).inv (fun A hA => hA)
  have h2 : ContDiffOn ℝ ⊤
      (fun A : Fin n → Fin n → ℝ => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j)
      {A | (Matrix.of A).det ≠ 0} :=
    h1.mul hadj.contDiffOn
  refine h2.congr ?_
  intro A _
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

/-- For a fixed entry `(i, j)` and a fixed order `s`, the `s`-th derivative of `A ↦ A⁻¹ i j` is
bounded on any compact set contained in the invertible matrices. -/
private lemma exists_bound_invEntry_at (n : ℕ) {T : Set (Fin n → Fin n → ℝ)} (hT : IsCompact T)
    (hTsub : T ⊆ {A | (Matrix.of A).det ≠ 0}) (i j : Fin n) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A ∈ T,
      ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖ ≤ C := by
  have hU := isOpen_det_ne_zero n
  have hcont : ContinuousOn
      (fun A : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖)
      {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} :=
    (ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_invEntry n i j) hU (by simp)).norm
  obtain ⟨C, hC⟩ := (hT.image_of_continuousOn (hcont.mono hTsub)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun A hA => ?_⟩
  have hmem : (fun A : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖) A
      ∈ (fun A : Fin n → Fin n → ℝ =>
        ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖) '' T :=
    ⟨A, hA, rfl⟩
  exact le_trans (hC hmem) (le_max_left _ _)

lemma exists_bound_iteratedFDeriv_invEntry_of_isCompact
    (n : ℕ) {T : Set (Fin n → Fin n → ℝ)} (hT : IsCompact T)
    (hTsub : T ⊆ {A | (Matrix.of A).det ≠ 0}) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A ∈ T, ∀ (i j : Fin n), ∀ s ≤ k,
      ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖ ≤ C := by
  classical
  have key : ∀ p : (Fin n × Fin n) × Fin (k + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ A ∈ T, ‖iteratedFDeriv ℝ (p.2 : ℕ)
        (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ p.1.1 p.1.2) A‖ ≤ C :=
    fun p => exists_bound_invEntry_at n hT hTsub p.1.1 p.1.2 p.2
  choose C hC using key
  refine ⟨∑ p : (Fin n × Fin n) × Fin (k + 1), C p,
    Finset.sum_nonneg (fun p _ => (hC p).1), ?_⟩
  intro A hA i j s hs
  have hlt : s < k + 1 := Nat.lt_succ_of_le hs
  have hb : ‖iteratedFDeriv ℝ s (fun A' : Fin n → Fin n → ℝ => (Matrix.of A')⁻¹ i j) A‖ ≤
      C ((i, j), ⟨s, hlt⟩) := (hC ((i, j), ⟨s, hlt⟩)).2 A hA
  exact hb.trans (Finset.single_le_sum (fun p _ => (hC p).1) (Finset.mem_univ _))

end Work.Diff.EXT
