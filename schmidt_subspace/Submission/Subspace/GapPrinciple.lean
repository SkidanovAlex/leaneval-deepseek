import Mathlib
import Submission.Subspace.ApproxSpace
import Submission.Commons.NumberTheory.DiophantineApproximation.det_eq_zero_of_box_gap_le

/-!
# The gap principle for the approximation domain

If `Q ≤ Q' ≤ Q ^ (1 + ε/2)`, both scales large, and `V(Q) = approxSpace L γ Q` is a
*hyperplane*, then `V(Q') ≤ V(Q)`.  Equivalently: two *distinct* hyperplanes `V(Q)`, `V(Q')`
with `Q < Q'` force the multiplicative gap `Q' > Q ^ (1 + ε/2)`.

This is Evertse's Lemma 28 in the elementary form suitable for the development here; it rests
on the "box gap" determinant lemma `Commons.NumberTheory.DiophantineApproximation.det_eq_zero_of_box_gap_le`.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {N : ℕ}

/-- If `g : Fin (N-1) → Fin N → K` is linearly independent and `y` is outside its span, the
square matrix with columns `g 0, …, g (N-2), y` is invertible. -/
private lemma det_ne_zero_aux {K : Type*} [Field K] {n : ℕ}
    (g : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (hg : LinearIndependent K g)
    (hy : y ∉ Submodule.span K (Set.range g)) :
    (Matrix.of (fun i j : Fin (n + 1) =>
      if h : (j : ℕ) < n then g ⟨j, h⟩ i else y i)).det ≠ 0 := by
  classical
  have hcol : (Matrix.of (fun i j : Fin (n + 1) =>
      if h : (j : ℕ) < n then g ⟨j, h⟩ i else y i)).col = Fin.snoc g y := by
    funext j i
    rw [Matrix.col_apply, Matrix.of_apply]
    refine Fin.lastCases ?_ ?_ j
    · rw [Fin.snoc_last]
      rw [dif_neg (by rw [Fin.val_last]; exact Nat.lt_irrefl n)]
    · intro j'
      rw [Fin.snoc_castSucc, dif_pos (by simpa using j'.isLt)]
      simp
  have hli : LinearIndependent K (Matrix.of (fun i j : Fin (n + 1) =>
      if h : (j : ℕ) < n then g ⟨j, h⟩ i else y i)).col := by
    rw [hcol]
    exact linearIndependent_finSnoc.mpr ⟨hg, hy⟩
  have hunit : IsUnit (Matrix.of (fun i j : Fin (n + 1) =>
      if h : (j : ℕ) < n then g ⟨j, h⟩ i else y i)) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- **The gap principle.**  If `V(Q)` is a hyperplane and `Q ≤ Q' ≤ Q^(1+ε/2)` with `Q` large,
then `V(Q') ≤ V(Q)`. -/
theorem approxSpace_le_of_gap (hN : 2 ≤ N)
    (L : Matrix (Fin N) (Fin N) ℂ) (hL : L.det ≠ 0)
    (γ : Fin N → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (ε : ℝ) (hε : 0 < ε) (hsum : ∑ i, γ i ≤ -ε)
    (Q Q' : ℝ) (hQ1 : 1 ≤ Q) (hle : Q ≤ Q') (hgap : Q' ≤ Q ^ (1 + ε / 2))
    (hbig : (Nat.factorial N : ℝ) < ‖L.det‖ * Q ^ (ε / 2))
    (hr : Module.finrank ℚ (approxSpace L γ Q) = N - 1) :
    approxSpace L γ Q' ≤ approxSpace L γ Q := by
  classical
  obtain ⟨g, hgs, hgli⟩ := exists_fin_box_independent (N - 1) (approxBox L γ Q) (approxSpace L γ Q)
    (by rintro v ⟨y, hy, rfl⟩; exact mem_approxSpace_of_mem_box hy) rfl hr
  -- every point of the larger box lies in `V(Q)`
  have hmem : ∀ y ∈ approxBox L γ Q', intCastVec y ∈ approxSpace L γ Q := by
    intro y hy
    by_contra hnot
    have hspan_sub : Submodule.span ℚ (Set.range (fun j : Fin (N - 1) => intCastVec (g j)))
        ≤ approxSpace L γ Q := by
      rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      exact mem_approxSpace_of_mem_box (hgs j)
    have hnot' : (fun i => (y i : ℚ)) ∉
        Submodule.span ℚ (Set.range (fun j : Fin (N - 1) => fun i => (g j i : ℚ))) :=
      fun hc => hnot (hspan_sub hc)
    have hdetQ : (Matrix.of (fun i j : Fin N =>
        if h : (j : ℕ) < N - 1 then ((g ⟨j, h⟩ i : ℤ) : ℚ) else ((y i : ℤ) : ℚ))).det ≠ 0 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
      exact det_ne_zero_aux (fun j => fun i => ((g j i : ℤ) : ℚ)) (fun i => ((y i : ℤ) : ℚ))
        hgli hnot'
    -- transport to the integer matrix
    have hcast : (Matrix.of (fun i j : Fin N =>
        if h : (j : ℕ) < N - 1 then ((g ⟨j, h⟩ i : ℤ) : ℚ) else ((y i : ℤ) : ℚ)))
        = (Matrix.of (fun i j : Fin N =>
            if h : (j : ℕ) < N - 1 then g ⟨j, h⟩ i else y i)).map (Int.castRingHom ℚ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      by_cases h : (j : ℕ) < N - 1 <;> simp [h]
    have hdetZ : (Matrix.of (fun i j : Fin N =>
        if h : (j : ℕ) < N - 1 then g ⟨j, h⟩ i else y i)).det ≠ 0 := by
      intro hz
      refine hdetQ ?_
      rw [hcast, ← RingHom.mapMatrix_apply (Int.castRingHom ℚ), ← RingHom.map_det (Int.castRingHom ℚ),
        hz, map_zero]
    exact Commons.NumberTheory.DiophantineApproximation.det_eq_zero_of_box_gap_le hN L hL γ hγ1 ε
      hε hsum Q Q' hQ1 hle hgap hbig g y (fun j i => (hgs j) i) (fun i => hy i) hdetZ
  show Submodule.span ℚ (intCastVec '' approxBox L γ Q')
      ≤ Submodule.span ℚ (intCastVec '' approxBox L γ Q)
  apply Submodule.span_le.mpr
  rintro v ⟨y, hy, rfl⟩
  exact hmem y hy

end Submission.Subspace
