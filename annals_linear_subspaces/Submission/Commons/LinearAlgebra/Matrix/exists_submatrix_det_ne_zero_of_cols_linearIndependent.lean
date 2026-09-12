import Mathlib.Analysis.Normed.Field.Lemmas
import Submission.Commons.LinearAlgebra.Matrix.exists_det_ne_zero_of_rank_ge

open Matrix
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

private lemma qprod_erase_mul {r : ℕ} (c : Fin r → ℚ) (j : Fin r) :
    (∏ k ∈ (Finset.univ.erase j), ((c k).den : ℚ)) * ((c j).den : ℚ) =
      (∏ k : Fin r, ((c k).den : ℚ)) := by
  simpa using (Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
    (fun k : Fin r => ((c k).den : ℚ)) (a := j) (Finset.mem_univ j))

/-- For a rational coefficient `c j` and the product `D` of all denominators appearing
in the family `c`, the rational number `num j * (D / den j)` equals `D * c j`. -/
private lemma zq_scaled {r : ℕ} (c : Fin r → ℚ) (j : Fin r) :
    (((c j).num : ℚ) * (∏ k ∈ (Finset.univ.erase j), ((c k).den : ℚ))) =
      (∏ k : Fin r, ((c k).den : ℚ)) * c j := by
  have hden : ((c j).den : ℚ) ≠ 0 := by exact_mod_cast (c j).den_ne_zero
  have hcj : c j * ((c j).den : ℚ) = (c j).num :=
    (eq_div_iff hden).mp (Rat.num_div_den (c j)).symm
  let P : ℚ := (∏ k ∈ (Finset.univ.erase j), ((c k).den : ℚ))
  let D : ℚ := (∏ k : Fin r, ((c k).den : ℚ))
  apply mul_right_cancel₀ hden
  calc
    ((c j).num : ℚ) * P * ((c j).den : ℚ)
        = ((c j).num : ℚ) * (P * ((c j).den : ℚ)) := by ring
    _ = ((c j).num : ℚ) * D := by rw [show P * ((c j).den : ℚ) = D from qprod_erase_mul c j]
    _ = D * ((c j).num : ℚ) := by ring
    _ = D * c j * ((c j).den : ℚ) := by
          rw [← hcj]
          ring

/-- Linear independence over `ℤ` of a family of integer vectors implies linear
independence over `ℚ` of their rational casts. -/
private lemma rat_linIndep_of_int {n r : ℕ} (w : Fin r → Fin n → ℤ)
    (h : LinearIndependent ℤ w) :
    LinearIndependent ℚ (fun j : Fin r => fun i : Fin n => (w j i : ℚ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let v : Fin r → (Fin n → ℚ) := fun j i => (w j i : ℚ)
  change (∑ j : Fin r, c j • v j) = 0 at hc
  let dz : Fin r → ℤ := fun j => (∏ k ∈ (Finset.univ.erase j), ((c k).den : ℤ))
  let z : Fin r → ℤ := fun j => (c j).num * dz j
  let D : ℤ := ∏ k : Fin r, ((c k).den : ℤ)
  have hD0 : D ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact_mod_cast (c k).den_ne_zero
  have hDq : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hD0
  -- (z j : ℚ) = (D : ℚ) * c j
  have hzq : ∀ j : Fin r, (z j : ℚ) = ((D : ℤ) : ℚ) * c j := by
    intro j
    have h1 := zq_scaled c j
    dsimp [z, dz, D] at h1 ⊢
    simpa [Int.cast_mul] using h1
  -- rational relation with integer coefficients `z`
  have hzrel : (∑ j : Fin r, (z j : ℚ) • v j) = 0 := by
    have hsmul := congrArg (fun f : Fin n → ℚ => ((D : ℤ) : ℚ) • f) hc
    rw [Finset.smul_sum] at hsmul
    have hstep : (∑ j : Fin r, (((D : ℤ) : ℚ) * c j) • v j) = 0 := by
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsmul
    simpa [hzq] using hstep
  -- per-coordinate integer sums
  have hzi : ∀ i : Fin n, (∑ j : Fin r, z j * w j i) = 0 := by
    intro i
    have hqi := congrFun hzrel i
    have hcoord : (∑ j : Fin r, (z j : ℚ) * (w j i : ℚ)) = 0 := by
      simpa [v, Pi.smul_apply, Finset.sum_apply] using hqi
    have hcoord2 : (∑ j : Fin r, ((z j * w j i : ℤ) : ℚ)) = 0 := by
      have hconv : (∑ j : Fin r, ((z j * w j i : ℤ) : ℚ)) =
          ∑ j : Fin r, (z j : ℚ) * (w j i : ℚ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Int.cast_mul (z j) (w j i)
      rw [hconv]
      exact hcoord
    have hcoord3 : (((∑ j : Fin r, (z j * w j i : ℤ)) : ℤ) : ℚ) = 0 := by
      simpa using hcoord2
    exact_mod_cast hcoord3
  -- integer relation, so ℤ-linear independence gives `z = 0`
  have hzint : (∑ j : Fin r, z j • w j) = 0 := by
    funext i
    simp [Finset.sum_apply, hzi i]
  have hz0 : ∀ j : Fin r, z j = 0 := Fintype.linearIndependent_iff.mp h z hzint
  -- conclude `c i = 0`
  have hDci : ((D : ℤ) : ℚ) * c i = 0 := by
    rw [← hzq i]
    simp [hz0 i]
  exact (mul_eq_zero.mp hDci).resolve_left hDq

theorem exists_submatrix_det_ne_zero_of_cols_linearIndependent
    {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (h : LinearIndependent ℤ A.col) :
    ∃ e : Fin r ↪ Fin n, (A.submatrix e (fun j : Fin r => j)).det ≠ 0 := by
  classical
  -- work over ℚ
  let B : Matrix (Fin n) (Fin r) ℚ := A.map (fun z : ℤ => (z : ℚ))
  have hBcol : LinearIndependent ℚ B.col := by
    have hw := rat_linIndep_of_int A.col h
    change LinearIndependent ℚ (fun j : Fin r => fun i : Fin n => (B i j))
    simpa [B] using hw
  -- rank of `B` is `r`
  have hBrank : B.rank = r := by
    rw [B.rank_eq_finrank_span_cols]
    rw [finrank_span_eq_card hBcol]
    simp
  -- row space has dimension at least `r`
  have hrow : r ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range B.row)) := by
    rw [← B.rank_eq_finrank_span_row]
    rw [hBrank]
  -- pick `r` linearly independent rows
  obtain ⟨e, herow⟩ := exists_linearIndependent_comp_fin B.row hrow
  -- the square submatrix formed by these rows has linearly independent rows
  let Q : Matrix (Fin r) (Fin r) ℚ := B.submatrix e (fun j : Fin r => j)
  have hQrow : LinearIndependent ℚ Q.row := by
    have hfam : (B.submatrix e (fun j : Fin r => j)).row = B.row ∘ e := by
      ext i j
      simp [Matrix.row_apply]
    simpa [Q, hfam] using herow
  have hQunit : IsUnit Q := Matrix.linearIndependent_rows_iff_isUnit.mp hQrow
  have hQdet : Q.det ≠ 0 := by
    have hu := (Matrix.isUnit_iff_isUnit_det Q).mp hQunit
    exact (isUnit_iff_ne_zero.mp hu)
  -- transfer back to the integer matrix
  refine ⟨e, ?_⟩
  let P : Matrix (Fin r) (Fin r) ℤ := A.submatrix e (fun j : Fin r => j)
  change P.det ≠ 0
  have hPQ : Q = P.map (fun z : ℤ => (z : ℚ)) := by
    simp [Q, P, B, Matrix.submatrix_map]
  have hPdetQ : ((P.det : ℤ) : ℚ) = Q.det := by
    rw [Int.cast_det]
    exact congrArg Matrix.det hPQ.symm
  intro hP0
  have hQ0 : Q.det = 0 := by
    rw [← hPdetQ]
    exact_mod_cast hP0
  exact hQdet hQ0

end Commons.LinearAlgebra.Matrix