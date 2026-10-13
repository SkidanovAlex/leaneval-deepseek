import Mathlib

/-!
  `Work.WilE7.FrontierCS.exists_smul_add_det_ne_zero`.

  For square real matrices `M`, `N` of size `j × j` there is a real number `a` such that both
  `det (M + a • 1)` and `det (1 + a • N)` are nonzero.

  The argument is the standard one: `a ↦ det (1 + a • N)` is the evaluation of the nonzero
  polynomial `det (1 + X • N.map C)` (which takes the value `1` at `a = 0`, as its constant
  term is `det 1 = 1`), hence has finitely many zeros.  For the other factor we use the identity
  `det (M + a • 1) = a ^ j * det (1 + a⁻¹ • M)` valid for `a ≠ 0`, which shows that its zero set
  lies in `{0} ∪ (·⁻¹) '' {b | det (1 + b • M) = 0}`, again finite.  A finite union of finite
  sets cannot exhaust `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Matrix Polynomial

namespace Work.WilE7.FrontierCS

/-- Evaluation of the determinant of a polynomial matrix: evaluating the entries of `A` at `a`
and then taking the determinant agrees with evaluating the determinant of `A`. -/
private lemma eval_det_map {j : ℕ} (A : Matrix (Fin j) (Fin j) (Polynomial ℝ)) (a : ℝ) :
    (A.det).eval a = (A.map (Polynomial.eval a)).det := by
  rw [eval_det, matPolyEquiv_eval_eq_map]

/-- Entrywise evaluation of `1 + X • (C.map C)` at `a` is `1 + a • C`. -/
private lemma map_one_add_X_smul {j : ℕ} (C : Matrix (Fin j) (Fin j) ℝ) (a : ℝ) :
    ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C).map (Polynomial.eval a)
      = 1 + a • C := by
  ext i k
  by_cases h : i = k <;>
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_zero, Polynomial.eval_one, h, ↓reduceIte, smul_eq_mul]

/-- The polynomial `det (1 + X • N.map C)` evaluated at `a` is `det (1 + a • N)`. -/
private lemma eval_det_one_add_smul {j : ℕ} (C : Matrix (Fin j) (Fin j) ℝ) (a : ℝ) :
    ((det ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C))).eval a
      = (1 + a • C).det := by
  rw [eval_det_map, map_one_add_X_smul]

/-- The polynomial `det (1 + X • N.map C)` is nonzero, since `det (1 + 0 • C) = det 1 = 1`. -/
private lemma det_one_add_X_smul_ne_zero {j : ℕ} (C : Matrix (Fin j) (Fin j) ℝ) :
    (det ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C)) ≠ 0 := by
  intro h
  have h1 : ((det ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C))).eval 0 = 1 := by
    rw [eval_det_one_add_smul C 0]
    simp
  rw [h] at h1
  simp at h1

/-- For a square matrix `C`, the set of `a` with `det (1 + a • C) = 0` is finite. -/
private lemma finite_det_one_add_smul {j : ℕ} (C : Matrix (Fin j) (Fin j) ℝ) :
    {a : ℝ | (1 + a • C).det = 0}.Finite := by
  have hne : (det ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C)) ≠ 0 :=
    det_one_add_X_smul_ne_zero C
  have heq : {a : ℝ | (1 + a • C).det = 0}
      = {a : ℝ | (det ((1 : Matrix (Fin j) (Fin j) (Polynomial ℝ))
        + (Polynomial.X : Polynomial ℝ) • C.map Polynomial.C)).IsRoot a} := by
    ext a
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot]
    rw [eval_det_one_add_smul]
  rw [heq]
  exact Polynomial.finite_setOfPred_isRoot hne

/-- For `a ≠ 0`, `det (M + a • 1) = a ^ j * det (1 + a⁻¹ • M)`. -/
private lemma det_add_smul_one {j : ℕ} (M : Matrix (Fin j) (Fin j) ℝ) {a : ℝ} (ha : a ≠ 0) :
    (M + a • 1).det = a ^ j * (1 + a⁻¹ • M).det := by
  have h : M + a • 1 = a • (1 + a⁻¹ • M) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul, add_comm]
  rw [h, Matrix.det_smul, Fintype.card_fin]

/-- For a square matrix `M`, the set of `a` with `det (M + a • 1) = 0` is finite. -/
private lemma finite_det_add_smul_one {j : ℕ} (M : Matrix (Fin j) (Fin j) ℝ) :
    {a : ℝ | (M + a • 1).det = 0}.Finite := by
  have hfin := finite_det_one_add_smul M
  have hsub : {a : ℝ | (M + a • 1).det = 0}
      ⊆ insert 0 ((fun b : ℝ => b⁻¹) '' {b : ℝ | (1 + b • M).det = 0}) := by
    intro a ha
    by_cases h0 : a = 0
    · exact Set.mem_insert_iff.mpr (Or.inl h0)
    · rw [Set.mem_insert_iff]
      right
      rw [Set.mem_image]
      refine ⟨a⁻¹, ?_, inv_inv a⟩
      simp only [Set.mem_ofPred_eq] at ha ⊢
      have hdet := det_add_smul_one M h0
      rw [ha] at hdet
      have hp : a ^ j ≠ 0 := pow_ne_zero j h0
      rcases mul_eq_zero.mp hdet.symm with h | h
      · exact absurd h hp
      · exact h
  exact ((hfin.image (fun b : ℝ => b⁻¹)).insert 0).subset hsub

theorem exists_smul_add_det_ne_zero {j : ℕ} (M N : Matrix (Fin j) (Fin j) ℝ) :
    ∃ a : ℝ, (M + a • 1).det ≠ 0 ∧ (1 + a • N).det ≠ 0 := by
  have hB : ({a : ℝ | (M + a • 1).det = 0} ∪ {a : ℝ | (1 + a • N).det = 0}).Finite :=
    (finite_det_add_smul_one M).union (finite_det_one_add_smul N)
  obtain ⟨a, ha⟩ := hB.exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at ha
  exact ⟨a, ha⟩

end Work.WilE7.FrontierCS
