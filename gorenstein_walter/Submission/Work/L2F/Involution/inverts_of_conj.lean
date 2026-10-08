import Mathlib
import Submission.Work.L2F.Defs

namespace Work.L2F.Involution

open scoped MatrixGroups
open Matrix

/-! ## The commutant of a matrix `X` with `X² = -1` and `det X = 1`

The heart of `inverts_of_conj` is the two-dimensional linear-algebra fact that such a matrix has
commutant exactly spanned by `1` and `X`.  We prove the auxiliary statements here in terms of
`Matrix (Fin 2) (Fin 2) F`. -/

/-- If `X * X = -1` and `det X = 1` then `tr X = 0`: from `X² = -1` one gets
`tr(X²) = -2 = tr(X)² - 2 det X`, hence `tr(X)² = 0`.  Concretely,
`(X₀₀ + X₁₁)² = (X₀₀² + X₀₁X₁₀) + (X₁₀X₀₁ + X₁₁²) + 2(X₀₀X₁₁ - X₀₁X₁₀) = -2 + 2`. -/
private lemma trace_eq_zero {F : Type*} [Field F] (X : Matrix (Fin 2) (Fin 2) F)
    (hX : X * X = -1) (hdetX : X.det = 1) : X 0 0 + X 1 1 = 0 := by
  have h00 := congrFun (congrFun hX 0) 0
  have h11 := congrFun (congrFun hX 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  simp at h00 h11
  rw [Matrix.det_fin_two] at hdetX
  have hsq : (X 0 0 + X 1 1) * (X 0 0 + X 1 1) = 0 := by
    have hid : (X 0 0 + X 1 1) * (X 0 0 + X 1 1) =
        (X 0 0 * X 0 0 + X 0 1 * X 1 0) + (X 1 0 * X 0 1 + X 1 1 * X 1 1)
          + 2 * (X 0 0 * X 1 1 - X 0 1 * X 1 0) := by ring
    rw [hid, h00, h11, hdetX]; norm_num
  exact mul_self_eq_zero.mp hsq

/-- `det (a • 1 + b • X) = a² + b²` when `tr X = 0` and `det X = 1`. -/
private lemma det_smul_one_add {F : Type*} [Field F] (X : Matrix (Fin 2) (Fin 2) F) (a b : F)
    (htr : X 0 0 + X 1 1 = 0) (hdet : X.det = 1) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X).det = a^2 + b^2 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul]
  rw [Matrix.det_fin_two] at hdet
  linear_combination (a*b) * htr + (b^2) * hdet

/-- `(a • 1 + b • X).adjugate = a • 1 - b • X` when `tr X = 0`: the adjugate of
`!![a + bX₀₀, bX₀₁; bX₁₀, a + bX₁₁]` is `!![a + bX₁₁, -bX₀₁; -bX₁₀, a + bX₀₀]`, and this equals
`a • 1 - b • X` precisely because `X₁₁ = -X₀₀`. -/
private lemma adjugate_smul_one_add {F : Type*} [Field F] (X : Matrix (Fin 2) (Fin 2) F) (a b : F)
    (htr : X 0 0 + X 1 1 = 0) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X).adjugate = a • 1 - b • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_two] <;> simp <;> linear_combination b * htr

/-- In `M₂(F)`, `F` a field with `2 ≠ 0`: if `X * X = -1` and `det X = 1`, then every matrix `C`
commuting with `X` lies in `span {1, X}`.  Writing `X = !![p, q; r, s]`, `C = !![m, n; o, t]`,
the commutation relations are `nr = qo`, `q(m - t) + n(s - p) = 0`, `o(p - s) + r(t - m) = 0`,
which are solved by `n = b q`, `o = b r`, `m = a + b p`, `t = a + b s`; the remaining freedom is
settled by a case split on whether `q`, resp. `r`, vanishes (the diagonal case `q = r = 0` has
`s = -p ≠ 0` and needs `2 ≠ 0`). -/
private lemma commutant_span {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (X C : Matrix (Fin 2) (Fin 2) F)
    (hX : X * X = -1) (hdetX : X.det = 1) (hC : C * X = X * C) :
    ∃ a b : F, C = a • 1 + b • X := by
  have hdet' : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdetX; exact hdetX
  have htr : X 0 0 + X 1 1 = 0 := trace_eq_zero X hX hdetX
  have f1 : C 0 1 * X 1 0 = X 0 1 * C 1 0 := by
    have h := congrFun (congrFun hC 0) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  have f2 : X 0 1 * (C 0 0 - C 1 1) + C 0 1 * (X 1 1 - X 0 0) = 0 := by
    have h := congrFun (congrFun hC 0) 1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  have f3 : C 1 0 * (X 0 0 - X 1 1) + X 1 0 * (C 1 1 - C 0 0) = 0 := by
    have h := congrFun (congrFun hC 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h
    linear_combination h
  by_cases hq : X 0 1 = 0
  · by_cases hr : X 1 0 = 0
    · -- diagonal case `X = !![p, 0; 0, -p]`, `C` diagonal
      have hp : X 0 0 ≠ 0 := by
        intro h0
        have hd := hdet'
        rw [h0, zero_mul, hq, hr, mul_zero, sub_zero] at hd
        exact one_ne_zero hd.symm
      have hX1100 : X 1 1 - X 0 0 ≠ 0 := by
        have he : X 1 1 - X 0 0 = -(2 * X 0 0) := by
          have hh : X 1 1 = -(X 0 0) := by linear_combination htr
          rw [hh]; ring
        rw [he]; exact neg_ne_zero.mpr (mul_ne_zero h2 hp)
      have hC01 : C 0 1 = 0 := by
        have h := f2
        rw [hq, zero_mul, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_right hX1100
      have hC10 : C 1 0 = 0 := by
        have h := f3
        rw [hr, zero_mul, add_zero] at h
        have he2 : X 0 0 - X 1 1 ≠ 0 := by
          have he : X 0 0 - X 1 1 = 2 * X 0 0 := by
            have hh : X 1 1 = -(X 0 0) := by linear_combination htr
            rw [hh]; ring
          rw [he]; exact mul_ne_zero h2 hp
        exact (mul_eq_zero.mp h).resolve_right he2
      refine ⟨(C 0 0 + C 1 1) / 2, (C 0 0 - C 1 1) / (2 * X 0 0), ?_⟩
      have h00 : C 0 0 = (((C 0 0 + C 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((C 0 0 - C 1 1) / (2 * X 0 0)) • X) 0 0 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        field_simp
        ring
      have h01 : C 0 1 = (((C 0 0 + C 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((C 0 0 - C 1 1) / (2 * X 0 0)) • X) 0 1 := by
        simp only [Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_eq_mul, mul_zero, zero_add,
          hq, hC01]
      have h10 : C 1 0 = (((C 0 0 + C 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((C 0 0 - C 1 1) / (2 * X 0 0)) • X) 1 0 := by
        simp only [Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, zero_add,
          hr, hC10]
      have h11 : C 1 1 = (((C 0 0 + C 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((C 0 0 - C 1 1) / (2 * X 0 0)) • X) 1 1 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        field_simp
        linear_combination (C 1 1 - C 0 0) * htr
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact h00 | exact h01 | exact h10 | exact h11
    · -- `q = 0`, `r ≠ 0`: use the first row of `X * X = -1` and `C * X = X * C`
      refine ⟨C 0 0 - (C 1 0 / X 1 0) * X 0 0, C 1 0 / X 1 0, ?_⟩
      have hC01 : C 0 1 = 0 := by
        have h := f1
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h).resolve_right hr
      have h00 : C 0 0 = ((C 0 0 - (C 1 0 / X 1 0) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
          + (C 1 0 / X 1 0) • X) 0 0 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        ring
      have h01 : C 0 1 = ((C 0 0 - (C 1 0 / X 1 0) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
          + (C 1 0 / X 1 0) • X) 0 1 := by
        simp only [Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_eq_mul, mul_zero, zero_add,
          hq, hC01]
      have h10 : C 1 0 = ((C 0 0 - (C 1 0 / X 1 0) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
          + (C 1 0 / X 1 0) • X) 1 0 := by
        simp only [Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, zero_add]
        field_simp
      have h11 : C 1 1 = ((C 0 0 - (C 1 0 / X 1 0) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
          + (C 1 0 / X 1 0) • X) 1 1 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        field_simp
        linear_combination f3
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact h00 | exact h01 | exact h10 | exact h11
  · -- `q ≠ 0`: use the first column
    refine ⟨C 0 0 - (C 0 1 / X 0 1) * X 0 0, C 0 1 / X 0 1, ?_⟩
    have h00 : C 0 0 = ((C 0 0 - (C 0 1 / X 0 1) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (C 0 1 / X 0 1) • X) 0 0 := by
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      ring
    have h01 : C 0 1 = ((C 0 0 - (C 0 1 / X 0 1) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (C 0 1 / X 0 1) • X) 0 1 := by
      simp only [Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), smul_eq_mul, mul_zero, zero_add]
      field_simp
    have h10 : C 1 0 = ((C 0 0 - (C 0 1 / X 0 1) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (C 0 1 / X 0 1) • X) 1 0 := by
      simp only [Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, zero_add]
      field_simp
      rw [f1]
      ring
    have h11 : C 1 1 = ((C 0 0 - (C 0 1 / X 0 1) * X 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (C 0 1 / X 0 1) • X) 1 1 := by
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      field_simp
      linear_combination (-1 : F) * f2
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | exact h00 | exact h01 | exact h10 | exact h11

/-- If `x ∈ SL(2,F)` satisfies `x² = -1`, `(2:F) ≠ 0`, and `w x w⁻¹ = -x`, then `w` inverts the
centralizer of `x`: every `c` commuting with `x` is `a • 1 + b • x` for some `a, b` (the pair
`(v, x v)` is a basis for suitable `v ≠ 0`, and a linear map is determined by its values on a
basis), so `w c w⁻¹ = a • 1 + b • (w x w⁻¹) = a • 1 - b • x = c⁻¹`.  (No hypothesis on `w * w`
is needed.) -/
theorem inverts_of_conj (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x w : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1)
    (hw : w * x * w⁻¹ = Work.L2F.negOne F * x) :
    ∀ c ∈ Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      w * c * w⁻¹ = c⁻¹ := by
  intro c hc
  -- `c` commutes with `x` as matrices.
  have hcomm : (c : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hc
    have h' := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) h
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h'
  -- Hence `c = a • 1 + b • x` as matrices.
  obtain ⟨a, b, hab⟩ := commutant_span h2 (x : Matrix (Fin 2) (Fin 2) F)
    (c : Matrix (Fin 2) (Fin 2) F) hx (Matrix.SpecialLinearGroup.det_coe x) hcomm
  have htr : (x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 :=
    trace_eq_zero _ hx (Matrix.SpecialLinearGroup.det_coe x)
  -- `w x w⁻¹ = -x` at the matrix level.
  have hwmat : (w : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
      ((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      -(x : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) hw
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl, neg_one_mul] at h
    exact h
  have hWW : (w : Matrix (Fin 2) (Fin 2) F) *
      ((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
      (t : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel w)
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  -- Conjugation by `w` acts on `a • 1 + b • x` by `x ↦ -x`.
  have hconj : ((w * c * w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = a • 1 - b • (x : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hab]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, hWW, hwmat, smul_neg]
    simp [sub_eq_add_neg]
  -- The matrix `c⁻¹` is the adjugate of `c` (since `det c = 1`), i.e. `a • 1 - b • x`.
  have hcinv : ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = a • 1 - b • (x : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hab]
    exact adjugate_smul_one_add _ a b htr
  apply Subtype.ext
  rw [hconj, hcinv]

end Work.L2F.Involution
