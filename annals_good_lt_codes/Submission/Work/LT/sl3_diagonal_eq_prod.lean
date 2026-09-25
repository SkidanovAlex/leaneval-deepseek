import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-! # Diagonal matrices of determinant one in `SL₃` as short products of transvections

This file proves `sl3_diagonal_eq_prod`: a diagonal `3 × 3` matrix over `ZMod p` of determinant `1`
is a product of at most `12` elementary matrices `E_ij(t)`, `i ≠ j`.

The mathematical content is the two polynomial (Whitehead-style) identities

* `diagonal ![a, a⁻¹, 1] = E₀₁(a-1) · E₁₀(1) · E₀₁(a⁻¹-1) · E₁₀(-a)`
* `diagonal ![1, u, u⁻¹] = E₁₂(u-1) · E₂₁(1) · E₁₂(u⁻¹-1) · E₂₁(-u)`

for `a, u ≠ 0`, together with the factorisation `diagonal D = diagonal ![a, a⁻¹, 1] *
diagonal ![1, u, u⁻¹]` with `a = D 0`, `u = D 0 * D 1` (so `u⁻¹ = D 2`).  The two identities are
kept as separate, field-general lemmas since they are also useful on their own (e.g. for bounded
generation of `SL₃`). -/

/-- Whitehead-type identity in `SL₃`: the diagonal matrix with entries `a, a⁻¹, 1` is a product of
four transvections. -/
lemma sl3_diag_ab_inv_transvection_prod {F : Type*} [Field F] (a : F) (ha : a ≠ 0) :
    Matrix.diagonal (![a, a⁻¹, 1] : Fin 3 → F) =
      Matrix.transvection (0 : Fin 3) 1 (a - 1) * Matrix.transvection (1 : Fin 3) 0 1 *
      Matrix.transvection (0 : Fin 3) 1 (a⁻¹ - 1) * Matrix.transvection (1 : Fin 3) 0 (-a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transvection, Matrix.diagonal,
      Matrix.one_apply, Matrix.single_apply, Matrix.add_apply]
  all_goals field_simp
  all_goals ring_nf
  all_goals tauto

/-- Whitehead-type identity in `SL₃`: the diagonal matrix with entries `1, u, u⁻¹` is a product of
four transvections. -/
lemma sl3_diag_one_u_inv_transvection_prod {F : Type*} [Field F] (u : F) (hu : u ≠ 0) :
    Matrix.diagonal (![1, u, u⁻¹] : Fin 3 → F) =
      Matrix.transvection (1 : Fin 3) 2 (u - 1) * Matrix.transvection (2 : Fin 3) 1 1 *
      Matrix.transvection (1 : Fin 3) 2 (u⁻¹ - 1) * Matrix.transvection (2 : Fin 3) 1 (-u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transvection, Matrix.diagonal,
      Matrix.one_apply, Matrix.single_apply, Matrix.add_apply]
  all_goals field_simp
  all_goals ring_nf
  all_goals tauto

/-- The underlying matrix of a product of elements of `SLₙ` is the product of the underlying
matrices. -/
lemma slg_val_list_prod {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (l : List (Matrix.SpecialLinearGroup n R)) :
    (l.prod).val = (l.map (fun g => g.val)).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    change a.val * t.prod.val = a.val * (t.map fun g => g.val).prod
    rw [ih]

-- The statement and proof mix the subtype `{A // A.det = 1}` (the definitional unfolding of
-- `SpecialLinearGroup`) with the wrapper type, so defeq checks at *implicit* transparency (used by
-- the matcher of `rw`/`simp`) need to see through `Matrix.SpecialLinearGroup`.  This is the same
-- workaround that Mathlib's own `Matrix/SpecialLinearGroup.lean` uses.
set_option backward.isDefEq.respectTransparency.types false in
/-- A determinant-one diagonal `3 × 3` matrix over `ZMod p` is a product of at most `12`
elementary matrices `E_ij(t)`, `i ≠ j`. Suggested route: `det (diagonal D) = 1` gives
`D 0 * D 1 * D 2 = 1`, so `a := D 0` and `u := D 0 * D 1` are nonzero and
`diagonal D = diagonal ![a, a⁻¹, 1] * diagonal ![1, u, u⁻¹]`; each factor is a product of four
transvections via the polynomial identities
`diagonal ![a, a⁻¹, 1] = transvection 0 1 (a-1) * transvection 1 0 1 * transvection 0 1 (a⁻¹-1)
* transvection 1 0 (-a)`
(and the same with `(0,1) ↦ (1,2)`, `(1,0) ↦ (2,1)`), proved by
`ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three,
Matrix.transvection, Matrix.diagonal, Matrix.one_apply, Matrix.single_apply, Matrix.add_apply]`
followed by `field_simp`/`ring`. Then push through `Subtype.ext` and
`Matrix.SpecialLinearGroup.coe_mul`, using `sl3E p i j t = Matrix.SpecialLinearGroup.transvection
hij t` for `hij : i ≠ j` (both have underlying matrix `Matrix.transvection i j t`). -/
theorem sl3_diagonal_eq_prod (p : ℕ) [Fact p.Prime] (D : Fin 3 → ZMod p)
    (hD : Matrix.det (Matrix.diagonal D) = 1) :
    ∃ l : List (Fin 3 × Fin 3 × ZMod p), l.length ≤ 12 ∧ (∀ x ∈ l, x.1 ≠ x.2.1) ∧
      (⟨Matrix.diagonal D, hD⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) =
        (l.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
  -- `det (diagonal D) = D 0 * D 1 * D 2`, so all three entries are nonzero.
  have hprod : D 0 * D 1 * D 2 = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at hD
    exact hD
  have hnz : D 0 * D 1 * D 2 ≠ 0 := by rw [hprod]; exact one_ne_zero
  have h0 : D 0 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnz).1).1
  have hu : D 0 * D 1 ≠ 0 := (mul_ne_zero_iff.mp hnz).1
  have hD2 : D 2 = (D 0 * D 1)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  -- Split `D` into `(D 0, (D 0)⁻¹, 1)` and `(1, D 0 * D 1, (D 0 * D 1)⁻¹)`.
  have hdec : Matrix.diagonal D =
      Matrix.diagonal (![D 0, (D 0)⁻¹, 1] : Fin 3 → ZMod p) *
      Matrix.diagonal (![1, D 0 * D 1, (D 0 * D 1)⁻¹] : Fin 3 → ZMod p) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hD2, ← mul_assoc, inv_mul_cancel₀ h0]
  refine ⟨[((0 : Fin 3), 1, D 0 - 1), (1, 0, 1), (0, 1, (D 0)⁻¹ - 1), (1, 0, -(D 0)),
      (1, 2, D 0 * D 1 - 1), (2, 1, 1), (1, 2, (D 0 * D 1)⁻¹ - 1), (2, 1, -(D 0 * D 1))],
    ?_, ?_, ?_⟩
  · simp
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> (rw [h]; simp)
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mk, slg_val_list_prod, hdec,
      sl3_diag_ab_inv_transvection_prod (D 0) h0, sl3_diag_one_u_inv_transvection_prod (D 0 * D 1) hu]
    simp [sl3E, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_assoc, mul_one]

end Work.LT
