import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef

/-!
# The height of any Weyl conjugate of `ρ` in `E₈` is at most `620`

Let `A = CartanMatrix.E₈` and `ρ = ω₁ + ⋯ + ω₈` (the Weyl vector, whose coordinates in the
fundamental-weight basis are all `1`).  The *height* of an integral weight `w` (in the
fundamental-weight basis) is the sum of the coefficients of `w` in the simple-root basis, i.e.

  `e8ht w = ∑ i, (A⁻¹ w) i = ∑ i, ∑ j, E8inv i j * w j`.

Since `ρ` is regular, the set of vectors obtained from `ρ` by folding arbitrary sequences of
simple reflections is exactly the Weyl orbit `W·ρ`.  We show that the height never exceeds the
height of `ρ` itself, which equals the sum of all entries of `A⁻¹`, namely `620`.

The proof is Cauchy–Schwarz for the (positive definite, by `E8_posDef`) quadratic form of `A`.
Writing `u = A⁻¹ w`, we have `height w = δ ⬝ u` and `u ⬝ A u = w ⬝ A⁻¹ w` where `δ = (1,…,1)`;
Cauchy–Schwarz in the form `(x,y) ↦ x ⬝ A y` with `x = A⁻¹ δ` and `y = u` gives

  `(height w)² = (δ ⬝ u)² ≤ (δ ⬝ A⁻¹ δ) (u ⬝ A u) = 620 * (qZ w)`.

The quantity `qZ w = w ⬝ A⁻¹ w` is invariant under simple reflections, hence constant `= 620`
along the fold, and the claim follows.
-/

namespace Commons.LinearAlgebra.Matrix.Cartan

open E8NormTwo

/-- The all-ones weight `ρ = ω₁ + ⋯ + ω₈` (the Weyl vector in the fundamental-weight basis). -/
private def rhoZ : Fin 8 → ℤ := fun _ => 1

/-- `form2 x y = ∑ i, x i * (A y) i` where `A = CartanMatrix.E₈` is read over `ℚ`. -/
private lemma form2_eq_sum_mulVec (x y : Fin 8 → ℚ) :
    form2 x y = ∑ i, x i * (E8q.mulVec y) i := by
  rw [form2]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [E8q, E8NormTwo.E8, Matrix.map_apply, Int.coe_castRingHom]
  ring

/-- The height of `ρ` is `620`, the sum of all entries of the inverse Cartan matrix. -/
private lemma qZ_rhoZ : qZ rhoZ = 620 := by decide

/-- The quadratic form `qZ` is invariant under a fold of simple reflections. -/
private lemma qZ_foldl (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    qZ (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v) = qZ v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [List.foldl_cons, ih]
      exact qZ_refl v i

/-- The pairing of `xc w` with `xc ρ` is the height of `w`. -/
private lemma form2_xc_rho (w : Fin 8 → ℤ) :
    form2 (xc w) (xc rhoZ) = (e8ht w : ℚ) := by
  rw [form2_eq_sum_mulVec, E8q_mul_xc]
  simp only [rhoZ, Int.cast_one, mul_one, e8ht]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [xc]

/-- Cauchy–Schwarz for the positive semidefinite form `form2`. -/
private lemma form2_cauchy (x y : Fin 8 → ℚ) : form2 x y ^ 2 ≤ form2 x x * form2 y y := by
  by_cases hy : y = 0
  · subst hy
    simp [form2]
  · have hypos : 0 < form2 y y := by
      have := E8_posDef y hy
      simpa [form2, E8NormTwo.E8] using this
    have hne : form2 y y ≠ 0 := ne_of_gt hypos
    have hkey : form2 x y ^ 2 / form2 y y ≤ form2 x x := by
      have hnn : 0 ≤ form2 (x - (form2 x y / form2 y y) • y)
          (x - (form2 x y / form2 y y) • y) := form2_nonneg _
      rw [form2_bilin] at hnn
      have hid : form2 x x - 2 * (form2 x y / form2 y y) * form2 x y
          + (form2 x y / form2 y y) ^ 2 * form2 y y
          = form2 x x - form2 x y ^ 2 / form2 y y := by
        field_simp
        ring
      linarith [hnn, hid]
    have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hypos)
    rw [div_mul_cancel₀ _ hne] at hmul
    exact hmul

/-- Any integral weight `w` with `qZ w = 620` has height at most `620`. -/
private lemma e8ht_le_of_qZ (w : Fin 8 → ℤ) (hw : qZ w = 620) : e8ht w ≤ 620 := by
  have hcs := form2_cauchy (xc w) (xc rhoZ)
  rw [form2_xc_rho w, form2_xc_self w, form2_xc_self rhoZ, hw, qZ_rhoZ] at hcs
  have habs : |(e8ht w : ℚ)| ≤ 620 := by
    have h' : (e8ht w : ℚ) ^ 2 ≤ (620 : ℚ) ^ 2 := by
      push_cast at hcs
      nlinarith [hcs]
    have := sq_le_sq.mp h'
    simpa using this
  have hq : (e8ht w : ℚ) ≤ 620 := le_trans (le_abs_self _) habs
  exact_mod_cast hq

theorem E8_weyl_height_bound (L : List (Fin 8)) :
    (∑ i, ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j *
      (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
        (fun _ => (1 : ℤ))) j) ≤ 620 := by
  have hqZ : qZ (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
      (fun _ => (1 : ℤ))) = 620 := by
    rw [qZ_foldl L (fun _ => (1 : ℤ))]
    exact qZ_rhoZ
  have h := e8ht_le_of_qZ _ hqZ
  show e8ht (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
      (fun _ => (1 : ℤ))) ≤ 620
  exact h

end Commons.LinearAlgebra.Matrix.Cartan
