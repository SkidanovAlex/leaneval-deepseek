import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

/-!
# Uniform ellipticity is open in the uniform norm

If the real part of a matrix-valued torus function `u : Torus n` satisfies the uniform ellipticity
bound `lam * ‖v‖² ≤ ∑ᵢⱼ (reMat (u x))ᵢⱼ vᵢ vⱼ` at *every* point `x` of the torus (with `lam > 0`),
then any `w` whose entries are uniformly `ε`-close to those of `u` (in the supremum norm on
`MatC n`) still satisfies the bound with constant `lam / 2`, for `ε := lam / (2 * n)`.

The proof is the elementary `n²`-term estimate: the perturbation of the quadratic form by a matrix
with entries bounded by `ε` is at most `ε * n * ‖v‖²`, by Cauchy–Schwarz and the triangle
inequality.
-/

/-- The Cauchy–Schwarz bound `(∑ᵢ |vᵢ|)² ≤ n * ∑ᵢ vᵢ²` for a real vector indexed by `Fin n`. -/
lemma sum_abs_sq_le_card_mul_sum_sq (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) (fun i => |v i|)
    (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  simp only [sq_abs] at h
  linarith [h]

/-- The perturbation bound for a real quadratic form: if every entry of `D` is bounded by `e` in
absolute value then `|∑ᵢⱼ Dᵢⱼ vᵢ vⱼ| ≤ e * n * ∑ᵢ vᵢ²`. -/
lemma abs_quadForm_entrywise_le {n : ℕ} {e : ℝ} (he : 0 ≤ e) (D : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) (hD : ∀ i j, |D i j| ≤ e) :
    |∑ i, ∑ j, D i j * v i * v j| ≤ e * (n : ℝ) * ∑ i, (v i) ^ 2 := by
  have h1 : |∑ i, ∑ j, D i j * v i * v j| ≤ ∑ i, ∑ j, |D i j * v i * v j| := by
    calc |∑ i, ∑ j, D i j * v i * v j|
        ≤ ∑ i, |∑ j, D i j * v i * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |D i j * v i * v j| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have h2 : ∑ i, ∑ j, |D i j * v i * v j| ≤ ∑ i, ∑ j, e * |v i| * |v j| := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hD i j) (abs_nonneg _)) (abs_nonneg _)
  have h3 : (∑ i, ∑ j, e * |v i| * |v j|) = e * (∑ i, |v i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  calc |∑ i, ∑ j, D i j * v i * v j| ≤ ∑ i, ∑ j, |D i j * v i * v j| := h1
    _ ≤ ∑ i, ∑ j, e * |v i| * |v j| := h2
    _ = e * (∑ i, |v i|) ^ 2 := h3
    _ ≤ e * ((n : ℝ) * ∑ i, (v i) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_abs_sq_le_card_mul_sum_sq n v) he
    _ = e * (n : ℝ) * ∑ i, (v i) ^ 2 := by ring

theorem posDef_of_uniform_close {n : ℕ} (u : Work.Diff.STE.Flat.Torus n)
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u x) i j * v i * v j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : Work.Diff.STE.Flat.Torus n,
      (∀ x : Fin n → ℝ, ‖w x - u x‖ ≤ ε) →
      ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (w x) i j * v i * v j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun w _ x v => ?_⟩
    simp
  · have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    set ε : ℝ := lam / (2 * (n : ℝ)) with hε
    have hεpos : 0 < ε := by rw [hε]; positivity
    refine ⟨ε, hεpos, fun w hw x v => ?_⟩
    -- entrywise bound on the perturbation of the matrix of `u x` by that of `w x`
    have hDd : ∀ i j, |reMat (w x) i j - reMat (u x) i j| ≤ ε := by
      intro i j
      have h1 : (w x i j).re - (u x i j).re = (w x i j - u x i j).re := by simp
      rw [reMat_apply, reMat_apply, h1]
      calc |(w x i j - u x i j).re| ≤ ‖w x i j - u x i j‖ := Complex.abs_re_le_norm _
        _ ≤ ‖w x - u x‖ := by
            have h2 : ‖(w x - u x) i j‖ = ‖w x i j - u x i j‖ := by simp
            rw [← h2]
            exact (norm_le_pi_norm ((w x - u x) i) j).trans (norm_le_pi_norm (w x - u x) i)
        _ ≤ ε := hw x
    -- split the quadratic form of `w x` into that of `u x` plus the perturbation
    have hsplit : (∑ i, ∑ j, reMat (w x) i j * v i * v j)
        = (∑ i, ∑ j, reMat (u x) i j * v i * v j)
          + ∑ i, ∑ j, (reMat (w x) i j - reMat (u x) i j) * v i * v j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have hR := abs_quadForm_entrywise_le (le_of_lt hεpos)
      (fun i j => reMat (w x) i j - reMat (u x) i j) v hDd
    have hen : ε * (n : ℝ) = lam / 2 := by
      rw [hε]; field_simp
    have h3 : ε * (n : ℝ) * ∑ i, (v i) ^ 2 = (lam / 2) * ∑ i, (v i) ^ 2 := by
      rw [hen]
    rw [hsplit]
    linarith [hell x v, (abs_le.mp hR).1, h3]

end Work.Diff.STE.flat
