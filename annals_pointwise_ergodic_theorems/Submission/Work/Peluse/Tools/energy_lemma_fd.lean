import Mathlib

namespace Work.Peluse.Tools

open scoped BigOperators

/-!
# The energy (Gram / Cauchy–Schwarz) inequality, finite-dimensional case

For a finite family `v : ι → H` of vectors in a complex inner product space and any `w : H`,

  `(∑ i, ‖⟪v i, w⟫‖ ^ 2) ^ 2 ≤ (∑ i, ∑ j, ‖⟪v i, v j⟫‖ ^ 2) * ‖w‖ ^ 4`.

This is the "level-1 interchange" device: it bounds the fourth power of the mass of the
correlations of `w` against the `v i` by the `ℓ²` energy of the Gram matrix of the family.

## Proof (the "test vector" argument)

Put `a i = ⟪v i, w⟫`, `G i j = ⟪v i, v j⟫`, `A = ∑ i, ‖a i‖ ^ 2`, `P = ∑ i, ∑ j, ‖G i j‖ ^ 2`
and let `U = ∑ i, a i • v i` be the associated test vector.  Two elementary inequalities
combine.

* `⟪U, w⟫ = ∑ i, star (a i) * a i = A` is a nonnegative *real* number, so by
  Cauchy–Schwarz `A ≤ ‖U‖ * ‖w‖`.
* Expanding the square of the norm, `⟪U, U⟫ = ∑ i, star (a i) * ∑ j, a j * G i j`, and
  `‖U‖ ^ 2 ≤ ‖⟪U, U⟫‖` (the quantity is a nonnegative real).  The triangle inequality and
  the double-sum Cauchy–Schwarz inequality (`Finset.sum_mul_sq_le_sq_mul_sq`) give

    `‖U‖ ^ 4 ≤ (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖) ^ 2 ≤ P * A ^ 2`.

Multiplying the two bounds, `A ^ 4 ≤ ‖U‖ ^ 4 * ‖w‖ ^ 4 ≤ P * A ^ 2 * ‖w‖ ^ 4`, which is
`A ^ 2 ≤ P * ‖w‖ ^ 4` after cancelling the nonnegative factor `A ^ 2` (the case `A = 0` is
immediate).  -/

/-- `star z * z` is the (nonnegative) real number `‖z‖ ^ 2`, coerced to `ℂ`. -/
private lemma star_mul_self_eq_normSq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, ← Complex.sq_norm]

/-- Cauchy–Schwarz for a double sum over a finite type. -/
private lemma sum_sum_mul_sq_le_sq_mul_sq {ι : Type*} [Fintype ι] (f g : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j * g i j) ^ 2
      ≤ (∑ i, ∑ j, f i j ^ 2) * (∑ i, ∑ j, g i j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (ι := ι × ι) Finset.univ
      (fun p : ι × ι => f p.1 p.2) (fun p : ι × ι => g p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

/-- Energy (Gram/Cauchy–Schwarz) inequality, finite-dimensional case.  Engine of the level-1
interchange device. -/
theorem energy_lemma_fd {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (v : ι → H) (w : H) :
    (∑ i, ‖inner ℂ (v i) w‖ ^ 2) ^ 2
      ≤ (∑ i, ∑ j, ‖inner ℂ (v i) (v j)‖ ^ 2) * ‖w‖ ^ 4 := by
  classical
  let a : ι → ℂ := fun i => inner ℂ (v i) w
  let G : ι → ι → ℂ := fun i j => inner ℂ (v i) (v j)
  let U : H := ∑ i, a i • v i
  let A : ℝ := ∑ i, ‖a i‖ ^ 2
  let P : ℝ := ∑ i, ∑ j, ‖G i j‖ ^ 2
  change A ^ 2 ≤ P * ‖w‖ ^ 4
  have hAval : A = ∑ i, ‖a i‖ ^ 2 := rfl
  have hPval : P = ∑ i, ∑ j, ‖G i j‖ ^ 2 := rfl
  -- `⟪U, w⟫ = A`, a nonnegative real number.
  have hUw : inner ℂ U w = (A : ℂ) := by
    show inner ℂ (∑ i, a i • v i) w = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ)
    rw [sum_inner, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left]
    exact star_mul_self_eq_normSq _
  -- `⟪v i, U⟫ = ∑ j, a j * G i j`.
  have hAU : ∀ i, inner ℂ (v i) U = ∑ j, a j * G i j := by
    intro i
    show inner ℂ (v i) (∑ j, a j • v j) = ∑ j, a j * G i j
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_smul_right]
  -- Cauchy–Schwarz: `A ≤ ‖U‖ * ‖w‖`.
  have hA_le : A ≤ ‖U‖ * ‖w‖ := by
    have h1 : A = (inner ℂ U w).re := by rw [hUw, Complex.ofReal_re]
    rw [h1]
    exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm U w)
  have hA_nonneg : 0 ≤ A := by
    rw [hAval]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- `‖U‖ ^ 2 ≤ ‖⟪U, U⟫‖`.
  have hU2 : ‖U‖ ^ 2 ≤ ‖inner ℂ U U‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) U, RCLike.re_to_complex]
    exact Complex.re_le_norm _
  -- Expansion of `⟪U, U⟫`.
  have hUU : inner ℂ U U = ∑ i, star (a i) * (∑ j, a j * G i j) := by
    have key : inner ℂ U U = ∑ i, (starRingEnd ℂ) (a i) * (∑ j, a j * G i j) := by
      show inner ℂ (∑ i, a i • v i) U = _
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_smul_left, hAU i]
    simpa only [Complex.star_def] using key
  -- Triangle inequality + Cauchy–Schwarz on the double index.
  have htri : ‖inner ℂ U U‖ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖ := by
    rw [hUU]
    calc ‖∑ i, star (a i) * (∑ j, a j * G i j)‖
        ≤ ∑ i, ‖star (a i) * (∑ j, a j * G i j)‖ :=
          norm_sum_le Finset.univ _
      _ = ∑ i, ‖a i‖ * ‖∑ j, a j * G i j‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_mul, norm_star]
      _ ≤ ∑ i, ‖a i‖ * (∑ j, ‖a j‖ * ‖G i j‖) := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖∑ j, a j * G i j‖ ≤ ∑ j, ‖a j * G i j‖ := norm_sum_le Finset.univ _
              _ = ∑ j, ‖a j‖ * ‖G i j‖ := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [norm_mul]
      _ = ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  have hsq : (∑ i, ∑ j, (‖a i‖ * ‖a j‖) ^ 2) = A ^ 2 := by
    rw [hAval, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcs : (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖) ^ 2 ≤ P * A ^ 2 := by
    have h := sum_sum_mul_sq_le_sq_mul_sq (fun i j => ‖a i‖ * ‖a j‖) (fun i j => ‖G i j‖)
    rw [hsq, ← hPval] at h
    calc (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖) ^ 2 ≤ A ^ 2 * P := h
      _ = P * A ^ 2 := by ring
  -- `‖U‖ ^ 4 ≤ P * A ^ 2`.
  have hU4 : ‖U‖ ^ 4 ≤ P * A ^ 2 := by
    calc ‖U‖ ^ 4 = (‖U‖ ^ 2) ^ 2 := by ring
      _ ≤ (∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖G i j‖) ^ 2 :=
            pow_le_pow_left₀ (pow_nonneg (norm_nonneg U) 2) (le_trans hU2 htri) 2
      _ ≤ P * A ^ 2 := hcs
  -- `A ^ 2 ≤ ‖U‖ ^ 2 * ‖w‖ ^ 2`.
  have h1 : A ^ 2 ≤ ‖U‖ ^ 2 * ‖w‖ ^ 2 := by
    calc A ^ 2 ≤ (‖U‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ hA_nonneg hA_le 2
      _ = ‖U‖ ^ 2 * ‖w‖ ^ 2 := by ring
  -- Combine and cancel `A ^ 2`.
  have h2 : A ^ 2 * A ^ 2 ≤ A ^ 2 * (P * ‖w‖ ^ 4) := by
    calc A ^ 2 * A ^ 2 = (A ^ 2) ^ 2 := by ring
      _ ≤ (‖U‖ ^ 2 * ‖w‖ ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg A) h1 2
      _ = ‖U‖ ^ 4 * ‖w‖ ^ 4 := by ring
      _ ≤ (P * A ^ 2) * ‖w‖ ^ 4 := mul_le_mul_of_nonneg_right hU4 (pow_nonneg (norm_nonneg w) 4)
      _ = A ^ 2 * (P * ‖w‖ ^ 4) := by ring
  rcases eq_or_lt_of_le (sq_nonneg A) with heq | hlt
  · rw [← heq]
    exact mul_nonneg
      (by rw [hPval]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
      (pow_nonneg (norm_nonneg w) 4)
  · exact le_of_mul_le_mul_left h2 hlt

end Work.Peluse.Tools
