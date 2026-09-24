import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- For a non-prime `i` with `1 ≤ i`, the factor `(log i)⁻¹` has modulus at most `1`:
`i = 1` contributes `0`, and any other non-prime `i ≥ 2` is a composite, hence `i ≥ 4`
and `log i ≥ 1`. -/
theorem inv_log_norm_le_one_of_not_prime {i : ℕ} (hi : 1 ≤ i) (hinp : ¬ i.Prime) :
    ‖(((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    simp [Real.log_one]
  · have hne2 : i ≠ 2 := fun hh => hinp (hh ▸ Nat.prime_two)
    have hne3 : i ≠ 3 := fun hh => hinp (hh ▸ Nat.prime_three)
    have hi4 : 4 ≤ i := by omega
    have hlog1 : (1 : ℝ) ≤ Real.log (i : ℝ) := by
      rw [Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < i))]
      have h4 : (4 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi4
      linarith [Real.exp_one_lt_three]
    have hpos : 0 ≤ (Real.log (i : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
    exact inv_le_one_of_one_le₀ hlog1

/-- The character-weighted von Mangoldt sum over non-primes with the weight `(log i)⁻¹`
is bounded by the constant `Cpp` controlling the plain von Mangoldt sum over non-primes.
Indeed each summand has modulus at most `Λ i`, since `‖χ‖ ≤ 1` and `(log i)⁻¹ ≤ 1` for
non-prime `i ≥ 1`. -/
theorem chiLambdaNonprimeSumBound (Cpp : ℝ)
    (hCpp : ∀ t : ℕ, (∑ n ∈ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n) ≤ Cpp * Real.sqrt (t : ℝ))
    (c t : ℕ) (χ : DirichletCharacter ℂ c) :
    ‖∑ i ∈ (Finset.Icc 1 t).filter (fun i => ¬ i.Prime),
        χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) *
          (((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ Cpp * Real.sqrt (t : ℝ) := by
  set s := (Finset.Icc 1 t).filter (fun i => ¬ i.Prime) with hs
  have hterm : ∀ i ∈ s, ‖χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) *
      (((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖ ≤ (ArithmeticFunction.vonMangoldt i : ℝ) := by
    intro i hi
    rw [hs] at hi
    obtain ⟨hiIcc, hinp⟩ := Finset.mem_filter.mp hi
    rw [Finset.mem_Icc] at hiIcc
    rw [norm_mul, norm_mul]
    have hchi : ‖χ (i : ZMod c)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hLam : ‖((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ)‖ =
        (ArithmeticFunction.vonMangoldt i : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hw := inv_log_norm_le_one_of_not_prime hiIcc.1 hinp
    rw [hLam]
    calc ‖χ (i : ZMod c)‖ * ArithmeticFunction.vonMangoldt i *
          ‖(((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖
        ≤ 1 * ArithmeticFunction.vonMangoldt i * 1 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hchi ArithmeticFunction.vonMangoldt_nonneg
          · exact hw
          · exact norm_nonneg _
          · exact mul_nonneg zero_le_one ArithmeticFunction.vonMangoldt_nonneg
      _ = ArithmeticFunction.vonMangoldt i := by ring
  have hsub : s ⊆ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime) := by
    rw [hs]
    exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) le_rfl)
  have h2 : ∑ i ∈ s, (ArithmeticFunction.vonMangoldt i : ℝ)
      ≤ ∑ n ∈ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  calc ‖∑ i ∈ s, χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) *
          (((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖
      ≤ ∑ i ∈ s, ‖χ (i : ZMod c) * ((ArithmeticFunction.vonMangoldt i : ℝ) : ℂ) *
          (((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (ArithmeticFunction.vonMangoldt i : ℝ) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ (Finset.Icc 0 t).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n := h2
    _ ≤ Cpp * Real.sqrt (t : ℝ) := hCpp t

end Work.NumberTheory.Chen.BTermCount
