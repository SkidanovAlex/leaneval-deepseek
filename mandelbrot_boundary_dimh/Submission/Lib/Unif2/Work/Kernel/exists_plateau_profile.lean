import Mathlib

open scoped Interval

namespace Work.Kernel

/-- There is a `C^1`, monotone "plateau profile" `Θ : ℝ → ℝ` which is the identity on
`[0, M/4]`, is constantly `M/2` on `[M, ∞)`, and has derivative everywhere in `[0, 1]`.

The profile is obtained by integrating the continuous trapezoidal function
`φ w = min (max 0 ((2/M) * (3M/4 - w))) 1`; then `Θ` is `C^1` with `deriv Θ = φ`, and the
normalisation of the transition region `[M/4, 3M/4]` makes `Θ (3M/4) = M/2`. -/
theorem exists_plateau_profile (M : ℝ) (hM : 0 < M) :
    ∃ Θ : ℝ → ℝ, ContDiff ℝ 1 Θ ∧ Monotone Θ ∧
      (∀ w : ℝ, 0 ≤ w → w ≤ M / 4 → Θ w = w) ∧
      (∀ w : ℝ, M ≤ w → Θ w = M / 2) ∧
      (∀ w : ℝ, 0 ≤ deriv Θ w ∧ deriv Θ w ≤ 1) := by
  have hM0 : (0 : ℝ) < M := hM
  let g : ℝ → ℝ := fun x => (2 / M) * (3 * M / 4 - x)
  let φ : ℝ → ℝ := fun x => min (max 0 (g x)) 1
  have hgc : Continuous g := by
    show Continuous (fun x : ℝ => (2 / M) * (3 * M / 4 - x))
    fun_prop
  have hmaxc : Continuous (fun x : ℝ => max 0 (g x)) := continuous_const.max hgc
  have hφc : Continuous φ := by
    show Continuous (fun x : ℝ => min (max 0 (g x)) 1)
    exact hmaxc.min continuous_const
  have hφ_nonneg : ∀ x, 0 ≤ φ x := fun x => le_min (le_max_left 0 (g x)) zero_le_one
  have hφ_le_one : ∀ x, φ x ≤ 1 := fun x => min_le_right _ _
  have hone : (1 : ℝ) = (2 / M) * (M / 2) := by field_simp
  have hφ_eq_one : ∀ x, x ≤ M / 4 → φ x = 1 := by
    intro x hx
    have h1 : (1 : ℝ) ≤ g x := by
      show (1 : ℝ) ≤ (2 / M) * (3 * M / 4 - x)
      rw [hone]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    show min (max 0 (g x)) 1 = 1
    rw [max_eq_right (by linarith), min_eq_right h1]
  have hφ_eq_zero : ∀ x, 3 * M / 4 ≤ x → φ x = 0 := by
    intro x hx
    have h0 : g x ≤ 0 := by
      show (2 / M) * (3 * M / 4 - x) ≤ 0
      apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
      linarith
    show min (max 0 (g x)) 1 = 0
    rw [max_eq_left h0, min_eq_left zero_le_one]
  have hφ_eq_g : ∀ x, M / 4 ≤ x → x ≤ 3 * M / 4 → φ x = g x := by
    intro x hx1 hx2
    have h0 : 0 ≤ g x := by
      show 0 ≤ (2 / M) * (3 * M / 4 - x)
      apply mul_nonneg (by positivity); linarith
    have h1 : g x ≤ 1 := by
      show (2 / M) * (3 * M / 4 - x) ≤ 1
      rw [hone]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    show min (max 0 (g x)) 1 = g x
    rw [max_eq_right h0, min_eq_left h1]
  let Θ : ℝ → ℝ := fun w => ∫ x in 0..w, φ x
  have hφ_ii : ∀ a b, IntervalIntegrable φ MeasureTheory.volume a b :=
    fun a b => hφc.intervalIntegrable a b
  have hΘderiv : ∀ w, deriv Θ w = φ w := fun w =>
    Continuous.deriv_integral φ hφc 0 w
  have hΘdiff : Differentiable ℝ Θ := fun w =>
    (Continuous.integral_hasStrictDerivAt hφc 0 w).hasDerivAt.differentiableAt
  refine ⟨Θ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨hΘdiff, ?_⟩
    have : deriv Θ = φ := funext hΘderiv
    rw [this]; exact hφc
  · exact monotone_of_deriv_nonneg hΘdiff (fun w => by rw [hΘderiv w]; exact hφ_nonneg w)
  · intro w hw0 hwM
    show (∫ x in 0..w, φ x) = w
    have hcongr : ∫ x in 0..w, φ x = ∫ x in 0..w, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hw0] at hx
      exact hφ_eq_one x (le_trans hx.2 hwM)
    rw [hcongr, intervalIntegral.integral_const]
    simp
  · intro w hwM
    show (∫ x in 0..w, φ x) = M / 2
    have h34 : 3 * M / 4 ≤ M := by linarith
    have h3w : 3 * M / 4 ≤ w := le_trans h34 hwM
    have hsplit : ∫ x in 0..w, φ x = (∫ x in 0..(3 * M / 4), φ x) + ∫ x in (3 * M / 4)..w, φ x :=
      (intervalIntegral.integral_add_adjacent_intervals (hφ_ii 0 (3 * M / 4))
        (hφ_ii (3 * M / 4) w)).symm
    have hzero : ∫ x in (3 * M / 4)..w, φ x = 0 := by
      have hcongr0 : ∫ x in (3 * M / 4)..w, φ x = ∫ x in (3 * M / 4)..w, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h3w] at hx
        exact hφ_eq_zero x hx.1
      rw [hcongr0, intervalIntegral.integral_const]
      simp
    have h34' : M / 4 ≤ 3 * M / 4 := by linarith
    have h0_4 : (0 : ℝ) ≤ M / 4 := by linarith
    have hint1 : ∫ x in 0..(M / 4), φ x = M / 4 := by
      have hcongr : ∫ x in 0..(M / 4), φ x = ∫ x in 0..(M / 4), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h0_4] at hx
        exact hφ_eq_one x hx.2
      rw [hcongr, intervalIntegral.integral_const]; simp
    have hint2 : ∫ x in (M / 4)..(3 * M / 4), φ x = M / 4 := by
      have hcongr : ∫ x in (M / 4)..(3 * M / 4), φ x = ∫ x in (M / 4)..(3 * M / 4), g x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le h34'] at hx
        exact hφ_eq_g x hx.1 hx.2
      rw [hcongr]
      have hderiv : ∀ x ∈ [[M / 4, 3 * M / 4]],
          HasDerivAt (fun y : ℝ => (2 / M) * (3 * M / 4 * y - y ^ 2 / 2)) (g x) x := by
        intro x hx
        show HasDerivAt (fun y : ℝ => (2 / M) * (3 * M / 4 * y - y ^ 2 / 2))
          ((2 / M) * (3 * M / 4 - x)) x
        have h1 : HasDerivAt (fun y : ℝ => (3 * M / 4) * y) (3 * M / 4) x := by
          simpa using (hasDerivAt_id x).const_mul (3 * M / 4)
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          simpa using (hasDerivAt_pow 2 x).div_const 2
        exact (h1.sub h2).const_mul (2 / M)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hgc.intervalIntegrable _ _)]
      field_simp
      ring
    have hval : ∫ x in 0..(3 * M / 4), φ x = M / 2 := by
      have hsplit2 : ∫ x in 0..(3 * M / 4), φ x
          = (∫ x in 0..(M / 4), φ x) + ∫ x in (M / 4)..(3 * M / 4), φ x :=
        (intervalIntegral.integral_add_adjacent_intervals (hφ_ii 0 (M / 4))
          (hφ_ii (M / 4) (3 * M / 4))).symm
      rw [hsplit2, hint1, hint2]
      ring
    rw [hsplit, hval, hzero]
    ring
  · intro w
    rw [hΘderiv w]
    exact ⟨hφ_nonneg w, hφ_le_one w⟩

end Work.Kernel
