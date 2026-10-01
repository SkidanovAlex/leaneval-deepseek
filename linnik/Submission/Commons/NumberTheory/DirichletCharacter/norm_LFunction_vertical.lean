import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex DirichletCharacter
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- The value of a Dirichlet character at a natural number (viewed modulo `N`) has
norm at most `1`. -/
private lemma norm_char_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 :=
  DirichletCharacter.norm_le_one χ (n : ZMod N)

/-- For `σ > 1` the `n`-th term of the Dirichlet L-series is bounded in norm by the
corresponding term of the Riemann zeta series (the constant-one L-series at `σ`), uniformly
in `t`. -/
private lemma norm_term_char_le_norm_term_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} {t : ℝ} (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦ (χ (m : ZMod N) : ℂ)) (σ + Complex.I * (t : ℂ)) n‖ ≤
      ‖LSeries.term (fun _ : ℕ ↦ (1 : ℂ)) (σ : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rw [show (σ + Complex.I * (t : ℂ)).re = σ by simp]
  rw [show ((σ : ℂ)).re = σ by simp]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    have hd : 0 ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
    exact div_le_div_of_nonneg_right (by simpa using norm_char_le_one χ n) hd

/-- `|L(σ + I t, χ)|` is bounded uniformly in `t` for `1 < σ`. -/
theorem norm_LFunction_vertical {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖LFunction χ (σ + Complex.I * (t : ℂ))‖ ≤ B := by
  classical
  let g : ℕ → ℂ := fun m : ℕ ↦ (χ (m : ZMod N) : ℂ)
  let oneC : ℕ → ℂ := fun _ : ℕ ↦ (1 : ℂ)
  let B : ℝ := ∑' n : ℕ, ‖LSeries.term oneC (σ : ℂ) n‖
  refine ⟨B, ?hB0, ?bound⟩
  · dsimp [B]
    exact tsum_nonneg (fun n ↦ norm_nonneg _)
  · intro t
    let s : ℂ := σ + Complex.I * (t : ℂ)
    have hre : s.re = σ := by simp [s]
    have hs : 1 < s.re := by simpa [hre] using hσ
    have hs1 : 1 < (σ : ℂ).re := by simpa using hσ
    have hsumg : LSeriesSummable g s := by
      refine LSeriesSummable_of_bounded_of_one_lt_re (f := g) (m := 1) ?_ hs
      intro n _hn
      dsimp [g]
      exact norm_char_le_one χ n
    have hsum1 : LSeriesSummable oneC (σ : ℂ) := by
      refine LSeriesSummable_of_bounded_of_one_lt_re (f := oneC) (m := 1) ?_ hs1
      intro n _hn
      dsimp [oneC]
      simp
    calc
      ‖LFunction χ s‖ = ‖LSeries (fun x : ℕ ↦ (χ (x : ZMod N) : ℂ)) s‖ := by
        rw [LFunction_eq_LSeries χ hs]
      _ = ‖LSeries g s‖ := by rfl
      _ = ‖∑' n : ℕ, LSeries.term g s n‖ := by rfl
      _ ≤ ∑' n : ℕ, ‖LSeries.term g s n‖ := by
        exact norm_tsum_le_tsum_norm (f := fun n : ℕ ↦ LSeries.term g s n) hsumg.norm
      _ ≤ B := by
        dsimp [B]
        refine Summable.tsum_le_tsum ?_ hsumg.norm hsum1.norm
        intro n
        dsimp [g, oneC]
        exact norm_term_char_le_norm_term_one χ n

end Commons.NumberTheory.DirichletCharacter