import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Avalanche.dframe
import Submission.Work.TMC7Core.Avalanche.rownorm
import Submission.Work.TMC7Core.Avalanche.chain_gram
import Submission.Work.TMC7Core.Avalanche.ratio_bound_num

/-!
# The analytic core of the avalanche principle, via row norms

Let `s : ℕ → ℝ` (the singular values, `s j ≥ 1`) and `W : ℕ → Matrix (Fin 2) (Fin 2) ℂ` (the
unitaries `W j = V (j+1)ᴴ · U j`), and put `N k = D k · W (k-1) ⋯ W 0 · D 0`.  We estimate
`frob (N (n-1))` by following the two *Euclidean row norms*

  `rA k = ‖rowE (N k) 0‖`,  `rB k = ‖rowE (N k) 1‖`

of the truncated product.  The invariant is that the second row stays much smaller than the
first (`rB k ≤ η · rA k` with `η = 2/μ^{3/2}`), which makes the diagonal weighting by
`Dm (s k)` almost optimal at every step.
-/

set_option maxHeartbeats 1600000

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-! ## Notation -/

/-- Euclidean norm of the first row of the truncated product `N k`. -/
def rA (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ :=
  ‖rowE (Nmat s W k) 0‖

/-- Euclidean norm of the second row of the truncated product `N k`. -/
def rB (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ :=
  ‖rowE (Nmat s W k) 1‖

/-- `‖W k 0 0‖`, the leading entry of the `k`-th unitary. -/
def lamW (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ := ‖W k 0 0‖

/-- `‖W k 0 1‖`, the off-diagonal entry of the `k`-th unitary. -/
def rhoW (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ := ‖W k 0 1‖

lemma rA_nonneg (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : 0 ≤ rA s W k :=
  norm_nonneg _

lemma rB_nonneg (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : 0 ≤ rB s W k :=
  norm_nonneg _

lemma rA_sq_add_rB_sq (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    frob (Nmat s W k) ^ 2 = rA s W k ^ 2 + rB s W k ^ 2 := by
  rw [frob_sq_eq_rowE]
  rfl

lemma lamW_nonneg (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : 0 ≤ lamW W k :=
  norm_nonneg _

lemma rhoW_nonneg (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : 0 ≤ rhoW W k :=
  norm_nonneg _

lemma lamW_sq_add_rhoW_sq (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hW : W k * (W k).conjTranspose = 1) : lamW W k ^ 2 + rhoW W k ^ 2 = 1 := by
  have h := unitary_entry01_sq (W k) hW
  simp only [lamW, rhoW]
  linarith

lemma lamW_sq_le_one (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hW : W k * (W k).conjTranspose = 1) : lamW W k ^ 2 ≤ 1 := by
  have h := lamW_sq_add_rhoW_sq W k hW
  nlinarith [rhoW_nonneg W k]

/-! ## The recursion of the two row norms -/

lemma rA_succ (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) (hs : 0 ≤ s (k + 1)) :
    rA s W (k + 1) = s (k + 1) * ‖rowE (W k * Nmat s W k) 0‖ := by
  rw [rA, Nmat_succ]
  rw [mul_assoc, norm_rowE_Dm_mul_row0 _ hs]

lemma rB_succ (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) (hs : 0 ≤ s (k + 1)) :
    rB s W (k + 1) = (s (k + 1))⁻¹ * ‖rowE (W k * Nmat s W k) 1‖ := by
  rw [rB, Nmat_succ]
  rw [mul_assoc, norm_rowE_Dm_mul_row1 _ hs]

/-! Entry identifications for a unitary block -/

lemma entry10_eq_rhoW (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hW : W k * (W k).conjTranspose = 1) (hW' : (W k).conjTranspose * W k = 1) :
    ‖W k 1 0‖ = rhoW W k := by
  have h1 := unitary_entry01_sq (W k) hW
  have h2 : ‖W k 1 0‖ ^ 2 = ‖W k 0 1‖ ^ 2 := by
    rw [unitary_entry10_sq (W k) hW', h1]
  have h3 : ‖W k 1 0‖ = ‖W k 0 1‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · linarith [norm_nonneg (W k 1 0), norm_nonneg (W k 0 1)]
  exact h3

lemma entry11_eq_lamW (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hW : W k * (W k).conjTranspose = 1) (hW' : (W k).conjTranspose * W k = 1) :
    ‖W k 1 1‖ = lamW W k := by
  have h2 : ‖W k 1 1‖ ^ 2 = ‖W k 0 0‖ ^ 2 := unitary_entry11_sq (W k) hW' hW
  have h3 : ‖W k 1 1‖ = ‖W k 0 0‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact h
    · linarith [norm_nonneg (W k 1 1), norm_nonneg (W k 0 0)]
  exact h3

lemma rA_succ_le (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 ≤ s (k + 1)) :
    rA s W (k + 1) ≤ s (k + 1) * (lamW W k * rA s W k + rhoW W k * rB s W k) := by
  rw [rA_succ s W k hs]
  have h := rowE_mul_row0_le (W k) (Nmat s W k)
  simp only [lamW, rhoW, rA, rB] at h ⊢
  nlinarith [h, hs]

lemma rA_succ_ge (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 ≤ s (k + 1)) :
    s (k + 1) * (lamW W k * rA s W k - rhoW W k * rB s W k) ≤ rA s W (k + 1) := by
  rw [rA_succ s W k hs]
  have h := rowE_mul_row0_ge (W k) (Nmat s W k)
  simp only [lamW, rhoW, rA, rB] at h ⊢
  nlinarith [h, hs]

lemma rB_succ_le (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 ≤ s (k + 1)) (hW : W k * (W k).conjTranspose = 1)
    (hW' : (W k).conjTranspose * W k = 1) :
    rB s W (k + 1) ≤ (s (k + 1))⁻¹ * (rhoW W k * rA s W k + lamW W k * rB s W k) := by
  rw [rB_succ s W k hs]
  have h := rowE_mul_row1_le (W k) (Nmat s W k)
  rw [entry10_eq_rhoW W k hW hW', entry11_eq_lamW W k hW hW'] at h
  have hi := inv_nonneg.mpr hs
  simp only [rA, rB] at h ⊢
  nlinarith [h, hi]

lemma rowE_one_norm (i : Fin 2) :
    ‖rowE (1 : Matrix (Fin 2) (Fin 2) ℂ) i‖ = 1 := by
  rw [rowE_norm]
  have : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i 0‖ ^ 2
      + ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i 1‖ ^ 2 = 1 := by
    fin_cases i <;> simp [Matrix.one_apply]
  rw [this, Real.sqrt_one]

lemma rA_zero (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 ≤ s 0) :
    rA s W 0 = s 0 := by
  have h := norm_rowE_Dm_mul_row0 (s 0) hs (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [mul_one, rowE_one_norm 0, mul_one] at h
  rw [rA]
  show ‖rowE (Dm (s 0)) 0‖ = s 0
  exact h

lemma rB_zero (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hs : 0 ≤ s 0) :
    rB s W 0 = (s 0)⁻¹ := by
  have h := norm_rowE_Dm_mul_row1 (s 0) hs (1 : Matrix (Fin 2) (Fin 2) ℂ)
  rw [mul_one, rowE_one_norm 1, mul_one] at h
  rw [rB]
  show ‖rowE (Dm (s 0)) 1‖ = (s 0)⁻¹
  exact h

/-! ## The numeric sub-invariance of the deviation parameter

The invariant `rB k ≤ η · rA k` with `η = 2/μ^{3/2}` is preserved by one step, for `μ ≥ 4`.
The estimate is a purely numeric inequality in `μ`, `λ = ‖W k 0 0‖` and
`ρ = ‖W k 0 1‖` (with `λ ^ 2 + ρ ^ 2 = 1` and `λ ^ 2 ≥ 1/μ - 2/(μ^2-1)^2`). -/

/-- The polynomial inequality behind the sub-invariance estimate: expanding around `μ = 4`
shows that the difference is `386384 + 4439888 t + ⋯ + 3 t^11` in `t = μ - 4`. -/
lemma key_poly (μ : ℝ) (hμ : 4 ≤ μ) :
    ((μ - 1) * (μ ^ 2 - 1) ^ 2 + 2 * μ) * (μ ^ 3 + 4 * μ ^ 2 - 4) ^ 2
      ≤ 4 * μ ^ 3 * ((μ ^ 2 - 1) ^ 2 - 2 * μ) * (μ ^ 2 - 2) ^ 2 := by
  have h1 : (0:ℝ) ≤ μ - 4 := by linarith
  have key : 4 * μ ^ 3 * ((μ ^ 2 - 1) ^ 2 - 2 * μ) * (μ ^ 2 - 2) ^ 2
      - ((μ - 1) * (μ ^ 2 - 1) ^ 2 + 2 * μ) * (μ ^ 3 + 4 * μ ^ 2 - 4) ^ 2
      = 386384 + 4439888*(μ-4) + 9909792*(μ-4)^2 + 10759944*(μ-4)^3 + 7045288*(μ-4)^4
        + 3038608*(μ-4)^5 + 897525*(μ-4)^6 + 183449*(μ-4)^7 + 25590*(μ-4)^8
        + 2330*(μ-4)^9 + 125*(μ-4)^10 + 3*(μ-4)^11 := by ring
  nlinarith [key, pow_nonneg h1 2, pow_nonneg h1 3, pow_nonneg h1 4, pow_nonneg h1 5,
    pow_nonneg h1 6, pow_nonneg h1 7, pow_nonneg h1 8, pow_nonneg h1 9, pow_nonneg h1 10,
    pow_nonneg h1 11]

lemma eta_sq (μ : ℝ) (hμ : 0 < μ) : (2 / (μ * Real.sqrt μ)) ^ 2 = 4 / μ ^ 3 := by
  rw [div_pow, mul_pow]
  have h : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt (le_of_lt hμ)
  rw [h]
  ring

/-- **Sub-invariance of the deviation parameter.**  If `λ ^ 2 + ρ ^ 2 = 1` with `ρ ≥ 0` and
`λ ^ 2 ≥ 1/μ - 2/(μ^2-1)^2` for `μ ≥ 4`, then the step recursion
`u ↦ (ρ + λ u)/(λ - ρ u)` keeps `u ≤ η = 2/μ^{3/2}`: in the cleared form
`ρ + λ η ≤ η (μ^2-1) (λ - ρ η)`. -/
lemma avalanche_inv (μ lam ρ : ℝ) (hμ : 4 ≤ μ) (hlam0 : 0 ≤ lam)
    (hlam : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ lam ^ 2) (hρ : 0 ≤ ρ)
    (hun : lam ^ 2 + ρ ^ 2 = 1) :
    ρ + lam * (2 / (μ * Real.sqrt μ))
      ≤ (2 / (μ * Real.sqrt μ)) * (μ ^ 2 - 1) * (lam - ρ * (2 / (μ * Real.sqrt μ))) := by
  set η := 2 / (μ * Real.sqrt μ) with hη
  have hμpos : 0 < μ := by linarith
  have hq : 0 < μ ^ 2 - 1 := by nlinarith
  have hetapos : 0 < η := by rw [hη]; positivity
  have hetasq : η ^ 2 = 4 / μ ^ 3 := by rw [hη]; exact eta_sq μ hμpos
  have hL0pos : 0 < 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
    have h2 : 2 * μ < (μ ^ 2 - 1) ^ 2 := by
      nlinarith [hμ, sq_nonneg (μ ^ 2 - 8), sq_nonneg (μ ^ 2 - 1)]
    have h3 : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2
        = ((μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2) := by
      field_simp
    rw [h3]
    exact div_pos (by linarith) (by positivity)
  have hlamle : lam ^ 2 ≤ 1 := by nlinarith [sq_nonneg ρ, hun]
  have hrho2 : ρ ^ 2 = 1 - lam ^ 2 := by linarith
  have hApos : 0 < (1 + η ^ 2 * (μ ^ 2 - 1)) ^ 2 := by positivity
  -- the polynomial inequality at the lower endpoint
  have hpoly0 : (1 - (1 / μ - 2 / (μ ^ 2 - 1) ^ 2)) * (1 + η ^ 2 * (μ ^ 2 - 1)) ^ 2
      ≤ (1 / μ - 2 / (μ ^ 2 - 1) ^ 2) * η ^ 2 * (μ ^ 2 - 2) ^ 2 := by
    have hkey := key_poly μ hμ
    rw [hetasq]
    have hstep : (1 - (1 / μ - 2 / (μ ^ 2 - 1) ^ 2)) * (1 + 4 / μ ^ 3 * (μ ^ 2 - 1)) ^ 2
        = ((μ - 1) * (μ ^ 2 - 1) ^ 2 + 2 * μ) * (μ ^ 3 + 4 * μ ^ 2 - 4) ^ 2
          / (μ * (μ ^ 2 - 1) ^ 2 * μ ^ 6) := by
      field_simp
      try ring
    have hstep2 : (1 / μ - 2 / (μ ^ 2 - 1) ^ 2) * (4 / μ ^ 3) * (μ ^ 2 - 2) ^ 2
        = 4 * μ ^ 3 * ((μ ^ 2 - 1) ^ 2 - 2 * μ) * (μ ^ 2 - 2) ^ 2
          / (μ * (μ ^ 2 - 1) ^ 2 * μ ^ 6) := by
      field_simp
      try ring
    rw [hstep, hstep2]
    exact div_le_div_of_nonneg_right hkey (by positivity)
  have hmain : (1 - lam ^ 2) * (1 + η ^ 2 * (μ ^ 2 - 1)) ^ 2 ≤ lam ^ 2 * η ^ 2 * (μ ^ 2 - 2) ^ 2 := by
    have h1 : (1 - lam ^ 2) * (1 + η ^ 2 * (μ ^ 2 - 1)) ^ 2
        ≤ (1 - (1 / μ - 2 / (μ ^ 2 - 1) ^ 2)) * (1 + η ^ 2 * (μ ^ 2 - 1)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hApos)
      linarith
    have h2 : (1 / μ - 2 / (μ ^ 2 - 1) ^ 2) * η ^ 2 * (μ ^ 2 - 2) ^ 2
        ≤ lam ^ 2 * η ^ 2 * (μ ^ 2 - 2) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hlam (sq_nonneg η)
    linarith
  have hsq : (ρ * (1 + η ^ 2 * (μ ^ 2 - 1))) ^ 2 ≤ (lam * η * (μ ^ 2 - 2)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hrho2]
    nlinarith [hmain]
  have hb1 : (0:ℝ) ≤ ρ * (1 + η ^ 2 * (μ ^ 2 - 1)) := by
    have : (0:ℝ) < 1 + η ^ 2 * (μ ^ 2 - 1) := by positivity
    exact mul_nonneg hρ (le_of_lt this)
  have hμ2 : (0:ℝ) ≤ μ ^ 2 - 2 := by nlinarith
  have hb2 : (0:ℝ) ≤ lam * η * (μ ^ 2 - 2) := by
    exact mul_nonneg (mul_nonneg hlam0 (le_of_lt hetapos)) hμ2
  have hle : ρ * (1 + η ^ 2 * (μ ^ 2 - 1)) ≤ lam * η * (μ ^ 2 - 2) := by
    have h := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg hb1, abs_of_nonneg hb2] at h
  nlinarith [hle]

/-! ## The invariant step

The step recursion for `u = rB k / rA k` is
`u ↦ s⁻² (ρ + λ u)/(λ - ρ u)`, with `λ = ‖W k 0 0‖`, `ρ = ‖W k 0 1‖`, `λ² + ρ² = 1` and
`λ² ≥ L := 1/μ - 2/(μ²-1)²`, while `s² ≥ μ² - 1`.  Combining `avalanche_inv` with the
monotonicity of the Möbius map in `u` keeps `u ≤ η = 2/μ^{3/2}`. -/

lemma frac_mono (lam rho u eta : ℝ) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hlr : lam ^ 2 + rho ^ 2 = 1) (hu : u ≤ eta) (hpos : 0 < lam - rho * eta) :
    (rho + lam * u) / (lam - rho * u) ≤ (rho + lam * eta) / (lam - rho * eta) := by
  have hden : 0 < lam - rho * u := by
    have h := mul_le_mul_of_nonneg_left hu hrho
    linarith
  rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [hlr, hu, hlam, hrho, mul_le_mul_of_nonneg_left hu hrho,
    mul_nonneg hrho (sub_nonneg.mpr hu)]

/-- The map `u ↦ s⁻² (ρ + λ u)/(λ - ρ u)` preserves `u ≤ η` for `μ ≥ 4`. -/
lemma inv_step_bound (μ lam rho s A B A' B' : ℝ) (hμ : 4 ≤ μ)
    (hspos : 0 < s) (hs2 : μ ^ 2 - 1 ≤ s ^ 2)
    (hlam0 : 0 ≤ lam) (hrho0 : 0 ≤ rho) (hlr : lam ^ 2 + rho ^ 2 = 1)
    (hL : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ lam ^ 2)
    (hA : 0 < A) (hB0 : 0 ≤ B)
    (hB : B ≤ (2 / (μ * Real.sqrt μ)) * A)
    (hAge : s * (lam * A - rho * B) ≤ A')
    (hB'le : B' ≤ s⁻¹ * (rho * A + lam * B)) :
    0 < A' ∧ B' ≤ (2 / (μ * Real.sqrt μ)) * A' := by
  have hμpos : 0 < μ := by linarith
  have hq : 0 < μ ^ 2 - 1 := by nlinarith
  set η : ℝ := 2 / (μ * Real.sqrt μ) with hη
  have hetapos : 0 < η := by rw [hη]; positivity
  have hLpos : 0 < 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
    have h2 : 2 * μ < (μ ^ 2 - 1) ^ 2 := by
      nlinarith [hμ, sq_nonneg (μ ^ 2 - 8), sq_nonneg (μ ^ 2 - 1)]
    have h3 : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2
        = ((μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2) := by
      field_simp
    rw [h3]
    exact div_pos (by linarith) (by positivity)
  have hlampos : 0 < lam := by nlinarith [hL, hLpos]
  -- `λ ^ 2 ≥ 3/(4 μ)`
  have hLbig : 3 / 4 / μ ≤ lam ^ 2 := by
    have h1 : (3:ℝ) / 4 / μ ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
      rw [← sub_nonneg]
      have h3 : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 - 3 / 4 / μ
          = (1 / 4 * (μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2) := by
        field_simp
        ring
      rw [h3]
      apply div_nonneg _ (by positivity)
      nlinarith [hμ, sq_nonneg (μ - 4), sq_nonneg (μ ^ 2 - 4)]
    linarith
  have hη2 : η ^ 2 = 4 / μ ^ 3 := by rw [hη]; exact eta_sq μ hμpos
  -- `λ - ρ η > 0`
  have hden : 0 < lam - rho * η := by
    have hr2 : rho ^ 2 = 1 - lam ^ 2 := by linarith
    have h5 : 4 / μ ^ 3 < 3 / 4 / μ := by
      rw [div_lt_div_iff₀ (by positivity) hμpos]
      nlinarith
    have hsq : (rho * η) ^ 2 < lam ^ 2 := by
      rw [mul_pow, hr2, hη2]
      nlinarith [hLbig, h5, mul_nonneg (sq_nonneg lam) (by positivity : (0:ℝ) ≤ 4 / μ ^ 3)]
    have h2 := sq_lt_sq.mp hsq
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (le_of_lt hlampos)] at h2
    linarith
  have hu : B / A ≤ η := by
    rw [div_le_iff₀ hA]; exact hB
  have hlamArB : 0 < lam * A - rho * B := by
    have h2 : rho * (B / A) ≤ rho * η := mul_le_mul_of_nonneg_left hu hrho0
    have h3 : 0 < lam - rho * (B / A) := by linarith
    have h4 : lam * A - rho * B = A * (lam - rho * (B / A)) := by
      field_simp
    rw [h4]
    exact mul_pos hA h3
  have hA'pos : 0 < A' := lt_of_lt_of_le (mul_pos hspos hlamArB) hAge
  refine ⟨hA'pos, ?_⟩
  have hnum_nonneg : 0 ≤ s⁻¹ * (rho * A + lam * B) := by positivity
  have hdenpos : 0 < s * (lam * A - rho * B) := mul_pos hspos hlamArB
  have hstep : B' / A' ≤ (s⁻¹ * (rho * A + lam * B)) / (s * (lam * A - rho * B)) := by
    calc B' / A' ≤ (s⁻¹ * (rho * A + lam * B)) / A' :=
          div_le_div_of_nonneg_right hB'le (le_of_lt hA'pos)
      _ ≤ (s⁻¹ * (rho * A + lam * B)) / (s * (lam * A - rho * B)) :=
          div_le_div_of_nonneg_left hnum_nonneg hdenpos hAge
  have hsplit : (s⁻¹ * (rho * A + lam * B)) / (s * (lam * A - rho * B))
      = s⁻¹ * s⁻¹ * ((rho + lam * (B / A)) / (lam - rho * (B / A))) := by
    field_simp
    try ring
  rw [hsplit] at hstep
  have hs2' : s⁻¹ * s⁻¹ ≤ 1 / (μ ^ 2 - 1) := by
    have h1 : s⁻¹ * s⁻¹ = (s ^ 2)⁻¹ := by rw [← sq, inv_pow]
    have h2 : (1:ℝ) / (μ ^ 2 - 1) = (μ ^ 2 - 1)⁻¹ := by rw [inv_eq_one_div]
    rw [h1, h2]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hs2
  have hfrac : (rho + lam * (B / A)) / (lam - rho * (B / A)) ≤ (rho + lam * η) / (lam - rho * η) :=
    frac_mono lam rho (B / A) η hlam0 hrho0 hlr hu hden
  have hden2 : 0 < lam - rho * (B / A) := by
    have := mul_le_mul_of_nonneg_left hu hrho0
    linarith
  have hc : 0 ≤ (rho + lam * (B / A)) / (lam - rho * (B / A)) :=
    div_nonneg (by positivity) (le_of_lt hden2)
  have hcomb : B' / A' ≤ (1 / (μ ^ 2 - 1)) * ((rho + lam * η) / (lam - rho * η)) := by
    calc B' / A' ≤ s⁻¹ * s⁻¹ * ((rho + lam * (B / A)) / (lam - rho * (B / A))) := hstep
      _ ≤ (1 / (μ ^ 2 - 1)) * ((rho + lam * η) / (lam - rho * η)) :=
          mul_le_mul hs2' hfrac hc (by positivity)
  rw [div_le_iff₀ hA'pos] at hcomb
  have hfinal : (rho + lam * η) ≤ η * (μ ^ 2 - 1) * (lam - rho * η) :=
    avalanche_inv μ lam rho hμ (le_of_lt hlampos) hL hrho0 hlr
  have h1 : (rho + lam * η) / (lam - rho * η) ≤ η * (μ ^ 2 - 1) := by
    rw [div_le_iff₀ hden]
    linarith [hfinal]
  calc B' ≤ (1 / (μ ^ 2 - 1)) * ((rho + lam * η) / (lam - rho * η)) * A' := hcomb
    _ ≤ (1 / (μ ^ 2 - 1)) * (η * (μ ^ 2 - 1)) * A' := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hA'pos)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = η * A' := by field_simp

/-! ## The accumulated logarithmic error -/

/-- `frob (Dm s) = √(s² + s⁻²)`. -/
lemma frob_Dm_ce (s : ℝ) : frob (Dm s) = Real.sqrt (s ^ 2 + (s ^ 2)⁻¹) := by
  have h0 : ‖(Dm s) 0 0‖ ^ 2 = s ^ 2 := by simp [Dm, Matrix.diagonal]
  have h1 : ‖(Dm s) 0 1‖ ^ 2 = 0 := by simp [Dm, Matrix.diagonal]
  have h2 : ‖(Dm s) 1 0‖ ^ 2 = 0 := by simp [Dm, Matrix.diagonal]
  have h3 : ‖(Dm s) 1 1‖ ^ 2 = (s ^ 2)⁻¹ := by simp [Dm, Matrix.diagonal, inv_pow]
  simp only [frob, h0, h1, h2, h3]
  ring_nf

/-- The accumulated error in the log-telescoping. -/
def Eerr (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ :=
  Real.log (frob (Nmat s W k)) - (∑ j ∈ Finset.range (k + 1), Real.log (s j))
    - (∑ j ∈ Finset.range k, Real.log (‖W j 0 0‖))

/-- The factor by which `frob (N (k+1))` exceeds `s (k+1) · ‖W k 0 0‖ · frob (N k)`. -/
def qrat (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℝ :=
  frob (Nmat s W (k + 1)) / (s (k + 1) * ‖W k 0 0‖ * frob (Nmat s W k))

lemma qrat_pos (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 < s (k + 1)) (hl : 0 < ‖W k 0 0‖) (hf : 0 < frob (Nmat s W k))
    (hf1 : 0 < frob (Nmat s W (k + 1))) : 0 < qrat s W k := by
  rw [qrat]
  exact div_pos hf1 (by positivity)

lemma mul_qrat (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 < s (k + 1)) (hl : 0 < ‖W k 0 0‖) (hf : 0 < frob (Nmat s W k)) :
    s (k + 1) * ‖W k 0 0‖ * frob (Nmat s W k) * qrat s W k = frob (Nmat s W (k + 1)) := by
  rw [qrat]
  field_simp

lemma Eerr_succ (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : 0 < s (k + 1)) (hl : 0 < ‖W k 0 0‖) (hf : 0 < frob (Nmat s W k))
    (hf1 : 0 < frob (Nmat s W (k + 1))) :
    Eerr s W (k + 1) = Eerr s W k + Real.log (qrat s W k) := by
  unfold Eerr
  rw [← mul_qrat s W k hs hl hf,
    Finset.sum_range_succ (fun j => Real.log (s j)) (k + 1),
    Finset.sum_range_succ (fun j => Real.log (‖W j 0 0‖)) k]
  rw [Real.log_mul (by positivity) (ne_of_gt (qrat_pos s W k hs hl hf hf1)),
    Real.log_mul (by positivity) (ne_of_gt hf),
    Real.log_mul (ne_of_gt hs) (ne_of_gt hl)]
  ring

lemma Eerr_zero (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (hs0 : 0 < s 0) :
    Eerr s W 0 = Real.log (1 + ((s 0) ^ 4)⁻¹) / 2 := by
  have hfrob : frob (Nmat s W 0) = s 0 * Real.sqrt (1 + ((s 0) ^ 4)⁻¹) := by
    show frob (Dm (s 0)) = s 0 * Real.sqrt (1 + ((s 0) ^ 4)⁻¹)
    rw [frob_Dm_ce]
    have h : s 0 ^ 2 + (s 0 ^ 2)⁻¹ = (s 0) ^ 2 * (1 + ((s 0) ^ 4)⁻¹) := by
      field_simp
      try ring
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hs0)]
  have h1 : 0 < 1 + ((s 0) ^ 4)⁻¹ := by positivity
  simp only [Eerr, Finset.sum_range_zero, Finset.sum_range_one, Nat.zero_add, sub_zero,
    Finset.sum_empty]
  rw [hfrob, Real.log_mul (ne_of_gt hs0) (ne_of_gt (Real.sqrt_pos.mpr h1)),
    Real.log_sqrt (le_of_lt h1)]
  ring

lemma Eerr_eq (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (m : ℕ)
    (hs : ∀ k, k < m → 0 < s (k + 1)) (hl : ∀ k, k < m → 0 < ‖W k 0 0‖)
    (hf : ∀ k, k ≤ m → 0 < frob (Nmat s W k)) :
    Eerr s W m = Eerr s W 0 + ∑ k ∈ Finset.range m, Real.log (qrat s W k) := by
  induction m with
  | zero => simp [Eerr]
  | succ m ih =>
    rw [Finset.sum_range_succ,
      Eerr_succ s W m (hs m (by omega)) (hl m (by omega)) (hf m (by omega))
        (hf (m+1) (by omega)),
      ih (fun k hk => hs k (by omega)) (fun k hk => hl k (by omega))
        (fun k hk => hf k (by omega))]
    ring

/-- `frob (N k) > 0` for the truncated products. -/
lemma frob_Nmat_pos (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ)
    (hs : ∀ j, j ≤ k → s j ≠ 0) (hW : ∀ j, j < k → W j * (W j).conjTranspose = 1) :
    0 < frob (Nmat s W k) := by
  have hdet : (Nmat s W k).det ≠ 0 := by
    have h := norm_det_Nmat s W k hs hW
    intro hc
    rw [hc, norm_zero] at h
    norm_num at h
  rcases lt_or_eq_of_le (frob_nonneg (Nmat s W k)) with h | h
  · exact h
  · exfalso
    have hM : Nmat s W k = 0 := by
      ext i j
      have h1 : ‖(Nmat s W k) i j‖ ≤ frob (Nmat s W k) := frob_entry _ i j
      rw [← h] at h1
      exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
    rw [hM] at hdet
    simp at hdet

/-! ## The crude step bounds (for `3 < μ < 4`) -/

lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [sq_nonneg (b - a), mul_nonneg ha hb]

lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith [sq_nonneg (b - a), sq_nonneg (a + b), mul_nonneg ha hb]

lemma log_ge_one_sub_inv {y : ℝ} (hy : 0 < y) : 1 - 1 / y ≤ Real.log y := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / y by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hy), Real.log_one] at h
  linarith

/-- Crude per-step log bound: if the deviation `u = B/A` is at most `1/3` (which is what
happens for the first two steps when `3 < μ < 4`) then the log-ratio is bounded by `8`. -/
lemma ratio_bound_crude (s lam rho A B A' B' : ℝ)
    (hs : 1 ≤ s) (hs2 : 8 ≤ s ^ 2)
    (hlam0 : 0 ≤ lam) (hrho0 : 0 ≤ rho)
    (hL : 23 / 100 ≤ lam ^ 2)
    (hlr : lam ^ 2 + rho ^ 2 = 1) (hA : 0 < A) (hB0 : 0 ≤ B) (hB'0 : 0 ≤ B')
    (hu : B ≤ (1 / 3) * A)
    (hA'le : A' ≤ s * (lam * A + rho * B)) (hA'ge : s * (lam * A - rho * B) ≤ A')
    (hB'le : B' ≤ s⁻¹ * (rho * A + lam * B)) :
    |Real.log ((A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)))| ≤ 8 := by
  have hlampos : 0 < lam := by nlinarith [hL]
  have hu0 : 0 ≤ B / A := div_nonneg hB0 (le_of_lt hA)
  have hu3 : B / A ≤ 1 / 3 := by rw [div_le_iff₀ hA]; linarith
  have hu2le : (B / A) ^ 2 ≤ 1 / 9 := by nlinarith [hu3, hu0]
  have hT : (0:ℝ) < A ^ 2 + B ^ 2 := by positivity
  -- the ratio `x = (ρ/λ) u` is at most `0.61`
  have hx2 : ((rho / lam) * (B / A)) ^ 2 ≤ (61 / 100) ^ 2 := by
    have hr2 : rho ^ 2 = 1 - lam ^ 2 := by linarith
    have e1 : (rho / lam) ^ 2 ≤ 77 / 23 := by
      rw [div_pow, hr2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hL]
    have e2 : ((rho / lam) * (B / A)) ^ 2 = (rho / lam) ^ 2 * (B / A) ^ 2 := by ring
    rw [e2]
    nlinarith [e1, hu2le, sq_nonneg (rho / lam), sq_nonneg (B / A)]
  have hx0 : 0 ≤ (rho / lam) * (B / A) := by positivity
  have hx : (rho / lam) * (B / A) ≤ 61 / 100 :=
    le_of_sq_le_sq_of_nonneg hx0 (by norm_num) hx2
  have hArB : lam * A - rho * B = A * (lam - rho * (B / A)) := by field_simp
  have hpos1 : 0 ≤ lam - rho * (B / A) := by
    have h := mul_le_mul_of_nonneg_right hx hlampos.le
    have h2 : (rho / lam) * (B / A) * lam = rho * (B / A) := by field_simp
    rw [h2] at h
    nlinarith [h, hlampos]
  have hA'0 : 0 ≤ A' := by
    have h1 : 0 ≤ s * (lam * A - rho * B) := by rw [hArB]; positivity
    linarith [hA'ge]
  have hs4 : (s⁻¹) ^ 4 ≤ 1 / 64 := by
    have h1 : (s ^ 2) ^ 2 ≥ 64 := by nlinarith
    rw [inv_pow]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith [h1]
  -- the two-sided bound for the ratio
  have hratio_le : (A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)) ≤ 5 := by
    have hA'2 : A' ^ 2 ≤ s ^ 2 * (A ^ 2 + B ^ 2) := by
      have h1 : A' ^ 2 ≤ (s * (lam * A + rho * B)) ^ 2 :=
        sq_le_sq_of_nonneg hA'0 (by positivity) hA'le
      rw [mul_pow] at h1
      have h2 : (lam * A + rho * B) ^ 2 ≤ (A ^ 2 + B ^ 2) := by
        nlinarith [sq_nonneg (lam * B - rho * A), hlr]
      nlinarith [h1, h2, hT, sq_nonneg s]
    have hB'2 : B' ^ 2 ≤ (s⁻¹) ^ 2 * (A ^ 2 + B ^ 2) := by
      have h1 : B' ^ 2 ≤ (s⁻¹ * (rho * A + lam * B)) ^ 2 :=
        sq_le_sq_of_nonneg hB'0 (by positivity) hB'le
      rw [mul_pow] at h1
      have h2 : (rho * A + lam * B) ^ 2 ≤ (A ^ 2 + B ^ 2) := by
        nlinarith [sq_nonneg (rho * B - lam * A), hlr]
      nlinarith [h1, h2, hT, sq_nonneg (s⁻¹)]
    rw [div_le_iff₀ (by positivity)]
    have h3 : (1 + (s⁻¹) ^ 4) ≤ 5 * lam ^ 2 := by nlinarith [hs4, hL]
    have h4 : (s ^ 2 + (s⁻¹) ^ 2) = (1 + (s⁻¹) ^ 4) * s ^ 2 := by
      field_simp
      try ring
    nlinarith [hA'2, hB'2, h3, h4, hT, sq_pos_of_pos hlampos]
  have hratio_ge : (1 : ℝ) / 9 ≤ (A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (s * (lam * A - rho * B)) ^ 2 ≤ A' ^ 2 :=
      sq_le_sq_of_nonneg (by rw [hArB]; positivity) hA'0 hA'ge
    have h2 : (s * (lam * A - rho * B)) ^ 2 = s ^ 2 * A ^ 2 * (lam - rho * (B / A)) ^ 2 := by
      rw [hArB]; ring
    rw [h2] at h1
    have h8 : lam - rho * (B / A) ≥ lam * (1 - 61 / 100) := by
      have h9 : rho * (B / A) = lam * ((rho / lam) * (B / A)) := by field_simp
      have h10 : lam * ((rho / lam) * (B / A)) ≤ lam * (61 / 100) :=
        mul_le_mul_of_nonneg_left hx hlampos.le
      linarith
    have h4 : (1 / 9) * lam ^ 2 * (1 + (B / A) ^ 2) ≤ (lam - rho * (B / A)) ^ 2 := by
      nlinarith [h8, hu2le, hlampos, sq_nonneg (lam - rho * (B / A)), sq_nonneg lam]
    have hT2 : A ^ 2 + B ^ 2 = A ^ 2 * (1 + (B / A) ^ 2) := by
      rw [eq_comm]; field_simp; try ring
    have h5 : (1 / 9) * (s ^ 2 * lam ^ 2 * (A ^ 2 * (1 + (B / A) ^ 2))) ≤ A' ^ 2 := by
      have h6 : (1 / 9) * lam ^ 2 * (1 + (B / A) ^ 2) * (s ^ 2 * A ^ 2)
          ≤ (lam - rho * (B / A)) ^ 2 * (s ^ 2 * A ^ 2) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      nlinarith [h1, h6]
    rw [hT2]
    nlinarith [h5, sq_nonneg B']
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hRpos : 0 < (A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)) := by positivity
    have hlow := log_ge_one_sub_inv hRpos
    have h9 : 1 / ((A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2))) ≤ 9 := by
      rw [div_le_iff₀ hRpos]; linarith
    linarith
  · have hRpos : 0 < (A' ^ 2 + B' ^ 2) / (s ^ 2 * lam ^ 2 * (A ^ 2 + B ^ 2)) := by positivity
    have hub := Real.log_le_sub_one_of_pos hRpos
    linarith [hub, hratio_le]


lemma Lmu_ge_23 (μ : ℝ) (hμ3 : 3 < μ) (hμ4 : μ ≤ 4) :
    (23 : ℝ) / 100 ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
  have hμpos : 0 < μ := by linarith
  have hQ : 8 ≤ μ ^ 2 - 1 := by nlinarith
  have hL4 : (217:ℝ) / 900 ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
    rw [← sub_nonneg]
    have h : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 - 217 / 900
        = (4 - μ) * (1 / (4 * μ)
            - 2 * (4 + μ) * (15 + (μ ^ 2 - 1)) / (225 * (μ ^ 2 - 1) ^ 2)) := by
      field_simp
      ring
    rw [h]
    apply mul_nonneg (by linarith)
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hμ3, hμ4, hQ]
  linarith

/-- The crude bound `u ₁ ≤ 1/3`, in the exact form needed for the induction. -/
lemma crude_u1_num (μ s0 s1 a b : ℝ) (hμ3 : 3 < μ) (hμ4 : μ ≤ 4)
    (hs0 : μ ^ 2 - 1 ≤ s0 ^ 2) (hs1 : μ ^ 2 - 1 ≤ s1 ^ 2) (hs0pos : 0 < s0) (hs1pos : 0 < s1)
    (ha : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ a ^ 2) (ha1 : a ≤ 1) (ha0 : 0 ≤ a)
    (hb : b ^ 2 = 1 - a ^ 2) (hb0 : 0 ≤ b) :
    s1⁻¹ * (b * s0 + a * s0⁻¹) ≤ (1 / 3) * s1 * (a * s0 - b * s0⁻¹) := by
  set Q := μ ^ 2 - 1 with hQ
  have hQpos : 0 < Q := by rw [hQ]; nlinarith
  have hQ8 : 8 ≤ Q := by rw [hQ]; nlinarith
  have ha2 : 23 / 100 ≤ a ^ 2 := le_trans (Lmu_ge_23 μ hμ3 hμ4) ha
  have hy : s0⁻¹ * s0⁻¹ ≤ 1 / Q := by
    have h1 : s0⁻¹ * s0⁻¹ = (s0 ^ 2)⁻¹ := by rw [← sq, inv_pow]
    rw [h1, one_div]
    exact (inv_le_inv₀ (by positivity) hQpos).mpr hs0
  have hkey : 16 * Q ^ 2 ≤ a ^ 2 * (Q ^ 4 + 10 * Q ^ 2 + 9) := by
    have h1 : 16 * Q ^ 2 ≤ (23 / 100) * (Q ^ 4 + 10 * Q ^ 2 + 9) := by
      have h60 : 0 ≤ Q ^ 2 - 60 := by
        have := mul_nonneg (sub_nonneg.mpr hQ8) (le_of_lt hQpos)
        nlinarith [this]
      have h2 : 0 ≤ Q ^ 2 * (Q ^ 2 - 60) := mul_nonneg (by positivity) h60
      nlinarith [h2, hQ8]
    nlinarith [h1, ha2, sq_nonneg (Q ^ 4 + 10 * Q ^ 2 + 9)]
  -- `4 b Q ≤ a (Q^2 - 3)`
  have h4b : 4 * b * Q ≤ a * (Q ^ 2 - 3) := by
    have e1 : (4 * b * Q) ^ 2 ≤ (a * (Q ^ 2 - 3)) ^ 2 := by
      nlinarith [hb, hkey, hQpos, ha0]
    have h2 : 0 ≤ 4 * b * Q := by positivity
    have h3 : 0 ≤ a * (Q ^ 2 - 3) := mul_nonneg ha0 (by nlinarith [hQ8])
    exact le_of_sq_le_sq_of_nonneg h2 h3 e1
  -- conclude `3 (b + a y') ≤ Q (a - b y')` with `y' = s0^{-2} ≤ 1/Q`
  have hbQ : b * (1 / Q) * Q = b := by field_simp
  have haQ : a * (1 / Q) * Q = a := by field_simp
  have h5 : b * (s0⁻¹ * s0⁻¹) * Q ≤ b := by
    have h := mul_le_mul_of_nonneg_left hy hb0
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hQpos)
    linarith [h2, hbQ]
  have h6 : a * (s0⁻¹ * s0⁻¹) * Q ≤ a := by
    have h := mul_le_mul_of_nonneg_left hy ha0
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hQpos)
    linarith [h2, haQ]
  have hmain : 3 * (b + a * (s0⁻¹ * s0⁻¹)) ≤ Q * (a - b * (s0⁻¹ * s0⁻¹)) := by
    have hQG : 0 ≤ Q * (Q * a - Q * b * (s0⁻¹ * s0⁻¹) - 3 * b - 3 * a * (s0⁻¹ * s0⁻¹)) := by
      nlinarith [h4b, h5, h6, hQpos, hb0, ha0, mul_nonneg hQpos.le hQpos.le]
    have := (mul_nonneg_iff_of_pos_left hQpos).mp hQG
    linarith [this]
  have hL : s1⁻¹ * (b * s0 + a * s0⁻¹)
      = s0 * (s1⁻¹ * s1⁻¹ * (b + a * (s0⁻¹ * s0⁻¹))) * s1 := by
    field_simp
    try ring
  have hR : (1 / 3) * s1 * (a * s0 - b * s0⁻¹)
      = s0 * (1 / 3 * (a - b * (s0⁻¹ * s0⁻¹))) * s1 := by
    field_simp
    try ring
  have hs1sq : s1⁻¹ * s1⁻¹ ≤ 1 / Q := by
    have h1 : s1⁻¹ * s1⁻¹ = (s1 ^ 2)⁻¹ := by rw [← sq, inv_pow]
    rw [h1, one_div]
    exact (inv_le_inv₀ (by positivity) hQpos).mpr hs1
  rw [hL, hR]
  have hstep : s1⁻¹ * s1⁻¹ * (b + a * (s0⁻¹ * s0⁻¹)) ≤ 1 / 3 * (a - b * (s0⁻¹ * s0⁻¹)) := by
    have h10 : (1 / Q) * (b + a * (s0⁻¹ * s0⁻¹)) ≤ (1 / 3) * (a - b * (s0⁻¹ * s0⁻¹)) := by
      have h11 : b + a * (s0⁻¹ * s0⁻¹) ≤ (Q / 3) * (a - b * (s0⁻¹ * s0⁻¹)) := by linarith [hmain]
      have hm := mul_le_mul_of_nonneg_left h11 (by positivity : (0:ℝ) ≤ 1 / Q)
      have h32 : (1 / Q) * ((Q / 3) * (a - b * (s0⁻¹ * s0⁻¹)))
          = (1 / 3) * (a - b * (s0⁻¹ * s0⁻¹)) := by
        field_simp
      linarith [hm, h32]
    have h12 : s1⁻¹ * s1⁻¹ * (b + a * (s0⁻¹ * s0⁻¹)) ≤ (1 / Q) * (b + a * (s0⁻¹ * s0⁻¹)) :=
      mul_le_mul_of_nonneg_right hs1sq (by positivity)
    linarith [h10, h12]
  have hfin := mul_le_mul_of_nonneg_left hstep (le_of_lt hs0pos)
  have hfin2 := mul_le_mul_of_nonneg_right hfin (le_of_lt hs1pos)
  exact hfin2

theorem core_est (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (μ : ℝ)
    (hn : 2 ≤ n) (hμn : (n : ℝ) < μ) (hμ : 3 < μ)
    (hσ : ∀ j, j < n → 1 ≤ s j)
    (hσμ : ∀ j, j + 1 < n → μ ^ 2 - 1 ≤ (s j) ^ 2 ∧ μ ^ 2 - 1 ≤ (s (j + 1)) ^ 2)
    (hW : ∀ j, j + 1 < n → (W j).conjTranspose * W j = 1 ∧ W j * (W j).conjTranspose = 1)
    (hlam : ∀ j, j + 1 < n → 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 ≤ ‖W j 0 0‖ ^ 2) :
    |Real.log (frob (Nmat s W (n - 1)))
        - (∑ j ∈ Finset.range n, Real.log (s j))
        - (∑ j ∈ Finset.range (n - 1), Real.log ‖W j 0 0‖)| ≤ 450 * (n : ℝ) / μ := by
  have hμpos : 0 < μ := by linarith
  have hs0 : 0 < s 0 := lt_of_lt_of_le zero_lt_one (hσ 0 (by omega))
  have hs1p : 0 < s 1 := lt_of_lt_of_le zero_lt_one (hσ 1 (by omega))
  by_cases hμ4 : 4 ≤ μ
  · -- ## the sharp case
    have hqpos : (0:ℝ) < μ ^ 2 - 1 := by nlinarith
    have hP : ∀ k, k ≤ n - 1 → 0 < rA s W k ∧ rB s W k ≤ (2 / (μ * Real.sqrt μ)) * rA s W k
        ∧ |Eerr s W k| ≤ 30 * (k + 1) / μ := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rwa [rA_zero s W hs0.le]
        · rw [rB_zero s W hs0.le, rA_zero s W hs0.le, inv_le_iff_one_le_mul₀ hs0]
          have hh : μ * Real.sqrt μ ≤ 2 * (μ ^ 2 - 1) := by
            have h1 : (μ * Real.sqrt μ) ^ 2 ≤ (2 * (μ ^ 2 - 1)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (le_of_lt hμpos)]
              nlinarith [hμ, sq_nonneg (μ ^ 2 - 1)]
            exact le_of_sq_le_sq_of_nonneg (by positivity) (by nlinarith) h1
          have h2 := (hσμ 0 (by omega)).1
          have hkey : μ * Real.sqrt μ ≤ 2 * (s 0) ^ 2 := by nlinarith [hh, h2]
          rw [show 2 / (μ * Real.sqrt μ) * s 0 * s 0
              = 2 * (s 0) ^ 2 / (μ * Real.sqrt μ) from by ring]
          rw [le_div_iff₀ (by positivity : (0:ℝ) < μ * Real.sqrt μ)]
          nlinarith [hkey]
        · rw [Eerr_zero s W hs0]
          have h1 : 0 < 1 + ((s 0) ^ 4)⁻¹ := by positivity
          have hlog0 : 0 ≤ Real.log (1 + ((s 0) ^ 4)⁻¹) :=
            Real.log_nonneg (by linarith [show (0:ℝ) ≤ ((s 0) ^ 4)⁻¹ by positivity])
          have hlog1 : Real.log (1 + ((s 0) ^ 4)⁻¹) ≤ ((s 0) ^ 4)⁻¹ := by
            linarith [Real.log_le_sub_one_of_pos h1]
          have ht : ((s 0) ^ 4)⁻¹ ≤ 1 / (μ ^ 2 - 1) ^ 2 := by
            have hq := (hσμ 0 (by omega)).1
            have hineq : (μ ^ 2 - 1) ^ 2 ≤ (s 0) ^ 4 := by
              have hp := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ μ ^ 2 - 1) hq 2
              rwa [show ((s 0) ^ 2) ^ 2 = (s 0) ^ 4 from by ring] at hp
            have hab : (0:ℝ) < (s 0) ^ 4 := pow_pos hs0 4
            have hbb : (0:ℝ) < (μ ^ 2 - 1) ^ 2 := pow_pos hqpos 2
            have hle : ((s 0) ^ 4)⁻¹ ≤ ((μ ^ 2 - 1) ^ 2)⁻¹ :=
              (inv_le_inv₀ hab hbb).mpr hineq
            simpa [one_div] using hle
          have hfin : 1 / (μ ^ 2 - 1) ^ 2 / 2 ≤ 30 / μ := by
            rw [div_div, div_le_div_iff₀ (show (0:ℝ) < (μ ^ 2 - 1) ^ 2 * 2 by positivity) hμpos]
            have hk : μ ≤ 60 * (μ ^ 2 - 1) ^ 2 := by
              have h0 : μ ^ 2 / 2 ≤ μ ^ 2 - 1 := by nlinarith [hμ4]
              have h1 : (μ ^ 2 / 2) ^ 2 ≤ (μ ^ 2 - 1) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h0 2
              nlinarith [h1, hμ4]
            nlinarith [hk]
          have e1 : Real.log (1 + ((s 0) ^ 4)⁻¹) / 2 ≤ ((s 0) ^ 4)⁻¹ / 2 := by linarith
          have e2 : ((s 0) ^ 4)⁻¹ / 2 ≤ 1 / (μ ^ 2 - 1) ^ 2 / 2 := by linarith
          rw [abs_of_nonneg (by linarith : 0 ≤ Real.log (1 + ((s 0) ^ 4)⁻¹) / 2)]
          linarith [e1, e2, hfin]
      | succ k ih =>
        intro hk
        obtain ⟨hAk, huBk, hErrk⟩ := ih (by omega)
        have hk1 : k + 1 < n := by omega
        have hσk : 1 ≤ s (k + 1) := hσ (k + 1) (by omega)
        have hsk2 : μ ^ 2 - 1 ≤ (s (k + 1)) ^ 2 := (hσμ k hk1).2
        have hWk := hW k hk1
        have hlamk := hlam k hk1
        have hfk : 0 < frob (Nmat s W k) :=
          frob_Nmat_pos s W k (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
            (fun j hj => (hW j (by omega)).2)
        have hfk1 : 0 < frob (Nmat s W (k + 1)) :=
          frob_Nmat_pos s W (k + 1) (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
            (fun j hj => (hW j (by omega)).2)
        have hLpos : 0 < 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := by
          have h3 : 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 = ((μ ^ 2 - 1) ^ 2 - 2 * μ) / (μ * (μ ^ 2 - 1) ^ 2) := by
            field_simp
            try ring
          rw [h3]
          exact div_pos (by nlinarith [hμ4, sq_nonneg (μ ^ 2 - 4), sq_nonneg μ]) (by positivity)
        have hlampos : 0 < ‖W k 0 0‖ := by
          have h2 : 0 < ‖W k 0 0‖ ^ 2 := lt_of_lt_of_le hLpos hlamk
          nlinarith [norm_nonneg (W k 0 0), sq_nonneg (‖W k 0 0‖), h2]
        obtain ⟨hinv1, hinv2⟩ := inv_step_bound μ (‖W k 0 0‖) (‖W k 0 1‖) (s (k + 1))
          (rA s W k) (rB s W k) (rA s W (k + 1)) (rB s W (k + 1)) hμ4 (by linarith) hsk2
          (norm_nonneg _) (norm_nonneg _) (lamW_sq_add_rhoW_sq W k hWk.2) hlamk hAk
          (rB_nonneg s W k) huBk (rA_succ_ge s W k (by linarith))
          (rB_succ_le s W k (by linarith) hWk.2 hWk.1)
        have hratio : |Real.log (qrat s W k)| ≤ 15 / μ := by
          have h1 : |Real.log (((rA s W (k + 1)) ^ 2 + (rB s W (k + 1)) ^ 2)
              / ((s (k + 1)) ^ 2 * (‖W k 0 0‖) ^ 2 * ((rA s W k) ^ 2 + (rB s W k) ^ 2)))| ≤ 30 / μ :=
            ratio_bound_num μ (s (k + 1)) (‖W k 0 0‖) (‖W k 0 1‖) (rA s W k) (rB s W k)
              (rA s W (k + 1)) (rB s W (k + 1)) hμ4 (by linarith) hsk2 (norm_nonneg _)
              (norm_nonneg _) hlamk (lamW_sq_add_rhoW_sq W k hWk.2) hAk (rB_nonneg s W k)
              (rB_nonneg s W (k + 1)) huBk (rA_succ_le s W k (by linarith))
              (rA_succ_ge s W k (by linarith)) (rB_succ_le s W k (by linarith) hWk.2 hWk.1)
          have hden : (s (k + 1) * ‖W k 0 0‖ * frob (Nmat s W k)) ^ 2
              = (s (k + 1)) ^ 2 * (‖W k 0 0‖) ^ 2 * ((rA s W k) ^ 2 + (rB s W k) ^ 2) := by
            rw [mul_pow, mul_pow, rA_sq_add_rB_sq]
          have h2 : qrat s W k ^ 2 = ((rA s W (k + 1)) ^ 2 + (rB s W (k + 1)) ^ 2)
              / ((s (k + 1)) ^ 2 * (‖W k 0 0‖) ^ 2 * ((rA s W k) ^ 2 + (rB s W k) ^ 2)) := by
            rw [qrat, div_pow, rA_sq_add_rB_sq, hden]
          rw [← h2] at h1
          have h3 : Real.log (qrat s W k ^ 2) = 2 * Real.log (qrat s W k) := by
            rw [Real.log_pow]
            norm_num
          rw [h3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h1
          have hh : (30:ℝ) / μ = 2 * (15 / μ) := by ring
          linarith [h1, hh]
        refine ⟨hinv1, hinv2, ?_⟩
        have hg2 : (30:ℝ) * (((k + 1 : ℕ) : ℝ) + 1) / μ = 30 * (((k : ℝ) + 1) + 1) / μ := by
          push_cast; ring
        rw [hg2]
        rw [Eerr_succ s W k (by linarith) hlampos hfk hfk1]
        calc |Eerr s W k + Real.log (qrat s W k)|
            ≤ |Eerr s W k| + |Real.log (qrat s W k)| := abs_add_le _ _
          _ ≤ 30 * (k + 1) / μ + 15 / μ := by
              push_cast
              linarith [hErrk, hratio]
          _ ≤ 30 * ((k + 1) + 1) / μ := by
              push_cast
              rw [← add_div]
              apply div_le_div_of_nonneg_right _ hμpos.le
              ring_nf
              linarith
    obtain ⟨_, _, hErr⟩ := hP (n - 1) (by omega)
    have hgoal : |Eerr s W (n - 1)| = |Real.log (frob (Nmat s W (n - 1)))
        - (∑ j ∈ Finset.range n, Real.log (s j))
        - (∑ j ∈ Finset.range (n - 1), Real.log ‖W j 0 0‖)| := by
      unfold Eerr
      rw [show n - 1 + 1 = n from by omega]
    rw [hgoal] at hErr
    have hcast : ((n - 1 : ℕ) + 1 : ℝ) = (n : ℝ) := by
      have hh : n - 1 + 1 = n := by omega
      exact_mod_cast hh
    rw [hcast] at hErr
    have hnn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc _ ≤ 30 * (n : ℝ) / μ := hErr
      _ ≤ 450 * (n : ℝ) / μ := by
          rw [div_le_div_iff₀ hμpos hμpos]
          nlinarith
  · -- ## the crude case: `n ≤ 3`
    have hn3 : n ≤ 3 := by
      have h : (n : ℝ) < 4 := by linarith
      have h2 : n < 4 := by exact_mod_cast h
      omega
    have hL23 : (23:ℝ) / 100 ≤ 1 / μ - 2 / (μ ^ 2 - 1) ^ 2 := Lmu_ge_23 μ hμ (le_of_lt (by linarith : μ < 4))
    have hu0 : rB s W 0 ≤ (1 / 3) * rA s W 0 := by
      rw [rB_zero s W hs0.le, rA_zero s W hs0.le, inv_le_iff_one_le_mul₀ hs0]
      have h2 := (hσμ 0 (by omega)).1
      nlinarith [h2, hs0]
    have hA0 : 0 < rA s W 0 := by rwa [rA_zero s W hs0.le]
    have hbnd0 : |Real.log (qrat s W 0)| ≤ 4 := by
      have h1 : |Real.log (((rA s W 1) ^ 2 + (rB s W 1) ^ 2)
          / ((s 1) ^ 2 * (‖W 0 0 0‖) ^ 2 * ((rA s W 0) ^ 2 + (rB s W 0) ^ 2)))| ≤ 8 :=
        ratio_bound_crude (s 1) (‖W 0 0 0‖) (‖W 0 0 1‖) (rA s W 0) (rB s W 0) (rA s W 1) (rB s W 1)
          (hσ 1 (by omega)) (by have := (hσμ 0 (by omega)).2; nlinarith)
          (norm_nonneg _) (norm_nonneg _) (le_trans hL23 (hlam 0 (by omega)))
          (lamW_sq_add_rhoW_sq W 0 (hW 0 (by omega)).2) hA0 (rB_nonneg s W 0) (rB_nonneg s W 1)
          hu0 (rA_succ_le s W 0 (by linarith)) (rA_succ_ge s W 0 (by linarith))
          (rB_succ_le s W 0 (by linarith) (hW 0 (by omega)).2 (hW 0 (by omega)).1)
      have hden : (s 1 * ‖W 0 0 0‖ * frob (Nmat s W 0)) ^ 2
          = (s 1) ^ 2 * (‖W 0 0 0‖) ^ 2 * ((rA s W 0) ^ 2 + (rB s W 0) ^ 2) := by
        rw [mul_pow, mul_pow, rA_sq_add_rB_sq]
      have h2 : qrat s W 0 ^ 2 = ((rA s W 1) ^ 2 + (rB s W 1) ^ 2)
          / ((s 1) ^ 2 * (‖W 0 0 0‖) ^ 2 * ((rA s W 0) ^ 2 + (rB s W 0) ^ 2)) := by
        rw [qrat, div_pow, rA_sq_add_rB_sq, hden]
      rw [← h2] at h1
      have h3 : Real.log (qrat s W 0 ^ 2) = 2 * Real.log (qrat s W 0) := by
        rw [Real.log_pow]; norm_num
      rw [h3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h1
      linarith
    have he0 : |Eerr s W 0| ≤ 1 / 128 := by
      rw [Eerr_zero s W hs0]
      have h1 : 0 < 1 + ((s 0) ^ 4)⁻¹ := by positivity
      have h2 := Real.log_le_sub_one_of_pos h1
      have h3 : 0 ≤ Real.log (1 + ((s 0) ^ 4)⁻¹) :=
        Real.log_nonneg (by linarith [show (0:ℝ) ≤ ((s 0) ^ 4)⁻¹ by positivity])
      have h4 : ((s 0) ^ 4)⁻¹ ≤ 1 / 64 := by
        have hq := (hσμ 0 (by omega)).1
        have hq8 : (8:ℝ) ≤ μ ^ 2 - 1 := by nlinarith [hμ]
        have hq4 : (64:ℝ) ≤ (s 0) ^ 4 := by nlinarith [hq, hq8, sq_nonneg (s 0)]
        have hab : (0:ℝ) < (s 0) ^ 4 := pow_pos hs0 4
        calc ((s 0) ^ 4)⁻¹ ≤ ((64:ℝ))⁻¹ := (inv_le_inv₀ hab (by norm_num)).mpr hq4
          _ = 1 / 64 := by norm_num
      rw [abs_of_nonneg (by linarith [h3])]
      linarith [h2, h4]
    have hfeq1 : Eerr s W 1 = Eerr s W 0 + Real.log (qrat s W 0) := by
      rw [Eerr_succ s W 0 (by linarith) (by have := hlam 0 (by omega); nlinarith [hL23, this, norm_nonneg (W 0 0 0)])
        (frob_Nmat_pos s W 0 (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
          (fun j hj => (hW j (by omega)).2))
        (frob_Nmat_pos s W 1 (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
          (fun j hj => (hW j (by omega)).2))]
    interval_cases n
    · -- n = 2
      change |Eerr s W (2 - 1)| ≤ 450 * (2 : ℝ) / μ
      rw [show 2 - 1 = 1 from rfl, hfeq1]
      have h4 := abs_add_le (Eerr s W 0) (Real.log (qrat s W 0))
      have : (450:ℝ) * 2 / μ ≥ 225 := by
        rw [ge_iff_le, le_div_iff₀ hμpos]
        nlinarith [hμ]
      linarith
    · -- n = 3
      change |Eerr s W (3 - 1)| ≤ 450 * (3 : ℝ) / μ
      have hσ1 : (1:ℝ) ≤ s 1 := hσ 1 (by omega)
      have hσ2 : (1:ℝ) ≤ s 2 := hσ 2 (by omega)
      have hW0 := hW 0 (by omega)
      have hW1 := hW 1 (by omega)
      have hfeq2 : Eerr s W 2 = Eerr s W 0 + Real.log (qrat s W 0) + Real.log (qrat s W 1) := by
        rw [Eerr_succ s W 1 (by linarith) (by have := hlam 1 (by omega); nlinarith [hL23, this, norm_nonneg (W 1 0 0)])
          (frob_Nmat_pos s W 1 (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
            (fun j hj => (hW j (by omega)).2))
          (frob_Nmat_pos s W 2 (fun j hj => ne_of_gt (lt_of_lt_of_le zero_lt_one (hσ j (by omega))))
            (fun j hj => (hW j (by omega)).2))]
        rw [hfeq1]
      rw [show 3 - 1 = 2 from rfl, hfeq2]
      have hu1 : rB s W 1 ≤ (1 / 3) * rA s W 1 := by
        have hb1 := rB_succ_le s W 0 (by linarith) (hW 0 (by omega)).2 (hW 0 (by omega)).1
        have ha1 := rA_succ_ge s W 0 (by linarith)
        rw [rA_zero s W hs0.le, rB_zero s W hs0.le] at hb1 ha1
        simp only [lamW, rhoW, Nat.zero_add, Nat.reduceAdd] at hb1 ha1
        have ha1' : ‖W 0 0 0‖ ≤ 1 := by
          have h := unitary_entry01_sq (W 0) (hW 0 (by omega)).2
          nlinarith [norm_nonneg (W 0 1)]
        have hnum := crude_u1_num μ (s 0) (s 1) (‖W 0 0 0‖) (‖W 0 0 1‖) hμ (by linarith)
          (by have := (hσμ 0 (by omega)).1; nlinarith) (by have := (hσμ 0 (by omega)).2; nlinarith)
          hs0 hs1p (hlam 0 (by omega)) ha1' (norm_nonneg _)
          (unitary_entry01_sq (W 0) (hW 0 (by omega)).2) (norm_nonneg _)
        linarith [hb1, ha1, hnum]
      have hA1 : 0 < rA s W 1 := by
        have hb1 := rA_succ_ge s W 0 (by linarith)
        rw [rA_zero s W hs0.le, rB_zero s W hs0.le] at hb1
        have h1 : 0 < ‖W 0 0 0‖ * s 0 - ‖W 0 0 1‖ * (s 0)⁻¹ := by
          have hlam23 : (23:ℝ) / 100 ≤ ‖W 0 0 0‖ ^ 2 := le_trans hL23 (hlam 0 (by omega))
          have hρ : ‖W 0 0 1‖ ^ 2 = 1 - ‖W 0 0 0‖ ^ 2 := unitary_entry01_sq (W 0) (hW 0 (by omega)).2
          have hσ0 : (8:ℝ) ≤ (s 0) ^ 2 := by have := (hσμ 0 (by omega)).1; nlinarith [hμ]
          have hρ1 : ‖W 0 0 1‖ ≤ 1 := by nlinarith [hρ, sq_nonneg (‖W 0 0 1‖)]
          have hls1 : 1 < ‖W 0 0 0‖ * s 0 ^ 2 := by
            have h0 : (0:ℝ) ≤ ‖W 0 0 0‖ := norm_nonneg _
            nlinarith [hlam23, hσ0, h0, sq_nonneg (s 0), hs0,
              mul_nonneg (by linarith : (0:ℝ) ≤ ‖W 0 0 0‖) (sq_nonneg (s 0))]
          have h2 : 0 < ‖W 0 0 0‖ * s 0 * s 0 - ‖W 0 0 1‖ := by nlinarith [hls1, hρ1]
          have h3 : ‖W 0 0 0‖ * s 0 - ‖W 0 0 1‖ * (s 0)⁻¹
              = (‖W 0 0 0‖ * s 0 * s 0 - ‖W 0 0 1‖) / s 0 := by field_simp
          rw [h3]
          exact div_pos h2 hs0
        simp only [lamW, rhoW, Nat.zero_add, Nat.reduceAdd] at hb1
        nlinarith [hb1, h1, hs1p]
      have hbnd1 : |Real.log (qrat s W 1)| ≤ 4 := by
        have h1 : |Real.log (((rA s W 2) ^ 2 + (rB s W 2) ^ 2)
            / ((s 2) ^ 2 * (‖W 1 0 0‖) ^ 2 * ((rA s W 1) ^ 2 + (rB s W 1) ^ 2)))| ≤ 8 :=
          ratio_bound_crude (s 2) (‖W 1 0 0‖) (‖W 1 0 1‖) (rA s W 1) (rB s W 1) (rA s W 2) (rB s W 2)
            hσ2
            (by have hq1 := (hσμ 1 (by omega)).2
                have hq8 : (8:ℝ) ≤ μ ^ 2 - 1 := by nlinarith [hμ]
                nlinarith [hq1, hq8])
            (norm_nonneg _) (norm_nonneg _) (le_trans hL23 (hlam 1 (by omega)))
            (lamW_sq_add_rhoW_sq W 1 (hW 1 (by omega)).2) hA1 (rB_nonneg s W 1) (rB_nonneg s W 2)
            hu1 (rA_succ_le s W 1 (by linarith)) (rA_succ_ge s W 1 (by linarith))
            (rB_succ_le s W 1 (by linarith) (hW 1 (by omega)).2 (hW 1 (by omega)).1)
        have hden : (s 2 * ‖W 1 0 0‖ * frob (Nmat s W 1)) ^ 2
            = (s 2) ^ 2 * (‖W 1 0 0‖) ^ 2 * ((rA s W 1) ^ 2 + (rB s W 1) ^ 2) := by
          rw [mul_pow, mul_pow, rA_sq_add_rB_sq]
        have h2 : qrat s W 1 ^ 2 = ((rA s W 2) ^ 2 + (rB s W 2) ^ 2)
            / ((s 2) ^ 2 * (‖W 1 0 0‖) ^ 2 * ((rA s W 1) ^ 2 + (rB s W 1) ^ 2)) := by
          rw [qrat, div_pow, rA_sq_add_rB_sq, hden]
        rw [← h2] at h1
        have h3 : Real.log (qrat s W 1 ^ 2) = 2 * Real.log (qrat s W 1) := by
          rw [Real.log_pow]; norm_num
        rw [h3, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h1
        linarith
      have h4 := abs_add_le (Eerr s W 0 + Real.log (qrat s W 0)) (Real.log (qrat s W 1))
      have h5 := abs_add_le (Eerr s W 0) (Real.log (qrat s W 0))
      have : (450:ℝ) * 3 / μ ≥ 300 := by
        rw [ge_iff_le, le_div_iff₀ hμpos]
        nlinarith [hμ]
      linarith


end Work.TMC7Core.Avalanche
