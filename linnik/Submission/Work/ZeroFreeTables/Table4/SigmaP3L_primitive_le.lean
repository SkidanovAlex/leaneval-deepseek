/-
# `SigmaP3L` at a higher level vs. at a lower level (Table 4, primitive step)

Heath-Brown's `Σ(s,χ)` of (8.4), in the coefficient-correct free-scale form
`Work.ZeroFreeTables.SigmaP3L`, is evaluated at a *primitive* character; in the
assembly it is evaluated at the modulus `q` of the `L`-function actually used.
The two differ only through `DirichletCharacter.changeLevel` on the common
modulus `N ∣ q`, and the difference is controlled by the non-coprime part of the
von Mangoldt series.

`SigmaP3L_changeLevel_diff` gives the absolute difference bound
`|Σ^q - Σ^N| ≤ (12/L) · (α S₁ + (α²/L) S₂ + (α³/L²) S₃)`, `α = a + λ₁`,
with `S_j = ∑_{p | q} (log p)^j / p`.  Feeding in the prime-factor estimates
`S_j ≤ C_j (log log q)^{j+1}` (`P9.primeFactors_logPow_div_le`) and using `L ≥ 1`
and `(log log q)^k ≤ (log log q + 2)^4` yields the one-sided bound

`Σ^q ≤ Σ^N + C (α + α² + α³) (log log q + 2)^4 / L`

with an absolute constant `C`.  The single extra wrinkle is that
`SigmaP3L_changeLevel_diff` is stated with `0 < a`, while here only `α = a + λ₁ ≥ 0`
is assumed; this is handled by the case `α = 0` (both sides vanish) and, for
`α > 0`, by replacing `(a, λ₁)` with `(α, 0)`, which does not change `SigmaP3L`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.LinnikContract.Defs

open scoped BigOperators

noncomputable section

namespace Work.ZeroFreeTables.Table4

/-- `hbWL` vanishes when `a + lam₁ = 0`. -/
lemma hbWL_eq_zero_of_add_eq_zero {L a lam₁ : ℝ} (n : ℕ) (h : a + lam₁ = 0) :
    Work.ZeroFreeTables.hbWL L a lam₁ n = 0 := by
  unfold Work.ZeroFreeTables.hbWL
  rw [h]
  ring

/-- `SigmaP3L` depends on `a, lam₁` only through `a + lam₁`. -/
lemma SigmaP3L_congr {N : ℕ} [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    {a a' lam₁ lam₁' : ℝ} (h : a + lam₁ = a' + lam₁') :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = Work.ZeroFreeTables.SigmaP3L N L χ s a' lam₁' := by
  unfold Work.ZeroFreeTables.SigmaP3L
  rw [h]

/-- `SigmaP3L` vanishes when `a + lam₁ = 0`. -/
lemma SigmaP3L_eq_zero_of_add_eq_zero {N : ℕ} [NeZero N] (L : ℝ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) {a lam₁ : ℝ} (h : a + lam₁ = 0) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁ = 0 := by
  unfold Work.ZeroFreeTables.SigmaP3L
  rw [h]
  simp

/-- For `q ≥ 3` and `k ≤ 4`, `(log log q)^k ≤ (log log q + 2)^4`. -/
lemma loglog_pow_le {q : ℕ} (hq : 3 ≤ q) {k : ℕ} (hk : k ≤ 4) :
    (Real.log (Real.log (q : ℝ))) ^ k ≤ (Real.log (Real.log (q : ℝ)) + 2) ^ 4 := by
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hlogq_gt1 : 1 < Real.log (q : ℝ) :=
    lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) hq3)
  have hu_gt0 : 0 < Real.log (Real.log (q : ℝ)) := Real.log_pos hlogq_gt1
  have hmono : Real.log (Real.log (q : ℝ)) ≤ Real.log (Real.log (q : ℝ)) + 2 := by linarith
  have hu2 : (1 : ℝ) ≤ Real.log (Real.log (q : ℝ)) + 2 := by linarith
  calc (Real.log (Real.log (q : ℝ))) ^ k
      ≤ (Real.log (Real.log (q : ℝ)) + 2) ^ k := pow_le_pow_left₀ hu_gt0.le hmono k
    _ ≤ (Real.log (Real.log (q : ℝ)) + 2) ^ 4 := pow_le_pow_right₀ hu2 hk

/-- The polynomial part of the error: the (absolute) change-of-level difference
bound of `SigmaP3L_changeLevel_diff`, once each prime-factor sum has been bounded
by `C_j · Z^4`, is dominated by `Cd C (α + α² + α³) Z^4 / L` with `C = C₁+C₂+C₃`. -/
lemma error_bound {q : ℕ} {L α Z : ℝ} (hL : 1 ≤ L) (hα : 0 ≤ α)
    {Cd C1 C2 C3 : ℝ} (hCd : 0 < Cd) (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3)
    (hS1 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ C1 * Z ^ 4)
    (hS2 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤ C2 * Z ^ 4)
    (hS3 : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) ≤ C3 * Z ^ 4) :
    Cd / L * (α * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ Cd * (C1 + C2 + C3) * (α + α ^ 2 + α ^ 3) * Z ^ 4 / L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have hL2inv : (L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith : (1:ℝ) ≤ L ^ 2)
  have hZ4nn : (0 : ℝ) ≤ Z ^ 4 := by positivity
  have key1 : α * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ α * (C1 * Z ^ 4) :=
    mul_le_mul_of_nonneg_left hS1 hα
  have key2 : α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ≤ α ^ 2 * (C2 * Z ^ 4) := by
    have h1 : α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        ≤ α ^ 2 / L * (C2 * Z ^ 4) := mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h2 : α ^ 2 / L ≤ α ^ 2 := by
      rw [div_eq_mul_inv]
      calc α ^ 2 * L⁻¹ ≤ α ^ 2 * 1 := mul_le_mul_of_nonneg_left hLinv (sq_nonneg α)
        _ = α ^ 2 := by ring
    calc α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
          ≤ α ^ 2 / L * (C2 * Z ^ 4) := h1
      _ ≤ α ^ 2 * (C2 * Z ^ 4) := mul_le_mul_of_nonneg_right h2 (by positivity)
  have key3 : α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ α ^ 3 * (C3 * Z ^ 4) := by
    have h1 : α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
        ≤ α ^ 3 / L ^ 2 * (C3 * Z ^ 4) := mul_le_mul_of_nonneg_left hS3 (by positivity)
    have h2 : α ^ 3 / L ^ 2 ≤ α ^ 3 := by
      rw [div_eq_mul_inv]
      calc α ^ 3 * (L ^ 2)⁻¹ ≤ α ^ 3 * 1 := mul_le_mul_of_nonneg_left hL2inv (pow_nonneg hα 3)
        _ = α ^ 3 := by ring
    calc α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
          ≤ α ^ 3 / L ^ 2 * (C3 * Z ^ 4) := h1
      _ ≤ α ^ 3 * (C3 * Z ^ 4) := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hP : α * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
      ≤ (α * C1 + α ^ 2 * C2 + α ^ 3 * C3) * Z ^ 4 := by
    nlinarith [key1, key2, key3]
  have hcoef : α * C1 + α ^ 2 * C2 + α ^ 3 * C3 ≤ (C1 + C2 + C3) * (α + α ^ 2 + α ^ 3) := by
    have hs : α ≤ α + α ^ 2 + α ^ 3 := by nlinarith [hα]
    have hs2 : α ^ 2 ≤ α + α ^ 2 + α ^ 3 := by nlinarith [hα]
    have hs3 : α ^ 3 ≤ α + α ^ 2 + α ^ 3 := by nlinarith [hα]
    have f1 : C1 * α ≤ C1 * (α + α ^ 2 + α ^ 3) := mul_le_mul_of_nonneg_left hs hC1.le
    have f2 : C2 * α ^ 2 ≤ C2 * (α + α ^ 2 + α ^ 3) := mul_le_mul_of_nonneg_left hs2 hC2.le
    have f3 : C3 * α ^ 3 ≤ C3 * (α + α ^ 2 + α ^ 3) := mul_le_mul_of_nonneg_left hs3 hC3.le
    nlinarith [f1, f2, f3]
  have hCL : (0 : ℝ) ≤ Cd / L := by positivity
  calc Cd / L * (α * (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        + α ^ 2 / L * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        + α ^ 3 / L ^ 2 * (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)))
      ≤ Cd / L * ((α * C1 + α ^ 2 * C2 + α ^ 3 * C3) * Z ^ 4) :=
        mul_le_mul_of_nonneg_left hP hCL
    _ ≤ Cd / L * ((C1 + C2 + C3) * (α + α ^ 2 + α ^ 3) * Z ^ 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hZ4nn) hCL
    _ = Cd * (C1 + C2 + C3) * (α + α ^ 2 + α ^ 3) * Z ^ 4 / L := by ring

theorem SigmaP3L_primitive_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N q : ℕ} [NeZero N] [NeZero q] (h : N ∣ q)
      (χ : DirichletCharacter ℂ N), χ ≠ 1 → 3 ≤ q → ∀ {s : ℂ}, 1 < s.re →
      ∀ {L a lam₁ : ℝ}, 1 ≤ L → Real.log (q : ℝ) ≤ L → 0 ≤ a + lam₁ →
      Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel h χ) s a lam₁ ≤
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          + C * ((a + lam₁) + (a + lam₁) ^ 2 + (a + lam₁) ^ 3)
              * (Real.log (Real.log (q : ℝ)) + 2) ^ 4 / L := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  refine ⟨Cd * (C1 + C2 + C3), by positivity, ?_⟩
  intro N q _ _ h χ hχ hq s hs L a lam₁ hL hlogq hα
  by_cases hα0 : a + lam₁ = 0
  · rw [SigmaP3L_eq_zero_of_add_eq_zero (N := q) L (DirichletCharacter.changeLevel h χ) s hα0,
        SigmaP3L_eq_zero_of_add_eq_zero (N := N) L χ s hα0]
    have hz : (a + lam₁) + (a + lam₁) ^ 2 + (a + lam₁) ^ 3 = 0 := by rw [hα0]; ring
    rw [hz]
    simp
  · set α : ℝ := a + lam₁ with hαdef
    set Z : ℝ := Real.log (Real.log (q : ℝ)) + 2 with hZdef
    have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hcongr : a + lam₁ = α + 0 := by rw [hαdef]; ring
    rw [SigmaP3L_congr L (DirichletCharacter.changeLevel h χ) s hcongr,
        SigmaP3L_congr L χ s hcongr]
    have hD := hCd (a := α) (lam₁ := 0) h χ hL hs hαpos (le_refl 0)
    simp only [add_zero] at hD
    have hupper := (abs_le.mp hD).2
    have hS1Z : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ)) ≤ C1 * Z ^ 4 := by
      have h := hC1 q hq
      simp only [pow_one] at h
      have hlp := loglog_pow_le (q := q) hq (k := 2) (by norm_num)
      rw [← hZdef] at hlp
      exact le_trans h (mul_le_mul_of_nonneg_left hlp hC1pos.le)
    have hS2Z : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤ C2 * Z ^ 4 := by
      have h := hC2 q hq
      have hlp := loglog_pow_le (q := q) hq (k := 3) (by norm_num)
      rw [← hZdef] at hlp
      exact le_trans h (mul_le_mul_of_nonneg_left hlp hC2pos.le)
    have hS3Z : (∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) ≤ C3 * Z ^ 4 := by
      have h := hC3 q hq
      have hlp := loglog_pow_le (q := q) hq (k := 4) (le_refl 4)
      rw [← hZdef] at hlp
      exact le_trans h (mul_le_mul_of_nonneg_left hlp hC3pos.le)
    have herr := error_bound (q := q) (L := L) (α := α) (Z := Z)
      hL hαpos.le hCdpos hC1pos hC2pos hC3pos hS1Z hS2Z hS3Z
    linarith [hupper, herr]

end Work.ZeroFreeTables.Table4
