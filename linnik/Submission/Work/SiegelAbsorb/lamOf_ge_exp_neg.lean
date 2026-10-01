import Mathlib
import Submission.Work.LinnikAreas.lamOfEps200

/-!
# `λ₁ ≫ q^{-a}` for every `a > 1/200`

Siegel's uniform bound in the `λ`-normalisation
(`Work.LinnikAreas.lamOfEps200`) reads

`C · log q / q^{1/200} ≤ λ₁ = (1 - β₁) log q`

for an absolute constant `C > 0`, every `q ≥ 2` and every Siegel datum `(χ₁, β₁)` mod `q`.
Since `q^{ε}` grows slower than `log q`, this implies the *pure power* lower bound

`q^{-a} = exp(-a log q) ≤ λ₁`

for every exponent `a > 1/200` (with the threshold `q₀` depending on `a`).

Indeed, writing `q^{-a} = q^{1/200 - a} · q^{-1/200}` with `1/200 - a < 0`, the first
factor is `≤ 1`, which gives `q^{-a} ≤ q^{-1/200} ≤ C log q · q^{-1/200}` as soon as
`C log q ≥ 1` (true for `q ≥ q₀`, depending on `C`).

The lemma is stated with a `q₀` (rather than a fixed threshold) because the constant `C`
produced by Siegel's theorem is ineffective.
-/

namespace Work.SiegelAbsorb

open scoped Classical

/-- For `C > 0` there is `N` with `1 ≤ C * log q` for every `q ≥ N`: the logarithm is
unbounded on the naturals. (The threshold is non-effective in `C`, as it must be.) -/
lemma exists_one_le_mul_log {C : ℝ} (hC : 0 < C) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → 1 ≤ C * Real.log q := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (1 / C))
  refine ⟨N, fun q hq => ?_⟩
  have h1 : Real.exp (1 / C) ≤ (q : ℝ) := le_trans hN (by exact_mod_cast hq)
  have h2 : 1 / C ≤ Real.log q := by
    have h := Real.log_le_log (Real.exp_pos (1 / C)) h1
    rwa [Real.log_exp] at h
  have h3 : C * (1 / C) = 1 := by field_simp
  calc (1 : ℝ) = C * (1 / C) := h3.symm
    _ ≤ C * Real.log q := mul_le_mul_of_nonneg_left h2 hC.le

theorem lamOf_ge_exp_neg {a : ℝ} (ha : 1 / 200 < a) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
      χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
      Real.exp (-(a * Real.log q)) ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) := by
  -- Siegel's uniform lower bound `C log q / q^{1/200} ≤ λ₁`
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.lamOfEps200
  -- threshold beyond which `C log q ≥ 1`
  obtain ⟨N, hN⟩ := exists_one_le_mul_log hCpos
  refine ⟨max 2 N, ?_⟩
  intro q hq hne χ₁ β₁ hχ hsq hβ hz
  have hq2 : 2 ≤ q := le_trans (le_max_left 2 N) hq
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h1q : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hSie := hC q hq2 χ₁ β₁ hχ hsq hβ hz
  have hone : 1 ≤ C * Real.log q := hN q (le_trans (le_max_right 2 N) hq)
  -- `exp (-(a log q)) = q^{-a}`
  have hExp : Real.exp (-(a * Real.log q)) = (q : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos hqpos]
    congr 1
    ring
  -- split the exponent: `-a = (1/200 - a) + (-(1/200))`
  have hsplit : (q : ℝ) ^ (-a) = (q : ℝ) ^ (1 / 200 - a) * (q : ℝ) ^ (-(1 / 200 : ℝ)) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    ring
  -- the negative-exponent factor is `≤ 1`
  have hle1 : (q : ℝ) ^ (1 / 200 - a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1q (by linarith)
  have hposinv : 0 < (q : ℝ) ^ (-(1 / 200 : ℝ)) := Real.rpow_pos_of_pos hqpos _
  have hA : (q : ℝ) ^ (1 / 200 - a) * (q : ℝ) ^ (-(1 / 200 : ℝ))
      ≤ 1 * (q : ℝ) ^ (-(1 / 200 : ℝ)) :=
    mul_le_mul_of_nonneg_right hle1 hposinv.le
  have hB : (1 : ℝ) * (q : ℝ) ^ (-(1 / 200 : ℝ))
      ≤ (C * Real.log q) * (q : ℝ) ^ (-(1 / 200 : ℝ)) :=
    mul_le_mul_of_nonneg_right hone hposinv.le
  have hCeq : (C * Real.log q) * (q : ℝ) ^ (-(1 / 200 : ℝ))
      = C * Real.log q / (q : ℝ) ^ (1 / 200 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hqpos), div_eq_mul_inv]
    ring
  rw [hExp, hsplit]
  calc (q : ℝ) ^ (1 / 200 - a) * (q : ℝ) ^ (-(1 / 200 : ℝ))
      ≤ 1 * (q : ℝ) ^ (-(1 / 200 : ℝ)) := hA
    _ ≤ (C * Real.log q) * (q : ℝ) ^ (-(1 / 200 : ℝ)) := hB
    _ = C * Real.log q / (q : ℝ) ^ (1 / 200 : ℝ) := hCeq
    _ ≤ Work.LinnikContract.lamOf q (β₁ : ℂ) := hSie

end Work.SiegelAbsorb
