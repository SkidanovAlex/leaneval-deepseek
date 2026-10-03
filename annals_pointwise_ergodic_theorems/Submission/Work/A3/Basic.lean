import Mathlib
import Submission.Work.A3.Defs

/-!
# Elementary lemmas for Area A3 (the `ℓ^p`-improving estimate)

Basic facts about the objects of `Submission/Work/A3/Defs.lean`:

* `kmtFhat_eq_sum` — the Fourier transform of a function vanishing off a finset is a finite sum;
* `norm_kmtMul_le` — the multiplier of the averaging operator is bounded by `1`;
* `norm_kmtFhat_le` — the Fourier transform is bounded by the `ℓ¹` norm;
* `summable_norm_sq_iff_count`, `summable_norm_rpow_iff_count` — sums over `ℤ` of powers of a
  finitely supported function are summable.

These are the bookkeeping facts used by the assembly of `Work.KMTContract.AreaA3` in
`Submission/Work/KMTAreas/area_A3.lean`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The Fourier transform of a function vanishing off `t` is the corresponding finite sum. -/
lemma kmtFhat_eq_sum {f : ℤ → ℂ} {t : Finset ℤ} (ht : ∀ x ∉ t, f x = 0) (θ : ℝ) :
    kmtFhat f θ = ∑ x ∈ t, f x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ))) := by
  rw [kmtFhat, tsum_eq_sum]
  intro x hx
  rw [ht x hx, zero_mul]

/-- The multiplier `m_N(θ) = N⁻¹ ∑_{n≤N} e(-2πi θ Q(n))` is bounded by `1`. -/
lemma norm_kmtMul_le (Q : ℤ[X]) (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) : ‖kmtMul Q N θ‖ ≤ 1 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hsum : ‖∑ n ∈ Finset.Icc 1 N,
      Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))‖ ≤ (N:ℝ) := by
    calc ‖∑ n ∈ Finset.Icc 1 N,
            Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))‖
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ‖Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, (1:ℝ) := by
          apply Finset.sum_congr rfl; intro n _
          rw [Complex.norm_exp]; simp
      _ ≤ (N:ℝ) := by simp
  rw [kmtMul, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N:ℝ)⁻¹ * ‖∑ n ∈ Finset.Icc 1 N,
          Complex.exp (-(2 * Real.pi * Complex.I * (((Q.eval (n : ℤ) : ℤ) : ℝ) * θ)))‖
      ≤ (N:ℝ)⁻¹ * (N:ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

/-- The Fourier transform of a finitely supported function is bounded by its `ℓ¹` norm. -/
lemma norm_kmtFhat_le {f : ℤ → ℂ} {t : Finset ℤ} (ht : ∀ x ∉ t, f x = 0) (θ : ℝ) :
    ‖kmtFhat f θ‖ ≤ ∑ x ∈ t, ‖f x‖ := by
  rw [kmtFhat_eq_sum ht θ]
  calc ‖∑ x ∈ t, f x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))‖
      ≤ ∑ x ∈ t, ‖f x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))‖ :=
        norm_sum_le _ _
    _ = ∑ x ∈ t, ‖f x‖ := by
        apply Finset.sum_congr rfl; intro x _
        rw [norm_mul, Complex.norm_exp]; simp

/-- Powers of a finitely supported function are summable over `ℤ`. -/
lemma summable_norm_sq_of_finsupp {u : ℤ → ℂ} {t : Finset ℤ} (ht : ∀ x ∉ t, u x = 0) :
    Summable (fun x : ℤ => ‖u x‖ ^ 2) := by
  refine summable_of_ne_finset_zero (s := t) ?_
  intro x hx
  rw [ht x hx]; simp

/-- `r`-th powers (`r > 0`) of a finitely supported function are summable over `ℤ`. -/
lemma summable_norm_rpow_of_finsupp {u : ℤ → ℂ} {t : Finset ℤ} (ht : ∀ x ∉ t, u x = 0)
    {r : ℝ} (hr : 0 < r) : Summable (fun x : ℤ => ‖u x‖ ^ r) := by
  refine summable_of_ne_finset_zero (s := t) ?_
  intro x hx
  rw [ht x hx]
  simp [Real.zero_rpow hr.ne']

end

end Work.A3
