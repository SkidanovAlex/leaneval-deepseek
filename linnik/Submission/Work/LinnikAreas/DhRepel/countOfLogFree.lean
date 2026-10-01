import Mathlib
import Submission.Work.LinnikContract.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas.DhRepel

/-- **From a log-free count `C·(log q)^A` (`A < 1`) to the `C'·log q` form (`C' < 10`).**  For
`q` so large that `log q ≥ C^{1/(1-A)}` one has `C·(log q)^A ≤ log q`, since
`log q = (log q)^A·(log q)^{1-A}` and `C ≤ (log q)^{1-A}`. -/
theorem countOfLogFree
    (h : ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ A < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
        t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧
            Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
          ≤ C * (Real.log (q : ℝ)) ^ A) :
    ∃ C' : ℝ, 0 < C' ∧ C' < 10 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ, 0 ≤ t →
        t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
        (∑ᶠ u : ℂ, if Work.LinnikContract.zeroMult χ u ≠ 0 ∧
            |u.im| ≤ 10 * Real.log (q : ℝ) ∧
            Work.LinnikContract.lamOf q u ≤ t
          then (Work.LinnikContract.zeroMult χ u : ℝ) else 0)
          ≤ C' * Real.log (q : ℝ) := by
  obtain ⟨C, A, hC, hA, hAlt, q₀, hb⟩ := h
  set Y : ℝ := C ^ (1 / (1 - A)) with hY
  have h1A : 0 < 1 - A := by linarith
  refine ⟨1, one_pos, by norm_num, max q₀ (Nat.ceil (Real.exp Y) + 2), ?_⟩
  intro q hq _inst χ hχ t ht0 htle
  have hq₀ : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqe : Nat.ceil (Real.exp Y) + 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hYlog : Y ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp Y < ((Nat.ceil (Real.exp Y) + 2 : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.exp Y)
      push_cast
      linarith
    have h2 : Real.log (Real.exp Y) < Real.log (((Nat.ceil (Real.exp Y) + 2 : ℕ) : ℝ)) :=
      Real.log_lt_log (Real.exp_pos Y) h1
    have h3 : Real.log (((Nat.ceil (Real.exp Y) + 2 : ℕ) : ℝ)) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hqe)
    rw [Real.log_exp] at h2
    linarith
  have hCY : C = Y ^ (1 - A) := by
    rw [show Y = C ^ (1 / (1 - A)) from hY, ← Real.rpow_mul hC.le]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt h1A), Real.rpow_one]
  have hθ : C ≤ (Real.log (q : ℝ)) ^ (1 - A) := by
    rw [hCY]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) hYlog h1A.le
  have hkey : C * (Real.log (q : ℝ)) ^ A ≤ Real.log (q : ℝ) := by
    have h1 : C * (Real.log (q : ℝ)) ^ A
        ≤ (Real.log (q : ℝ)) ^ (1 - A) * (Real.log (q : ℝ)) ^ A :=
      mul_le_mul_of_nonneg_right hθ (Real.rpow_nonneg hlogpos.le A)
    have h2 : (Real.log (q : ℝ)) ^ (1 - A) * (Real.log (q : ℝ)) ^ A = Real.log (q : ℝ) := by
      rw [← Real.rpow_add hlogpos (1 - A) A, show (1 - A) + A = 1 by ring, Real.rpow_one]
    linarith
  simpa only [one_mul] using le_trans (hb q hq₀ χ hχ t ht0 htle) hkey


end Work.LinnikAreas.DhRepel
