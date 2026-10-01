import Mathlib
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.f1_deriv
import Submission.Work.LinnikAreas.A5.f1_iteratedDeriv_two
import Submission.Work.LinnikAreas.A5.f1_deriv_at_K

namespace Work.LinnikAreas.A5

/-
Elementary data for HB's test function f₁(t) = sinh((K-t)λ) on [0,K] (definition
`Work.LinnikAreas.A5.f1` in `Submission/Work/LinnikAreas/A5/Basic.lean`): continuity on [0,∞),
C² on (0,K) with second derivative λ² sinh((K-t)λ) bounded by λ² sinh(Kλ), the bounds
|f₁| ≤ sinh(Kλ) on [0,K], f₁ ≥ 0, and |f₁'| ≤ λ cosh(Kλ) on [0,K].  These are exactly the
"Condition 1" hypotheses of HB 5.2 with x₀ = K and B = λ²sinh(Kλ).
-/
theorem f1_data (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    ContinuousOn (Work.LinnikAreas.A5.f1 K lam) (Set.Ici 0) ∧
    ContDiffOn ℝ 2 (Work.LinnikAreas.A5.f1 K lam) (Set.Ioo 0 K) ∧
    (∀ t ∈ Set.Ioo (0:ℝ) K, ‖iteratedDeriv 2 (Work.LinnikAreas.A5.f1 K lam) t‖
        ≤ lam ^ 2 * Real.sinh (K * lam)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K, ‖Work.LinnikAreas.A5.f1 K lam t‖ ≤ Real.sinh (K * lam)) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.f1 K lam t) ∧
    (∀ t ∈ Set.Icc (0:ℝ) K,
        ‖deriv (Work.LinnikAreas.A5.f1 K lam) t‖ ≤ lam * Real.cosh (K * lam)) := by
  have hcont : ContinuousOn (f1 K lam) (Set.Ici 0) := (continuous_f1 K lam).continuousOn
  -- `f₁` is C² on the open interval, where it agrees with the smooth branch `sinh((K-t)λ)`
  have hcd : ContDiffOn ℝ 2 (f1 K lam) (Set.Ioo 0 K) := by
    have hψ : ContDiff ℝ 2 (fun t : ℝ => Real.sinh ((K - t) * lam)) := by fun_prop
    exact hψ.contDiffOn.congr (fun t ht => f1_of_le ht.2.le)
  -- second derivative bound: `|f₁''(t)| = λ² sinh((K-t)λ) ≤ λ² sinh(Kλ)` for `0 < t < K`
  have hd2 : ∀ t ∈ Set.Ioo (0:ℝ) K,
      ‖iteratedDeriv 2 (f1 K lam) t‖ ≤ lam ^ 2 * Real.sinh (K * lam) := by
    intro t ht
    rw [f1_iteratedDeriv_two K lam ht]
    have h1 : (0:ℝ) ≤ (K - t) * lam := mul_nonneg (by linarith [ht.2]) hlam.le
    have hnn : 0 ≤ lam ^ 2 * Real.sinh ((K - t) * lam) :=
      mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr h1)
    rw [Real.norm_of_nonneg hnn]
    have hmono : Real.sinh ((K - t) * lam) ≤ Real.sinh (K * lam) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith [ht.1]) hlam.le)
    exact mul_le_mul_of_nonneg_left hmono (by positivity : (0:ℝ) ≤ lam ^ 2)
  -- size bound: `0 ≤ f₁(t) = sinh((K-t)λ) ≤ sinh(Kλ)` on `[0,K]`
  have hbnd : ∀ t ∈ Set.Icc (0:ℝ) K, ‖f1 K lam t‖ ≤ Real.sinh (K * lam) := by
    intro t ht
    rw [f1_of_le ht.2]
    have hnn : 0 ≤ Real.sinh ((K - t) * lam) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg (by linarith [ht.2]) hlam.le)
    rw [Real.norm_of_nonneg hnn]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith [ht.1]) hlam.le)
  -- nonnegativity everywhere
  have hnonneg : ∀ t : ℝ, 0 ≤ f1 K lam t := by
    intro t
    by_cases h : t ≤ K
    · rw [f1_of_le h]
      exact Real.sinh_nonneg_iff.mpr (mul_nonneg (by linarith) hlam.le)
    · rw [f1_of_ge (not_le.mp h).le]
  -- first derivative bound on `[0,K]`
  have hdbnd : ∀ t ∈ Set.Icc (0:ℝ) K,
      ‖deriv (f1 K lam) t‖ ≤ lam * Real.cosh (K * lam) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · have hd : deriv (f1 K lam) t = -lam * Real.cosh ((K - t) * lam) := f1_deriv K lam hlt
      have hc : 0 < Real.cosh ((K - t) * lam) := Real.cosh_pos _
      have habsval : ‖-lam * Real.cosh ((K - t) * lam)‖
          = lam * Real.cosh ((K - t) * lam) := by
        rw [Real.norm_eq_abs]
        rw [show -lam * Real.cosh ((K - t) * lam)
              = -(lam * Real.cosh ((K - t) * lam)) by ring]
        rw [abs_neg, abs_of_nonneg (mul_nonneg hlam.le hc.le)]
      rw [hd, habsval]
      have habs : |(K - t) * lam| ≤ |K * lam| := by
        rw [abs_of_nonneg (mul_nonneg (by linarith [ht.2]) hlam.le),
            abs_of_nonneg (mul_nonneg hK.le hlam.le)]
        exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) hlam.le
      exact mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.mpr habs) hlam.le
    · -- at the right endpoint `t = K` the function has a corner, and `deriv` takes its
      -- convention value `0` there
      rw [heq, f1_deriv_at_K K lam (ne_of_gt hlam), norm_zero]
      exact mul_nonneg hlam.le (Real.cosh_pos _).le
  exact ⟨hcont, hcd, hd2, hbnd, hnonneg, hdbnd⟩

end Work.LinnikAreas.A5
