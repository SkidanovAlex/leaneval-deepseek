import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.Analysis.Asymptotics.invSq_zeroSum_of_count

open Complex DirichletCharacter Metric MeromorphicOn Function
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Linnik

/-!
# Zero sum with the inverse-square kernel for the completed Dirichlet L-function

For a non-trivial primitive character `χ mod N`, the divisor of the completed L-function
`Λ(s) = completedLFunction χ s` is supported on the zeros of `Λ` (all inside the critical
strip `0 < Re < 1`), and its coefficients are the zero multiplicities.  The requested lemma
bounds the weighted zero sum

`Σᶠ_u |divisor Λ (closedBall 0 R) u| · 1/(1 + ‖s - u‖²)`

by `C · (log N + log (2 + ‖s‖) + 2)`, uniformly in the disk radius `R` and in `s`.

The proof splits into two parts.

* `completedL_ballZeroCount` gives, uniformly in the centre `a` and the radius `ρ ≥ 1`,
  the ball count bound `Σᶠ_u D_{closedBall a ρ}(u) ≤ c(ρ+1)(log(‖a‖+ρ+2) + log N + 2)`.
  Restricting `D_{closedBall 0 ρ₀}` (with `ρ₀ = max R 1`) to `closedBall a ρ` and comparing
  pointwise with `D_{closedBall a ρ}` (they agree on the intersection, and on the complement
  of `closedBall 0 ρ₀` the restricted coefficient vanishes) transfers this bound to the
  function `m = D_{closedBall 0 ρ₀}`.

* The purely analytic dyadic estimate `invSq_zeroSum_of_count` converts a ball-count bound
  of this shape into the quadratic-decay kernel bound.
-/

theorem zeroSum_invSq_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ∀ R : ℝ,
      (∑ᶠ u : ℂ, |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ)| * (1 / (1 + ‖s - u‖ ^ 2)))
        ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  classical
  rcases completedL_ballZeroCount χ hχ hχprim with ⟨c0, hc0⟩
  set c : ℝ := max c0 0 with hcdef
  have hc : 0 ≤ c := le_max_right c0 0
  have hN : 0 ≤ Real.log (N : ℝ) := log_N_nonneg
  obtain ⟨C, hCpos, hCgen⟩ :=
    Commons.Analysis.Asymptotics.invSq_zeroSum_of_count (c := c) (q := Real.log (N : ℝ)) hc hN
  -- positivity of divisor coefficients at any point
  have Dnn : ∀ (cc : ℂ) (r : ℝ) (u : ℂ),
      0 ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall cc r) u : ℤ) : ℝ) := by
    intro cc r u
    by_cases h : u ∈ Metric.closedBall cc r
    · exact divisor_real_nonneg_of_analyticOnNhd (completedLFunction_analyticOnNhd χ hχ _) h
    · have hz : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall cc r) u = 0 := by
        rw [MeromorphicOn.divisor_def]; rw [if_neg]; intro hh; exact h hh.2
      rw [hz]; simp
  refine ⟨C, hCpos, ?_⟩
  intro s R
  set ρ0 : ℝ := max R 1 with hρ0def
  have hR1 : R ≤ ρ0 := le_max_left R 1
  set m : ℂ → ℝ := fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 ρ0) u : ℤ) : ℝ) with hmdef
  have hm_nonneg : ∀ u : ℂ, 0 ≤ m u := by
    intro u; simp only [hmdef]; exact Dnn 0 ρ0 u
  have hfin : Function.HasFiniteSupport m := divisor_real_finiteSupport χ hχ 0 ρ0
  have hcount : ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
        ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    intro a ρ hρ
    have hAnal : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) ρ0 ∪ Metric.closedBall a ρ) :=
      completedLFunction_analyticOnNhd χ hχ _
    have hpt : Set.indicator (Metric.closedBall a ρ) m ≤
        fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ) u : ℤ) : ℝ) := by
      intro u
      dsimp only
      rw [Set.indicator_apply]
      by_cases hu : u ∈ Metric.closedBall a ρ
      · rw [if_pos hu]
        simp only [hmdef]
        by_cases huR : u ∈ Metric.closedBall (0:ℂ) ρ0
        · rw [divisor_eq_closedBall_subset (f := DirichletCharacter.completedLFunction χ) hAnal huR hu]
        · have hz : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) ρ0) u = 0 := by
            rw [MeromorphicOn.divisor_def]; rw [if_neg]; intro hh; exact huR hh.2
          rw [hz]; simp only [Int.cast_zero]; exact Dnn a ρ u
      · rw [if_neg hu]; exact Dnn a ρ u
    have hsub : Function.support (Set.indicator (Metric.closedBall a ρ) m) ⊆ Function.support m := by
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hm0
      apply hu
      rw [Set.indicator_apply]
      by_cases h : u ∈ Metric.closedBall a ρ
      · rw [if_pos h, hm0]
      · rw [if_neg h]
    have hfs_l : Function.HasFiniteSupport (Set.indicator (Metric.closedBall a ρ) m) :=
      hfin.subset hsub
    have hfs_r : Function.HasFiniteSupport (fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ) u : ℤ) : ℝ)) :=
      divisor_real_finiteSupport χ hχ a ρ
    have h1 : (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
        ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ) u : ℤ) : ℝ) :=
      finsum_le_finsum' hfs_l hfs_r hpt
    have h2 := hc0 a ρ hρ
    have hlog_ap : 0 ≤ Real.log (‖a‖ + ρ + 2) := by
      apply Real.log_nonneg
      have : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
      linarith
    have hfac : 0 ≤ (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) :=
      mul_nonneg (by linarith) (by linarith)
    calc (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ) m u)
        ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ) u : ℤ) : ℝ) := h1
      _ ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := h2
      _ ≤ c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
          have hcc : c0 * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2))
              ≤ c * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right (le_max_left c0 0) hfac
          calc c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
              = c0 * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
            _ ≤ c * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := hcc
            _ = c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hbound := hCgen m hm_nonneg hfin hcount s
  have hAnalR : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0:ℂ) R ∪ Metric.closedBall (0:ℂ) ρ0) :=
    completedLFunction_analyticOnNhd χ hχ _
  have hpt2 : (fun u => |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ)| * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ fun u => m u * (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    show |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ)| * (1 / (1 + ‖s - u‖ ^ 2)) ≤ m u * (1 / (1 + ‖s - u‖ ^ 2))
    have hw : 0 ≤ (1 / (1 + ‖s - u‖ ^ 2) : ℝ) := by positivity
    have hDle : ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R) u : ℤ) : ℝ) ≤ m u := by
      simp only [hmdef]
      by_cases hu : u ∈ Metric.closedBall (0:ℂ) R
      · have hu0 : u ∈ Metric.closedBall (0:ℂ) ρ0 := Metric.closedBall_subset_closedBall hR1 hu
        rw [divisor_eq_closedBall_subset (f := DirichletCharacter.completedLFunction χ) hAnalR hu hu0]
      · have hz : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R) u = 0 := by
          rw [MeromorphicOn.divisor_def]; rw [if_neg]; intro hh; exact hu hh.2
        rw [hz]; simp only [Int.cast_zero]; exact hm_nonneg u
    rw [abs_of_nonneg (Dnn 0 R u)]
    exact mul_le_mul_of_nonneg_right hDle hw
  have hfs_f : Function.HasFiniteSupport (fun u => |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ)| * (1 / (1 + ‖s - u‖ ^ 2))) := by
    refine (divisor_real_finiteSupport χ hχ 0 R).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hd0
    exact hu (by simp [hd0])
  have hfs_g : Function.HasFiniteSupport (fun u => m u * (1 / (1 + ‖s - u‖ ^ 2))) :=
    hfin.mul_left (fun u => (1 / (1 + ‖s - u‖ ^ 2) : ℝ))
  have hle : (∑ᶠ u : ℂ, |(((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ)| * (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ ∑ᶠ u : ℂ, m u * (1 / (1 + ‖s - u‖ ^ 2)) :=
    finsum_le_finsum' hfs_f hfs_g hpt2
  refine le_trans hle ?_
  simpa only [add_comm, add_left_comm, add_assoc] using hbound

end Commons.NumberTheory.Linnik
