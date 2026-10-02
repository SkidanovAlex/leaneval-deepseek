import Mathlib
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

namespace Work.LinnikAreas.Zeta1Aux

theorem zeta1_windowSum_le_ball11 {t : ℝ} (ht : |t| ≤ 5) :
    (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0))
      ≤ ((∑ᶠ u : ℂ,
          MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) 11) u : ℤ) : ℝ) := by
  classical
  have hR11 : |t| + 6 ≤ 11 := by
    have h := abs_nonneg t; linarith
  have han : ∀ U : Set ℂ, AnalyticOnNhd ℂ riemannZeta₁ U :=
    fun U z _ => differentiable_riemannZeta₁.analyticAt z
  -- finiteness of the two divisor supports
  have hdtfin : Function.HasFiniteSupport
      (fun u : ℂ => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u) :=
    (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6))).finiteSupport
      (isCompact_closedBall (0:ℂ) (|t|+6))
  have hd1fin : Function.HasFiniteSupport
      (fun u : ℂ => MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u) :=
    (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11)).finiteSupport
      (isCompact_closedBall (0:ℂ) 11)
  -- nonnegativity of the big-ball divisor
  have hd1nn : ∀ u : ℂ,
      (0:ℤ) ≤ MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (han (Metric.closedBall (0:ℂ) 11)) u
  -- agreement of the two divisors on the smaller ball
  have hagree : ∀ u : ℂ, u ∈ Metric.closedBall (0:ℂ) (|t|+6) →
      MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u
        = MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u := by
    intro u hu
    exact Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
      (a := 0) (b := 0) (ra := |t|+6) (rb := 11) (han _) hu
      (Metric.closedBall_subset_closedBall (x := (0:ℂ)) hR11 hu)
  -- the two explicit real-valued functions have finite support
  have hFfin : Function.HasFiniteSupport
      (fun u : ℂ =>
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) := by
    refine hdtfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp [h0])
  have hGfin : Function.HasFiniteSupport
      (fun u : ℂ =>
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ)) := by
    refine hd1fin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp [h0])
  -- pointwise comparison
  have hle : (fun u : ℂ =>
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0))
      ≤ (fun u : ℂ =>
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ)) := by
    intro u
    show ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)
        ≤ ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ)
    by_cases hu : u ∈ Metric.closedBall (0:ℂ) (|t|+6)
    · rw [hagree u hu]
      have hnn : (0:ℝ) ≤
          ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) := by
        exact_mod_cast hd1nn u
      have hind : (if |u.im - t| ≤ 3 then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
      calc ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) *
              (if |u.im - t| ≤ 3 then 1 else 0)
          ≤ ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hind hnn
        _ = ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) :=
            mul_one _
    · have h0 : MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6)) u = 0 :=
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) (|t|+6))) hu
      rw [h0]
      simp only [Int.cast_zero, zero_mul]
      exact_mod_cast hd1nn u
  have hmain := finsum_le_finsum' hFfin hGfin hle
  have hcast : ((∑ᶠ u : ℂ,
        MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ)
      = ∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) := by
    have h := map_finsum (Int.castAddHom ℝ) hd1fin
    simpa using h
  calc (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0))
      ≤ ∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) := hmain
    _ = ((∑ᶠ u : ℂ,
          MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0:ℂ) 11) u : ℤ) : ℝ) := hcast.symm

end Work.LinnikAreas.Zeta1Aux
