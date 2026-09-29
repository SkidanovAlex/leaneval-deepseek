import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.pullbackData_comp_mul_of_mero
import Submission.Work.Holonomy3.exists_taylor_series

/-!
# The scaled problem of STEP 0

For `r ∈ (0,1)` the maps `ψ_k := φ_k(r ·)` are holomorphic on the ball of radius `1/r > 1`
(whereas the `φ_k` are only holomorphic on the open unit disc).  This module produces, from the
data of the theorem, the whole analytic package of the scaled problem: the maps `ψ_k`, their
Taylor series `Φ_k` at `0`, and the pullback data `(N_{i,k}, P_{i,k})` of the species.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

noncomputable section

/-- The analytic package of the scaled problem for `r ∈ (0,1)`. -/
theorem scaled_setup {m r' l : ℕ} (f : Fin m → PowerSeries ℚ) (φ : Fin (l + 1) → ℂ → ℂ)
    (hadm : ∀ k, AdmissibleMap (φ k)) (hpm : ∀ i k, Submission.CDTPlan.PullbackMero (f i) (φ k))
    {r : ℝ} (hr0 : 0 < r) :
    ∃ (ψ : Fin (l + 1) → ℂ → ℂ) (Φ : Fin (l + 1) → PowerSeries ℂ)
      (N : Fin m → Fin (l + 1) → ℂ → ℂ) (P : Fin m → Fin (l + 1) → Polynomial ℂ),
      ψ = (fun k z => φ k (r * z)) ∧
      (∀ k, AnalyticOnNhd ℂ (ψ k) (Metric.ball 0 (1 / r))) ∧
      (∀ k, ψ k 0 = 0) ∧
      (∀ k, deriv (ψ k) 0 = r * deriv (φ k) 0) ∧
      (∀ k, PowerSeries.coeff 0 (Φ k) = 0 ∧ PowerSeries.coeff 1 (Φ k) = deriv (ψ k) 0 ∧
        ∀ z : ℂ, ‖z‖ < 1 / r →
          HasSum (fun p : ℕ => PowerSeries.coeff p (Φ k) * z ^ p) (ψ k z)) ∧
      (∀ i k, PullbackData (f i) (ψ k) (1 / r) (N i k) (P i k)) := by
  have hpos : (0 : ℝ) < 1 / r := by positivity
  have hdiff : ∀ k, DifferentiableOn ℂ (φ k) (Metric.ball 0 1) := fun k => (hadm k).2.1
  -- the scaled maps are analytic on the ball of radius `1/r`
  have hnorm : ‖((r : ℝ) : ℂ)‖ = r :=
    (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_pos hr0)
  have hψa : ∀ k, AnalyticOnNhd ℂ (fun z : ℂ => φ k (r * z)) (Metric.ball 0 (1 / r)) := by
    intro k z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz
    have hz1 : r * z ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right]
      rw [norm_mul, hnorm, mul_comm]
      rwa [lt_div_iff₀ hr0] at hz
    have hφ : AnalyticAt ℂ (φ k) (r * z) :=
      (hdiff k).analyticOnNhd Metric.isOpen_ball (r * z) hz1
    have hinner : AnalyticAt ℂ (fun w : ℂ => ((r : ℝ) : ℂ) * w) z :=
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((r : ℝ) : ℂ)) z).mul
        (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z))
    exact hφ.comp hinner
  -- the Taylor series of the scaled maps
  have hΦex : ∀ k, ∃ Φk : PowerSeries ℂ, PowerSeries.coeff 0 Φk = (fun z : ℂ => φ k (r * z)) 0 ∧
      PowerSeries.coeff 1 Φk = deriv (fun z : ℂ => φ k (r * z)) 0 ∧
      ∀ z : ℂ, ‖z‖ < 1 / r →
        HasSum (fun p : ℕ => PowerSeries.coeff p Φk * z ^ p) ((fun z : ℂ => φ k (r * z)) z) :=
    fun k => exists_taylor_series hpos (hψa k)
  choose Φ hΦ0 hΦ1 hΦsum using hΦex
  -- the pullback data of the scaled maps
  have hNP : ∀ i k, ∃ N' : ℂ → ℂ, ∃ P' : Polynomial ℂ,
      PullbackData (f i) (fun z => φ k (r * z)) (1 / r) N' P' :=
    fun i k => pullbackData_comp_mul_of_mero (hpm i k) hr0
  choose N P hNPl using hNP
  refine ⟨fun k z => φ k (r * z), Φ, N, P, rfl, hψa, ?_, ?_, ?_, hNPl⟩
  · intro k
    simp only
    rw [mul_zero]
    exact (hadm k).2.2.1
  · intro k
    rw [deriv_comp_mul_left]
    simp
  · intro k
    refine ⟨?_, hΦ1 k, hΦsum k⟩
    rw [hΦ0 k]
    simp [(hadm k).2.2.1]

end

end Work.Holonomy3
