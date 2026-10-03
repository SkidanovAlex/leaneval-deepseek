import Mathlib
import Submission.Work.FIArea5.HeckeZFR.analyticOrderAt_ne_top_of_differentiable_ne_zero
import Submission.Work.FIArea5.HeckeZFR.Hadm.divisorZeroOrder
import Submission.Work.FIArea5.HeckeZFR.Hadm.divisorFactorAway
import Submission.Work.FIArea5.HeckeZFR.Hadm.growthFactor

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Topology

namespace Work.FIArea5.HeckeZFR.Hadm

/-- **Weierstrass factorization at the origin.**  For an entire `Λ` that is not identically zero
and whose circle growth is `log ‖Λ z‖ ≤ C·R·(log (R+2) + K)` on `‖z‖ = R ≥ 1`, there are `k : ℕ`
and an entire `φ` with `φ 0 ≠ 0` and `Λ = z^k · φ`, `φ` inheriting the same shape of growth, and
the divisor of `Λ` on `closedBall 0 R` equal to `k` at the origin and to that of `φ` elsewhere. -/
theorem factorZero (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (hne : ∃ z : ℂ, Λ z ≠ 0)
    (hgrowth : ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K)) :
    ∃ (k : ℕ) (φ : ℂ → ℂ), Differentiable ℂ φ ∧ φ 0 ≠ 0 ∧
      (∀ z : ℂ, Λ z = z ^ k * φ z) ∧
      (∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
        Real.log ‖φ z‖ ≤ C * R * (Real.log (R + 2) + K)) ∧
      (∀ R : ℝ, 1 ≤ R → (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) 0 = (k : ℤ)) ∧
      (∀ (R : ℝ) (u : ℂ), u ≠ 0 →
        (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u =
          (MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u) := by
  classical
  have hΛ_an : AnalyticAt ℂ Λ 0 := hDiff.analyticAt 0
  have hord_ne : analyticOrderAt Λ 0 ≠ ⊤ :=
    Work.FIArea5.HeckeZFR.analyticOrderAt_ne_top_of_differentiable_ne_zero Λ hDiff hne 0
  obtain ⟨g, hg_an, hg_ne, hΛg⟩ := (hΛ_an.analyticOrderAt_ne_top).mp hord_ne
  set k : ℕ := analyticOrderNatAt Λ 0 with hk
  let φ : ℂ → ℂ := fun z => if z = 0 then g 0 else Λ z / z ^ k
  have hφ0 : φ 0 = g 0 := by simp [φ]
  have hφ_ne : φ 0 ≠ 0 := by rw [hφ0]; exact hg_ne
  have hφ_eq : ∀ z : ℂ, z ≠ 0 → φ z = Λ z / z ^ k := by
    intro z hz; simp [φ, hz]
  have hφ_an : ∀ u : ℂ, AnalyticAt ℂ φ u := by
    intro u
    by_cases hu : u = 0
    · rw [hu]
      have hEq : g =ᶠ[𝓝 (0 : ℂ)] φ := by
        filter_upwards [hΛg] with z hz
        by_cases hz0 : z = 0
        · subst hz0; rw [hφ0]
        · rw [hφ_eq z hz0, hz, sub_zero, smul_eq_mul,
            mul_div_cancel_left₀ (g z) (pow_ne_zero k hz0)]
      exact hg_an.congr hEq
    · have hEq : (fun z : ℂ => Λ z / z ^ k) =ᶠ[𝓝 u] φ := by
        filter_upwards [eventually_ne_nhds hu] with z hz
        rw [hφ_eq z hz]
      have hdiv : AnalyticAt ℂ (fun z : ℂ => Λ z / z ^ k) u :=
        (hDiff.analyticAt u).div (by fun_prop) (by simpa using pow_ne_zero k hu)
      exact hdiv.congr hEq
  have hφ_diff : Differentiable ℂ φ := fun u => (hφ_an u).differentiableAt
  have hfac : ∀ z : ℂ, Λ z = z ^ k * φ z := by
    intro z
    by_cases hz0 : z = 0
    · subst hz0
      rw [hφ0]
      have hz := hΛg.eq_of_nhds
      rw [sub_zero, smul_eq_mul] at hz
      exact hz
    · rw [hφ_eq z hz0]
      exact (mul_div_cancel₀ (Λ z) (pow_ne_zero k hz0)).symm
  have hφ_growth := growthFactor hfac hgrowth
  have hdiv0 : ∀ R : ℝ, 1 ≤ R →
      (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) 0 = (k : ℤ) := by
    intro R hR
    have hΛm : MeromorphicOn Λ (Metric.closedBall 0 R) :=
      fun z _ => (hDiff.analyticAt z).meromorphicAt
    have h0mem : (0 : ℂ) ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_self]; exact le_trans zero_le_one hR
    rw [divisorZeroOrder hΛm h0mem hΛ_an, hk]
  have hdiv_away : ∀ (R : ℝ) (u : ℂ), u ≠ 0 →
      (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u =
        (MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u := by
    intro R u hu
    have hΛm : MeromorphicOn Λ (Metric.closedBall 0 R) :=
      fun z _ => (hDiff.analyticAt z).meromorphicAt
    have hφm : MeromorphicOn φ (Metric.closedBall 0 R) :=
      fun z _ => (hφ_an z).meromorphicAt
    exact divisorFactorAway hΛm hφm hfac hu
  exact ⟨k, φ, hφ_diff, hφ_ne, hfac, hφ_growth, hdiv0, hdiv_away⟩

end Work.FIArea5.HeckeZFR.Hadm
