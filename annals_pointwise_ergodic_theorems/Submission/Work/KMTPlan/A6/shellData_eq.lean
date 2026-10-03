import Mathlib
import Submission.Work.KMTPlan.A6.BesselDefs

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-- Two data `(α, θ)` and `(α', θ')` with `α, α'` arithmetic frequencies inside a non-aliasing
set `A` at scale `K` and `θ, θ'` in the dyadic frequency shells of scales `k ≤ K`, `k' ≤ K`
are equal as soon as they have the same sum `α + θ = α' + θ'` in `ℝ/ℤ`.

Indeed `|θ| < 2^k ≤ 2^K` (and likewise for `θ'`) forces `θ, θ' ∈ ℝ_{≤K} = [-2^K, 2^K]`, so that
non-aliasing of `A` at scale `K` applies. -/
theorem shellData_eq {A : Finset Work.Analysis.IonescuWainger.Circle} {K : ℤ}
    (hNA : Work.Analysis.IonescuWainger.NonAliasing K A)
    {k k' : ℤ} (hk : k ≤ K) (hk' : k' ≤ K)
    {α α' : Work.Analysis.IonescuWainger.Circle} (hα : α ∈ A) (hα' : α' ∈ A) {θ θ' ξ : ℝ}
    (hθlo : (2:ℝ)^(k-2) < |θ|) (hθhi : |θ| < (2:ℝ)^k)
    (hθ'lo : (2:ℝ)^(k'-2) < |θ'|) (hθ'hi : |θ'| < (2:ℝ)^k')
    (hξ : α + (θ : Work.Analysis.IonescuWainger.Circle) = (ξ : Work.Analysis.IonescuWainger.Circle))
    (hξ' : α' + (θ' : Work.Analysis.IonescuWainger.Circle) = (ξ : Work.Analysis.IonescuWainger.Circle)) :
    α = α' ∧ θ = θ' := by
  have hpk : (2:ℝ)^k ≤ (2:ℝ)^K := zpow_le_zpow_right₀ (by norm_num) hk
  have hpk' : (2:ℝ)^k' ≤ (2:ℝ)^K := zpow_le_zpow_right₀ (by norm_num) hk'
  have hθmem : θ ∈ realArc K := by
    rw [realArc, Set.mem_Icc]
    obtain ⟨hl, hh⟩ := abs_lt.mp hθhi
    exact ⟨by linarith, by linarith⟩
  have hθ'mem : θ' ∈ realArc K := by
    rw [realArc, Set.mem_Icc]
    obtain ⟨hl, hh⟩ := abs_lt.mp hθ'hi
    exact ⟨by linarith, by linarith⟩
  exact hNA α hα α' hα' θ hθmem θ' hθ'mem (hξ.trans hξ'.symm)

end Work.KMTPlan.A6
