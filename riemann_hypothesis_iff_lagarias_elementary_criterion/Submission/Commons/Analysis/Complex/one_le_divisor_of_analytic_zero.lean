import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Divisor

open Complex Filter Metric MeromorphicOn
open scoped Topology

noncomputable section

namespace Commons.Analysis.Complex

theorem one_le_divisor_of_analytic_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) {x ρ : ℂ} (hx : x ∈ U) (hx0 : f x ≠ 0) (hρ : ρ ∈ U)
    (hzero : f ρ = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor f U ρ := by
  rw [hf.divisor_apply hρ]
  have hmer : MeromorphicOn f U := hf.meromorphicOn
  have hxfin : meromorphicOrderAt f x ≠ ⊤ := by
    rw [(hf x hx).meromorphicOrderAt_eq, ((hf x hx).analyticOrderAt_eq_zero).2 hx0]
    simp
  have hρfin : meromorphicOrderAt f ρ ≠ ⊤ :=
    hmer.meromorphicOrderAt_ne_top_of_isPreconnected hU hx hρ hxfin
  have hanfin : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    apply hρfin
    rw [(hf ρ hρ).meromorphicOrderAt_eq, h]
    simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hanfin
  rw [← hk, ENat.map_natCast, WithTop.untop₀_coe]
  have hk0 : k ≠ 0 := by
    intro hk0
    apply (analyticOrderAt_ne_zero.2 ⟨hf ρ hρ, hzero⟩)
    rw [← hk, hk0]
    rfl
  omega

end Commons.Analysis.Complex