import Mathlib
import Submission.Work.A14D.setup

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-- If two holomorphic functions `u`, `v` on a disc around `1` have vanishing Wronskian
everywhere except possibly at the centre `1`, and `v` never vanishes on the disc, then
`u` is a constant multiple of `v` on the disc.

The proof considers `w = u / v`, which is holomorphic on the disc; its derivative is
`-wron u v / v²`, hence vanishes off `1`.  Since `deriv w` is again holomorphic, it is
continuous, so the vanishing extends to `1`; `w` is therefore constant on the (convex)
disc, and `u = w · v` because `v ≠ 0`. -/
theorem exists_smul_of_wron_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {u v : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u (Metric.ball (1:ℂ) ρ))
    (hv : DifferentiableOn ℂ v (Metric.ball (1:ℂ) ρ))
    (hvne : ∀ z ∈ Metric.ball (1:ℂ) ρ, v z ≠ 0)
    (hW : ∀ z ∈ Metric.ball (1:ℂ) ρ, z ≠ 1 → wron u v z = 0) :
    ∃ c : ℂ, ∀ z ∈ Metric.ball (1:ℂ) ρ, u z = c * v z := by
  have hballmem : Metric.ball (1:ℂ) ρ ∈ 𝓝 (1:ℂ) := Metric.ball_mem_nhds 1 hρ
  have hconn : IsPreconnected (Metric.ball (1:ℂ) ρ) := (convex_ball 1 ρ).isPreconnected
  have hw : DifferentiableOn ℂ (u / v) (Metric.ball (1:ℂ) ρ) := hu.div hv hvne
  -- off the centre, `deriv (u/v) = -(wron u v)/v²` vanishes
  have hderiv : ∀ z ∈ Metric.ball (1:ℂ) ρ, z ≠ 1 → deriv (u / v) z = 0 := by
    intro z hz hz1
    have hdu : DifferentiableAt ℂ u z := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have hdv : DifferentiableAt ℂ v z := hv.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    rw [deriv_div hdu hdv (hvne z hz)]
    have hz0 : u z * deriv v z - deriv u z * v z = 0 := by
      have h := hW z hz hz1
      unfold wron at h
      exact h
    have hnum : deriv u z * v z - u z * deriv v z = 0 := by linear_combination -hz0
    rw [hnum, zero_div]
  -- the derivative vanishes on the whole disc, including at the centre, by continuity
  have hderiv_all : Set.EqOn (deriv (u / v)) 0 (Metric.ball (1:ℂ) ρ) := by
    intro z hz
    by_cases h1 : z = 1
    · subst h1
      have hcont : ContinuousOn (deriv (u / v)) (Metric.ball (1:ℂ) ρ) :=
        (hw.deriv Metric.isOpen_ball).continuousOn
      have hca : ContinuousAt (deriv (u / v)) 1 := hcont.continuousAt hballmem
      have ht1 : Tendsto (deriv (u / v)) (𝓝[≠] (1:ℂ)) (𝓝 (deriv (u / v) 1)) :=
        hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1:ℂ)}ᶜ))
      have hev : (fun _ : ℂ => (0:ℂ)) =ᶠ[𝓝[≠] (1:ℂ)] (deriv (u / v)) := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hballmem] with z hz1 hzball
        exact (hderiv z hzball (Set.mem_compl_singleton_iff.mp hz1)).symm
      have ht0 : Tendsto (deriv (u / v)) (𝓝[≠] (1:ℂ)) (𝓝 0) :=
        Filter.Tendsto.congr' hev tendsto_const_nhds
      exact tendsto_nhds_unique ht1 ht0
    · exact hderiv z hz h1
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero hconn hw hderiv_all
  refine ⟨c, fun z hz => ?_⟩
  have hz' : u z / v z = c := hc z hz
  rw [div_eq_iff (hvne z hz)] at hz'
  exact hz'

end Work.A14D
