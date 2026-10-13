import Mathlib
import Submission.Work.WilC4aA.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter Set
namespace Work.WilC4aA

/-- **Weyl/vanden Dries elementary fact.**  Equivalently: an analytic function which is not
identically zero near `0` has `f s / s ^ k → b ≠ 0` for some integer `k`. -/
theorem analytic_hasAsymAt0 {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    Work.WilC4aA.HasAsymAt0 f := by
  by_cases htop : analyticOrderAt f (0 : ℝ) = ⊤
  · -- `f` vanishes identically on a neighbourhood of `0`
    left
    rw [analyticOrderAt_eq_top] at htop
    exact htop.filter_mono nhdsWithin_le_nhds
  · -- `f = s ^ N * g`, `g` analytic with `g 0 ≠ 0`
    right
    obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
    refine ⟨(analyticOrderNatAt f 0 : ℤ), g 0, hg0, ?_⟩
    have hgT : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun s : ℝ => f s / s ^ ((analyticOrderNatAt f 0 : ℤ) : ℝ))
        =ᶠ[𝓝[>] (0 : ℝ)] g := by
      filter_upwards [hfg.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hfs hs
      have hsne : s ≠ 0 := ne_of_gt hs
      rw [hfs, smul_eq_mul, sub_zero, Int.cast_natCast, Real.rpow_natCast]
      exact mul_div_cancel_left₀ (g s) (pow_ne_zero _ hsne)
    exact (tendsto_congr' heq).mpr hgT

end Work.WilC4aA
