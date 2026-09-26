import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

namespace Work.Smooth.SphereJordan

open Set Filter

/-- A simple closed curve on the Riemann sphere which avoids `∞` is, literally, a simple closed
plane curve: it is the image of a continuous `2π`-periodic map `γ : ℝ → ℂ` which is injective on
the period `[0, 2π)`.

The point is that the finite part `ℂ ⊆ ℂ ∪ {∞}` is an *open* subspace of the one-point
compactification (`OnePoint.comap_coe_nhds` says exactly that the coercion induces the topology of
`ℂ`), so a continuous curve whose image lies in it is continuous as a plane curve. -/
theorem exists_planeCurve_of_avoids_infty {c : ℝ → RiemannSphere} (hc : IsSimpleClosedCurve c)
    (hinf : ∀ t : ℝ, c t ≠ infty) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ ∀ t : ℝ, c t = (γ t : RiemannSphere) := by
  -- `γ` is the unique finite lift of `c`, which exists because `c` avoids `∞`.
  choose γ hγ using fun t => OnePoint.ne_infty_iff_exists.mp (hinf t)
  refine ⟨γ, ?_, ?_, ?_, fun t => (hγ t).symm⟩
  · -- continuity: `c = (↑) ∘ γ` is continuous and `(↑) : ℂ → ℂ ∪ {∞}` induces the topology on `ℂ`
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    show Filter.Tendsto γ (nhds t) (nhds (γ t))
    rw [← OnePoint.comap_coe_nhds (γ t)]
    rw [Filter.tendsto_comap_iff]
    have hcoe : (OnePoint.some ∘ γ) = c := funext hγ
    rw [hcoe, hγ t]
    exact hc.continuous.continuousAt
  · -- periodicity, by injectivity of the coercion
    intro t
    exact OnePoint.coe_injective (by rw [hγ (t + 2 * Real.pi), hγ t, hc.periodic t])
  · -- injectivity on one period, by injectivity of the coercion and of `c`
    intro t ht s hs hts
    refine hc.injOn ht hs ?_
    rw [← hγ t, ← hγ s, hts]

end Work.Smooth.SphereJordan
