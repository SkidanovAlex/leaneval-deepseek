/-
# `Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_z` — shrinking `z`-layers

If `t : ℕ → Set ℝ` is an antitone sequence of measurable subsets of `Iz = [0,∞)` whose
intersection meets `Iz` in the empty set (each `z ∈ Iz` is eventually outside `t N`), then the
`ℋ⁴`-mass of `f` carried by the layer `t N`,

  `zShrinkInt α f (t N) = ∫_{Iz} 1_{t N}(z) · (∫_{Iθ} HkIntegrand α 4 f z θ)`,

tends to `0`.  This is the `z`-analogue of the layer lemma
`Work.FTS.GalBasis.cc.tendsto_HkIntegrand_indicator_theta`.

The proof is the dominated convergence theorem on the measure `volume.restrict Iz`: with
`g z := ∫_{Iθ} HkIntegrand α 4 f z θ`, the hypothesis `hmem` says exactly that `g` is integrable
on `Iz`; the integrands `1_{t N} · g` are dominated by `‖g‖` and converge pointwise to `0`
because `t` is antitone and every point of `Iz` leaves the sequence eventually.  Neither
`SmoothOpen f` nor the slice integrability of `hmem` is needed.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.GalBasis.cc

theorem tendsto_HkIntegrand_indicator_z {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {t : ℕ → Set ℝ}
    (hmeas : ∀ N : ℕ, MeasurableSet (t N)) (hsub : ∀ N : ℕ, t N ⊆ Work.Spaces.Iz)
    (hanti : ∀ N : ℕ, t (N + 1) ⊆ t N)
    (hlim : ∀ z ∈ Work.Spaces.Iz, ∃ N : ℕ, z ∉ t N) :
    Filter.Tendsto (fun N : ℕ => zShrinkInt α f (t N)) Filter.atTop (nhds 0) := by
  -- the marginal `g z = ∫_{Iθ} HkIntegrand α 4 f z θ` is integrable on `Iz` by `hmem`
  set g : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ with hg
  have hgint : IntegrableOn g Work.Spaces.Iz := by simpa only [hg] using hmem.2
  -- `t` is antitone as a sequence of sets
  have hanti' : Antitone t := antitone_nat_of_succ_le hanti
  -- pointwise the integrands vanish eventually on `Iz`
  have hlim' : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Tendsto (fun N : ℕ => (t N).indicator (fun _ => (1 : ℝ)) z * g z) atTop (nhds 0) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    obtain ⟨N0, hN0⟩ := hlim z hz
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop N0] with N hN
    have hzt : z ∉ t N := fun h => hN0 (hanti' hN h)
    simp only [Set.indicator_of_notMem hzt, zero_mul]
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iz)
    (F := fun N z => (t N).indicator (fun _ => (1 : ℝ)) z * g z)
    (f := fun _ => 0) (fun z => ‖g z‖)
    (fun N => (((measurable_const.indicator (hmeas N)).aestronglyMeasurable).mul hgint.1))
    hgint.norm
    (fun N => by
      filter_upwards with z
      by_cases hz : z ∈ t N
      · rw [Set.indicator_of_mem hz]; simp
      · rw [Set.indicator_of_notMem hz]; simp)
    hlim'
  simpa only [Work.FTS.GalBasis.cc.zShrinkInt, hg, MeasureTheory.integral_zero] using hmain

end Work.FTS.GalBasis.cc
