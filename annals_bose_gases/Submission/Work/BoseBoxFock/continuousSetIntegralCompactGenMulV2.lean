import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter Metric
open scoped Topology

namespace Work.BoseBoxFock

/-- Continuity in the parameter of `p ↦ ∫_{z ∈ k} a z * g p z`, for `k` compact, `a` a.e. strongly
measurable and a.e. bounded on `k`, and `g` jointly continuous.  The proof is the standard
dominated-convergence argument: on a neighbourhood of the base point `p` the integrand is dominated
by the constant `max Ca 0 * M`, where the uniformity of the bound on `g` over `k` comes from
compactness of `k` (finitely many product neighbourhoods extracted from continuity of
`(q,z) ↦ g q z` at `(p,z)`), and `max Ca 0 * M` is integrable because `volume.restrict k` is
finite. -/
theorem continuousSetIntegralCompactGenMulV2
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureTheory.MeasureSpace G]
    [BorelSpace G]
    [MeasureTheory.IsFiniteMeasureOnCompacts (MeasureTheory.volume : MeasureTheory.Measure G)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : Set G} (hk : IsCompact k) {a : G → ℂ} {Ca : ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a
      ((MeasureTheory.volume : MeasureTheory.Measure G).restrict k))
    (hab : Filter.Eventually (fun z => ‖a z‖ ≤ Ca)
      (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure G).restrict k)))
    {g : P → G → ℂ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ∫ z in k, a z * g p z) := by
  rw [continuous_iff_continuousAt]
  intro p
  -- `z ↦ g q z` is continuous for every `q`
  have hgc : ∀ q : P, Continuous (fun z : G => g q z) := fun q =>
    hg.comp (Continuous.prodMk_right q)
  -- local uniformity of `g` on `k`: for every `z` there is a radius `δ z` such that on the
  -- product neighbourhood `ball p (δ z) × ball z (δ z)` one has `‖g q z'‖ ≤ ‖g p z‖ + 1`
  have hloc : ∀ z : G, ∃ δ : ℝ, 0 < δ ∧ (z ∈ k → ∀ q : P, dist q p < δ →
      ∀ z' : G, dist z' z < δ → ‖g q z'‖ ≤ ‖g p z‖ + 1) := by
    intro z
    by_cases hz : z ∈ k
    · have hcont : ContinuousAt (Function.uncurry g) (p, z) := hg.continuousAt
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δ, hδpos, hδ⟩ := hcont 1 zero_lt_one
      refine ⟨δ, hδpos, fun _ q hq z' hz' => ?_⟩
      have h1 : dist (q, z') (p, z) < δ := by
        rw [Prod.dist_eq]; exact max_lt hq hz'
      have h2 : ‖g q z' - g p z‖ < 1 := by
        have := hδ h1
        simpa [dist_eq_norm, Function.uncurry] using this
      have h3 : ‖g q z'‖ ≤ ‖g q z' - g p z‖ + ‖g p z‖ := by
        have h4 := norm_add_le (g q z' - g p z) (g p z)
        rwa [sub_add_cancel] at h4
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hz⟩
  choose δ hδpos hδb using hloc
  -- finitely many points of `k` whose `δ`-balls about them cover `k`
  obtain ⟨t, hcover⟩ := hk.elim_nhds_subcover' (fun z _ => ball z (δ z / 2))
    (fun z _ => ball_mem_nhds z (half_pos (hδpos z)))
  -- a uniform bound `M` for `g p ·` on those finitely many points
  set M : ℝ := (∑ y ∈ t, (‖g p (y : G)‖ + 1)) + 1 with hMdef
  have hMge : ∀ x ∈ t, ‖g p (x : G)‖ + 1 ≤ M := by
    intro x hx
    have h1 : ‖g p (x : G)‖ + 1 ≤ ∑ y ∈ t, (‖g p (y : G)‖ + 1) :=
      Finset.single_le_sum (f := fun y : {z : G // z ∈ k} => ‖g p (y : G)‖ + 1)
        (fun i _ => add_nonneg (norm_nonneg _) zero_le_one) hx
    rw [hMdef]; linarith
  -- hence eventually in `q` near `p`, `‖g q z‖ ≤ M` for all `z ∈ k`
  have hbound_g : ∀ᶠ q in 𝓝 p, ∀ z ∈ k, ‖g q z‖ ≤ M := by
    have hmem : (⋂ x ∈ (t : Set {z : G // z ∈ k}), ball p (δ (x : G))) ∈ 𝓝 p := by
      rw [Filter.biInter_mem (Finset.finite_toSet t)]
      intro x _
      exact ball_mem_nhds p (hδpos (x : G))
    filter_upwards [hmem] with q hq z hz
    obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hcover hz)
    have hqx : q ∈ ball p (δ (x : G)) := Set.mem_iInter₂.1 hq x hxt
    rw [mem_ball] at hqx hzx
    have hzx' : dist z (x : G) < δ (x : G) :=
      lt_of_lt_of_le hzx (by linarith [hδpos (x : G)])
    exact le_trans (hδb (x : G) x.2 q hqx z hzx') (hMge x hxt)
  -- the restricted measure is finite, so constant functions are integrable
  haveI : IsFiniteMeasure (volume.restrict k) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (hk.measure_lt_top.ne)
  -- the a.e. dominating function for the integrand
  have hbound : ∀ᶠ q in 𝓝 p, ∀ᵐ z ∂(volume.restrict k), ‖a z * g q z‖ ≤ max Ca 0 * M := by
    filter_upwards [hbound_g] with q hq
    filter_upwards [hab, MeasureTheory.self_mem_ae_restrict hk.measurableSet] with z hz hzk
    have hza : ‖a z‖ ≤ max Ca 0 := le_trans hz (le_max_left _ _)
    have hzg : ‖g q z‖ ≤ M := hq z hzk
    calc ‖a z * g q z‖ = ‖a z‖ * ‖g q z‖ := norm_mul _ _
      _ ≤ max Ca 0 * M := mul_le_mul hza hzg (norm_nonneg _) (le_max_right _ _)
  have hmeas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (fun z => a z * g q z) (volume.restrict k) :=
    Filter.Eventually.of_forall fun q => ha.mul (hgc q).aestronglyMeasurable
  have hlim : ∀ᵐ z ∂(volume.restrict k), ContinuousAt (fun q : P => a z * g q z) p := by
    refine Filter.Eventually.of_forall fun z => ?_
    have h1 : Continuous (fun q : P => g q z) := hg.comp (Continuous.prodMk_left z)
    exact tendsto_const_nhds.mul h1.continuousAt
  have hInt : Integrable (fun _ : G => max Ca 0 * M) (volume.restrict k) :=
    MeasureTheory.integrable_const _
  exact MeasureTheory.continuousAt_of_dominated (μ := volume.restrict k)
    (F := fun q z => a z * g q z) (x₀ := p) (bound := fun _ => max Ca 0 * M)
    hmeas hbound hInt hlim

end Work.BoseBoxFock
