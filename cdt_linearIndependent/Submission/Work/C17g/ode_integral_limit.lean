import Mathlib

namespace Work.C17g

open MeasureTheory Set Filter

/-- Dominated-convergence for the Picard integral of a linear ODE along a segment: if the
pointwise limit `Yu` of the uniformly bounded continuous family `Y n` exists on `T`, then the
segment integrals of the inhomogeneous linear expression converge to the corresponding integral
of the limit. -/
theorem ode_integral_limit {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (z₀ : ℂ) {T : Set ℂ} (hseg : ∀ z ∈ T, ∀ t ∈ Set.Icc (0:ℝ) 1, z₀ + t • (z - z₀) ∈ T)
    (hAc : ∀ i j, ContinuousOn (fun z => A z i j) T) (hbc : ∀ i, ContinuousOn (fun z => b z i) T)
    {Y : ℕ → ℂ → (Fin k → ℂ)} {Yu : ℂ → (Fin k → ℂ)}
    (hYc : ∀ n, ContinuousOn (fun z => Y n z) T)
    (hYu : ∀ z ∈ T, Filter.Tendsto (fun n => Y n z) Filter.atTop (nhds (Yu z)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ n, ∀ z ∈ T, ‖Y n z‖ ≤ B)
    {M B' : ℝ} (hM : 0 ≤ M)
    (hAb : ∀ z ∈ T, ∀ x : Fin k → ℂ, ‖(fun i => ∑ j, A z i j * x j)‖ ≤ M * ‖x‖)
    (hb' : ∀ z ∈ T, ‖b z‖ ≤ B') :
    ∀ z ∈ T, Filter.Tendsto (fun n => ∫ t in (0:ℝ)..1, (fun i =>
        (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i))
      Filter.atTop (nhds (∫ t in (0:ℝ)..1, (fun i =>
        (∑ j, A (z₀ + t • (z - z₀)) i j * Yu (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i))) := by
  intro z hz
  have hw : Continuous (fun t : ℝ => z₀ + t • (z - z₀)) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ => z₀ + t • (z - z₀)) (Set.Icc (0:ℝ) 1) T :=
    fun t ht => hseg z hz t ht
  have hsub : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    have h1 : t ∈ Set.uIcc (0:ℝ) 1 := Set.uIoc_subset_uIcc ht
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h1
  -- Continuity of the integrand on the segment parameter set.
  have hcont : ∀ n, ContinuousOn (fun t : ℝ => fun i =>
      (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j) + b (z₀ + t • (z - z₀)) i)
      (Set.Icc (0:ℝ) 1) := by
    intro n
    have hYw : ContinuousOn (fun t : ℝ => Y n (z₀ + t • (z - z₀))) (Set.Icc (0:ℝ) 1) :=
      (hYc n).comp hw.continuousOn hmaps
    rw [continuousOn_pi]
    intro i
    refine ContinuousOn.add ?_ ((hbc i).comp hw.continuousOn hmaps)
    simpa using continuousOn_finsetSum (Finset.univ : Finset (Fin k))
      (fun j _ => ((hAc i j).comp hw.continuousOn hmaps).mul ((continuousOn_pi.mp hYw) j))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun n t => fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)
      + b (z₀ + t • (z - z₀)) i)
    (f := fun t => fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Yu (z₀ + t • (z - z₀)) j)
      + b (z₀ + t • (z - z₀)) i)
    (fun _ => M * B + B') ?_ ?_ ?_ ?_
  · -- almost-everywhere strong measurability, from continuity on `Icc 0 1`.
    exact Eventually.of_forall (fun n =>
      ContinuousOn.aestronglyMeasurable ((hcont n).mono hsub) measurableSet_uIoc)
  · -- uniform bound `M * B + B'` on the integrand.
    refine Eventually.of_forall (fun n => ?_)
    refine ae_of_all volume (fun t ht => ?_)
    have htI := hsub ht
    have hwT : z₀ + t • (z - z₀) ∈ T := hseg z hz t htI
    have h1 : ‖(fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)‖ ≤ M * B := by
      calc _ ≤ M * ‖Y n (z₀ + t • (z - z₀))‖ := hAb _ hwT _
        _ ≤ M * B := by gcongr; exact hB n _ hwT
    calc ‖(fun i => (∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)
            + b (z₀ + t • (z - z₀)) i)‖
        ≤ ‖(fun i => ∑ j, A (z₀ + t • (z - z₀)) i j * Y n (z₀ + t • (z - z₀)) j)‖
            + ‖b (z₀ + t • (z - z₀))‖ :=
          norm_add_le _ _
      _ ≤ M * B + B' := add_le_add h1 (hb' _ hwT)
  · exact intervalIntegrable_const
  · -- pointwise convergence of the integrand, from continuity of `x ↦ A w x + b w`.
    refine ae_of_all volume (fun t ht => ?_)
    have htI := hsub ht
    have hwT : z₀ + t • (z - z₀) ∈ T := hseg z hz t htI
    have hΦ : Continuous (fun x : Fin k → ℂ => fun i =>
        (∑ j, A (z₀ + t • (z - z₀)) i j * x j) + b (z₀ + t • (z - z₀)) i) := by
      rw [continuous_pi_iff]
      intro i
      refine Continuous.add ?_ continuous_const
      simpa using continuous_finsetSum (Finset.univ : Finset (Fin k))
        (fun j _ => continuous_const.mul (continuous_apply j))
    have := (hΦ.tendsto (Yu (z₀ + t • (z - z₀)))).comp (hYu (z₀ + t • (z - z₀)) hwT)
    simpa only [Function.comp_def] using this

end Work.C17g
