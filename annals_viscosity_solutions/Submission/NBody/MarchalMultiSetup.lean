import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalMultiOstrogradsky
import Submission.NBody.MarchalMultiJolt

/-!
# Setting up the sum-level Sundman analysis at a collision

The geometry of the Marchal chapter (F1), seventh layer: the elementary consequences of the collision
partition `ks = collClasses γ t₀` that the sum-level machinery consumes.

* `multiInertia_pos_of_withoutCollisions` — the total inertia of the family is positive at every
  collision-free configuration (the `hfpos` hypothesis);
* `tendsto_multiInertia_zero` — it tends to `0` at the collision time (a finite sum of the
  cluster estimates);
* `tendsto_const_div_sqrt_atTop` and `tendsto_multiPotential_atTop` — the potential diverges
  (the `hU` hypothesis), from Sperner's bound and `multiInertia → 0`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The total inertia of the family is positive** at a collision-free configuration, provided
every cluster has at least two bodies. -/
theorem multiInertia_pos_of_withoutCollisions {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {ks : Finset (Finset (Fin N))} (hne : ks.Nonempty) (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    {x : EN E N} (hnc : WithoutCollisions x) : 0 < multiInertia m ks x := by
  classical
  rw [multiInertia]
  exact Finset.sum_pos (fun k hk => clusterInertia_pos hm (hne2 k hk) hnc) hne

/-- **The total inertia tends to zero** at the collision time, if each cluster's inertia does. -/
theorem tendsto_multiInertia_zero {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {l : Filter ℝ}
    (h : ∀ k ∈ ks, Tendsto (fun t : ℝ => clusterInertia m k (x t)) l (𝓝 0)) :
    Tendsto (fun t : ℝ => multiInertia m ks (x t)) l (𝓝 0) := by
  classical
  have hfun : (fun t : ℝ => multiInertia m ks (x t))
      = fun t : ℝ => ∑ k ∈ ks, clusterInertia m k (x t) := by
    funext t; rw [multiInertia]
  rw [hfun]
  simpa using tendsto_finset_sum ks fun k hk => h k hk

/-- If `f → 0` through positive values and `c > 0`, then `c / √f → +∞`. -/
theorem tendsto_const_div_sqrt_atTop {f : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f l (𝓝 0)) (hpos : ∀ᶠ t in l, 0 < f t) :
    Tendsto (fun t : ℝ => c / Real.sqrt (f t)) l atTop := by
  rw [Filter.tendsto_atTop]
  intro a
  rcases le_or_gt a 0 with ha | ha
  · filter_upwards [hpos] with t ht
    exact le_trans ha (div_nonneg hc.le (Real.sqrt_nonneg _))
  · have hδ : 0 < c / a := div_pos hc ha
    have hthr : (0:ℝ) < (c / a) ^ 2 := by positivity
    filter_upwards [hf.eventually (isOpen_Iio.mem_nhds hthr), hpos] with t ht htp
    have h1 : Real.sqrt (f t) < c / a := by
      rw [← Real.sqrt_sq hδ.le]
      exact Real.sqrt_lt_sqrt (le_of_lt htp) ht
    have hpt : 0 < Real.sqrt (f t) := Real.sqrt_pos.mpr htp
    have h2 : a < c / Real.sqrt (f t) := by
      rw [lt_div_iff₀ hpt]
      have h3 := (lt_div_iff₀ ha).mp h1
      linarith [h3]
    exact le_of_lt h2

/-- **Sperner's bound makes the potential diverge** at a collision. -/
theorem tendsto_multiPotential_atTop {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {ks : Finset (Finset (Fin N))} (hne : ks.Nonempty) (hne2 : ∀ k ∈ ks, 2 ≤ k.card)
    {x : ℝ → EN E N} {l : Filter ℝ} (hnc : ∀ᶠ t in l, WithoutCollisions (x t))
    (hI : Tendsto (fun t : ℝ => multiInertia m ks (x t)) l (𝓝 0)) :
    Tendsto (fun t : ℝ => multiPotential m ks (x t)) l atTop := by
  obtain ⟨c, hcpos, hc⟩ := exists_const_le_multiPotential (E := E) hm ks hne2
  have hpos : ∀ᶠ t in l, 0 < multiInertia m ks (x t) := by
    filter_upwards [hnc] with t ht
    exact multiInertia_pos_of_withoutCollisions hm hne hne2 ht
  have hdiv : Tendsto (fun t : ℝ => c / Real.sqrt (multiInertia m ks (x t))) l atTop :=
    tendsto_const_div_sqrt_atTop hcpos hI hpos
  refine tendsto_atTop_mono' l ?_ hdiv
  filter_upwards [hnc] with t ht
  exact hc (x t) ht

end Submission.NBody
