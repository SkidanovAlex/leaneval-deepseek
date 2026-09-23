import Mathlib

namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology

/-- **Local uniqueness for the second-order ODE `u'' = G(u, u')`.**  Two solutions of the
first-order system `u' = v`, `v' = G(u, v)` (with `G` globally `C¹`, which suffices since only a
local Lipschitz constant is needed) that agree in value and derivative at `0` agree on a
neighbourhood of `0`.

Suggested proof: use `ODE_solution_unique_of_mem_Icc` (or the `IsPicardLindelof` uniqueness) for
the product-space field `F z = (z.2, G z)`; a local Lipschitz constant follows from
`hG.contDiffOn` on a suitable ball around the common initial value together with the mean value
inequality (`Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le` or
`ContDiffOn.lipschitzOnWith`). -/
theorem secondOrderODE_solution_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : E × E → E} (hG : ContDiff ℝ 1 G)
    {u₁ v₁ u₂ v₂ : ℝ → E} {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (h₁ : ∀ t ∈ Ioo (-ε₁) ε₁, HasDerivAt u₁ (v₁ t) t ∧ HasDerivAt v₁ (G (u₁ t, v₁ t)) t)
    (h₂ : ∀ t ∈ Ioo (-ε₂) ε₂, HasDerivAt u₂ (v₂ t) t ∧ HasDerivAt v₂ (G (u₂ t, v₂ t)) t)
    (h0 : u₁ 0 = u₂ 0 ∧ v₁ 0 = v₂ 0) :
    ∃ δ > (0 : ℝ), δ ≤ ε₁ ∧ δ ≤ ε₂ ∧ ∀ t ∈ Ioo (-δ) δ, u₁ t = u₂ t := by
  -- Rewrite the second-order equation as a first-order system on the product `E × E`.
  have hF : ContDiff ℝ 1 (fun z : E × E => (z.2, G z)) := by fun_prop
  -- A local Lipschitz constant for the field around the common initial value.
  obtain ⟨K, s, hs, hlip⟩ := (hF.contDiffAt (x := (u₁ 0, v₁ 0))).exists_lipschitzOnWith
  have hs₂ : s ∈ 𝓝 (u₂ 0, v₂ 0) := by rw [← h0.1, ← h0.2]; exact hs
  have h0' : (fun t : ℝ => (u₁ t, v₁ t)) 0 = (fun t : ℝ => (u₂ t, v₂ t)) 0 := by
    simp only [h0.1, h0.2]
  have hmem1 : ∀ᶠ t in 𝓝 (0 : ℝ), (u₁ t, v₁ t) ∈ s := by
    have hm : (0 : ℝ) ∈ Ioo (-ε₁) ε₁ := ⟨by linarith, hε₁⟩
    exact ((h₁ 0 hm).1.continuousAt.prodMk (h₁ 0 hm).2.continuousAt).eventually hs
  have hmem2 : ∀ᶠ t in 𝓝 (0 : ℝ), (u₂ t, v₂ t) ∈ s := by
    have hm : (0 : ℝ) ∈ Ioo (-ε₂) ε₂ := ⟨by linarith, hε₂⟩
    exact ((h₂ 0 hm).1.continuousAt.prodMk (h₂ 0 hm).2.continuousAt).eventually hs₂
  have hder1 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun t : ℝ => (u₁ t, v₁ t))
        ((fun z : E × E => (z.2, G z)) ((u₁ t, v₁ t))) t := by
    filter_upwards [Ioo_mem_nhds (show (-ε₁ : ℝ) < 0 by linarith) hε₁] with t ht
    exact (h₁ t ht).1.prodMk (h₁ t ht).2
  have hder2 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun t : ℝ => (u₂ t, v₂ t))
        ((fun z : E × E => (z.2, G z)) ((u₂ t, v₂ t))) t := by
    filter_upwards [Ioo_mem_nhds (show (-ε₂ : ℝ) < 0 by linarith) hε₂] with t ht
    exact (h₂ t ht).1.prodMk (h₂ t ht).2
  have key : (fun t : ℝ => (u₁ t, v₁ t)) =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => (u₂ t, v₂ t)) :=
    ODE_solution_unique_of_eventually
      (v := fun (_ : ℝ) (z : E × E) => (z.2, G z)) (s := fun _ => s) (K := K)
      (f := fun t : ℝ => (u₁ t, v₁ t)) (g := fun t : ℝ => (u₂ t, v₂ t)) (t₀ := 0)
      (Eventually.of_forall (fun _ => hlip)) (hder1.and hmem1) (hder2.and hmem2) h0'
  have key1 : u₁ =ᶠ[𝓝 (0 : ℝ)] u₂ := key.mono (fun t ht => congrArg Prod.fst ht)
  obtain ⟨s', hs', H⟩ := Filter.eventually_iff_exists_mem.mp key1
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp hs'
  refine ⟨min η (min ε₁ ε₂), lt_min hη (lt_min hε₁ hε₂), ?_, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)
  · intro t ht
    apply H
    apply hηs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1, min_le_left η (min ε₁ ε₂)],
           by linarith [ht.2, min_le_left η (min ε₁ ε₂)]⟩

end Commons.Analysis.ODE
