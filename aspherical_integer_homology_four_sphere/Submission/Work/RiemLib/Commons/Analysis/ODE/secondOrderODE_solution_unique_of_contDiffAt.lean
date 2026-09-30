import Mathlib.Analysis.ODE.ExistUnique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Filter Set
open scoped Topology

/-- **Local uniqueness for the second-order ODE `u'' = F(u,u')`, with a pointwise smoothness
hypothesis.**

Two solutions of the first-order system `u' = v`, `v' = F (u, v)` that agree in value and
derivative at `0` agree on a neighbourhood of `0`, provided `F` is only required to be `C¹` *at
the common initial value* `(u₁ 0, v₁ 0)` — all the standard proof needs is a local Lipschitz
constant there, via `ContDiffAt.exists_lipschitzOnWith`.

This is `Commons.Analysis.ODE.secondOrderODE_solution_unique` with the global hypothesis
`ContDiff ℝ 1 F` weakened to `ContDiffAt ℝ 1 F (u₁ 0, v₁ 0)`; the proof is identical (replace
`hF.contDiffAt (x := (u₁ 0, v₁ 0))` by the given hypothesis). -/
theorem secondOrderODE_solution_unique_of_contDiffAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : E × E → E} {u₁ v₁ u₂ v₂ : ℝ → E} {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hF : ContDiffAt ℝ 1 F (u₁ 0, v₁ 0))
    (h₁ : ∀ t ∈ Set.Ioo (-ε₁) ε₁, HasDerivAt u₁ (v₁ t) t ∧ HasDerivAt v₁ (F (u₁ t, v₁ t)) t)
    (h₂ : ∀ t ∈ Set.Ioo (-ε₂) ε₂, HasDerivAt u₂ (v₂ t) t ∧ HasDerivAt v₂ (F (u₂ t, v₂ t)) t)
    (h0 : u₁ 0 = u₂ 0 ∧ v₁ 0 = v₂ 0) :
    ∃ δ > (0 : ℝ), δ ≤ ε₁ ∧ δ ≤ ε₂ ∧ ∀ t ∈ Set.Ioo (-δ) δ, u₁ t = u₂ t := by
  -- The first-order system on the product `E × E` is `C¹` at the common initial value.
  have hFA : ContDiffAt ℝ 1 (fun z : E × E => (z.2, F z)) (u₁ 0, v₁ 0) :=
    (contDiffAt_snd (𝕜 := ℝ) (n := 1) (p := (u₁ 0, v₁ 0))).prodMk hF
  -- A local Lipschitz constant for the field around the common initial value.
  obtain ⟨K, s, hs, hlip⟩ := hFA.exists_lipschitzOnWith
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
        ((fun z : E × E => (z.2, F z)) ((u₁ t, v₁ t))) t := by
    filter_upwards [Ioo_mem_nhds (show (-ε₁ : ℝ) < 0 by linarith) hε₁] with t ht
    exact (h₁ t ht).1.prodMk (h₁ t ht).2
  have hder2 : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun t : ℝ => (u₂ t, v₂ t))
        ((fun z : E × E => (z.2, F z)) ((u₂ t, v₂ t))) t := by
    filter_upwards [Ioo_mem_nhds (show (-ε₂ : ℝ) < 0 by linarith) hε₂] with t ht
    exact (h₂ t ht).1.prodMk (h₂ t ht).2
  have key : (fun t : ℝ => (u₁ t, v₁ t)) =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => (u₂ t, v₂ t)) :=
    ODE_solution_unique_of_eventually
      (v := fun (_ : ℝ) (z : E × E) => (z.2, F z)) (s := fun _ => s) (K := K)
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