import Mathlib.Analysis.ODE.ExistUnique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Filter Set

/-- **Local existence for the second-order ODE `u'' = G(u, u')`.**  If `G` is `C¹` near
`(p₀, v₀)`, then there is a local solution with `u 0 = p₀`, `u' 0 = v₀`, written as a first-order
system for `(u, u')`.

Suggested proof: apply
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` to the vector field
`F : E × E → E × E`, `F z = (z.2, G z)` on the product space, at the point `(p₀, v₀)` and time
`t₀ = 0`; take `u` and `v` to be the two components of the resulting integral curve (using
`HasDerivAt.fst`/`HasDerivAt.snd`). -/
theorem exists_secondOrderODE_local_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : E × E → E} {p₀ v₀ : E} (hG : ContDiffAt ℝ 1 G (p₀, v₀)) :
    ∃ ε > (0 : ℝ), ∃ u v : ℝ → E,
      u 0 = p₀ ∧ v 0 = v₀ ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt u (v t) t) ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt v (G (u t, v t)) t) := by
  set F : E × E → E × E := fun z => (z.2, G z) with hFdef
  have hF : ContDiffAt ℝ 1 F (p₀, v₀) := by
    rw [hFdef]
    exact (contDiffAt_snd (𝕜 := ℝ) (n := 1) (p := (p₀, v₀))).prodMk hG
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε, hε, (fun t => (α t).1), (fun t => (α t).2), ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hα0
  · simpa using congrArg Prod.snd hα0
  · intro t ht
    have ht' : t ∈ Ioo ((0 : ℝ) - ε) (0 + ε) := by simpa using ht
    have h := HasFDerivAt.comp_hasDerivAt (f := α) t
      (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := α t)) (hα t ht')
    simpa [hFdef, Function.comp_def] using h
  · intro t ht
    have ht' : t ∈ Ioo ((0 : ℝ) - ε) (0 + ε) := by simpa using ht
    have h := HasFDerivAt.comp_hasDerivAt (f := α) t
      (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := α t)) (hα t ht')
    simpa [hFdef, Function.comp_def] using h

end Commons.Analysis.ODE