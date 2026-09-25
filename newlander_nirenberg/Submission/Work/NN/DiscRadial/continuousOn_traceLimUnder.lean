import Mathlib
import Submission.Work.NN.DiscRadial.holderDerivTendsto_of_isOpen

namespace Work.NN.DiscRadial

open scoped Topology
open Set Filter Metric

/-- **The trace of a Hölder function is continuous.**  Let `g : G × ℝ → ℂ` have finite `C^{k,β}` norm (`β > 0`) on the slab `W × (0,ε)` with `W` open.  Then for `y ∈ W` the limit `Ψ y = lim_{σ → 0⁺} g (y, σ)` exists, and `Ψ` is continuous on `W`.  The point is that the Hölder bound gives `‖g (y,σ) - Ψ y‖ ≤ C σ^β` with `C` independent of `y`. -/
theorem continuousOn_traceLimUnder {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {β : ℝ} (hβ : 0 < β) {k : ℕ} {W : Set G} (hW : IsOpen W) {ε : ℝ} (hε : 0 < ε)
    {g : G × ℝ → ℂ} (hfin : Work.CR.Flat.holderNorm k β g (W ×ˢ Set.Ioo 0 ε) ≠ ⊤) :
    ContinuousOn (fun y : G => Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (fun σ : ℝ => g (y, σ))) W := by
  classical
  set Ω : Set (G × ℝ) := W ×ˢ Set.Ioo 0 ε with hΩdef
  have hfinΩ : Work.CR.Flat.holderNorm k β g Ω ≠ ⊤ := by rw [hΩdef]; exact hfin
  set C : ℝ := (Work.CR.Flat.holderNorm k β g Ω).toReal with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact ENNReal.toReal_nonneg
  -- the order `0` part of the `C^{k,β}` norm controls `g` itself on the slab
  have hholder : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (g x) (g y) ≤ C * dist x y ^ β := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simp [dist_self, Real.zero_rpow hβ.ne']
    · have hsemi := Work.CR.Flat.le_holderSeminorm 0 β g Ω hx hy hxy
      have hle := le_trans hsemi
        (Work.CR.Flat.holderSeminorm_le_holderNorm k β g Ω (Nat.zero_le k))
      have hreal : ‖iteratedFDerivWithin ℝ 0 g Ω x - iteratedFDerivWithin ℝ 0 g Ω y‖
          / ‖x - y‖ ^ β ≤ C := by
        rw [hCdef]
        exact (ENNReal.ofReal_le_iff_le_toReal hfinΩ).mp hle
      have hpos : 0 < ‖x - y‖ ^ β :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) β
      have h1 : ‖iteratedFDerivWithin ℝ 0 g Ω x - iteratedFDerivWithin ℝ 0 g Ω y‖
          ≤ C * ‖x - y‖ ^ β := (div_le_iff₀ hpos).mp hreal
      have hdist : dist (iteratedFDerivWithin ℝ 0 g Ω x) (iteratedFDerivWithin ℝ 0 g Ω y)
          = dist (g x) (g y) := dist_iteratedFDerivWithin_zero g Ω x g Ω y
      calc dist (g x) (g y)
          = ‖iteratedFDerivWithin ℝ 0 g Ω x - iteratedFDerivWithin ℝ 0 g Ω y‖ := by
              rw [← hdist, dist_eq_norm]
        _ ≤ C * ‖x - y‖ ^ β := h1
        _ = C * dist x y ^ β := by rw [dist_eq_norm]
  -- for `y ∈ W` the trace `σ ↦ g (y,σ)` is Hölder, hence Cauchy as `σ → 0⁺`, hence convergent
  have hlim : ∀ y ∈ W, ∃ L : ℂ, Tendsto (fun σ : ℝ => g (y, σ)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    intro y hy
    have hbdd : ∀ σ ∈ Set.Ioo 0 ε, ∀ τ ∈ Set.Ioo 0 ε,
        dist (g (y, σ)) (g (y, τ)) ≤ C * dist σ τ ^ β := by
      intro σ hσ τ hτ
      have h1 := hholder (y, σ) ⟨hy, hσ⟩ (y, τ) ⟨hy, hτ⟩
      rwa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at h1
    have hunif : UniformContinuousOn (fun σ : ℝ => g (y, σ)) (Set.Ioo 0 ε) :=
      Work.NN.Final.uniformContinuousOn_of_holder hβ hC0 hbdd
    have hCau : Cauchy (𝓝[>] (0 : ℝ)) :=
      ⟨nhdsGT_neBot 0,
        le_trans (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
          (cauchy_nhds (a := (0 : ℝ))).2⟩
    have hCauMap : Cauchy (Filter.map (fun σ : ℝ => g (y, σ)) (𝓝[>] (0 : ℝ))) :=
      Cauchy.map_of_le hCau hunif (Filter.le_principal_iff.mpr (Ioo_mem_nhdsGT hε))
    exact cauchy_map_iff_exists_tendsto.mp hCauMap
  let Ψ : G → ℂ := fun y => Filter.limUnder (𝓝[>] (0 : ℝ)) (fun σ : ℝ => g (y, σ))
  have hΨ : ∀ y ∈ W, Tendsto (fun σ : ℝ => g (y, σ)) (𝓝[>] (0 : ℝ)) (𝓝 (Ψ y)) := by
    intro y hy
    exact tendsto_nhds_limUnder (hlim y hy)
  -- the boundary values inherit the Hölder bound, uniformly in the boundary parameter
  have hΨholder : ∀ y ∈ W, ∀ z ∈ W, dist (Ψ y) (Ψ z) ≤ C * dist y z ^ β := by
    intro y hy z hz
    have hbound : ∀ᶠ σ in 𝓝[>] (0 : ℝ), dist (g (y, σ)) (g (z, σ)) ≤ C * dist y z ^ β := by
      filter_upwards [Ioo_mem_nhdsGT hε] with σ hσ
      have h1 := hholder (y, σ) ⟨hy, hσ⟩ (z, σ) ⟨hz, hσ⟩
      rwa [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at h1
    have htend : Tendsto (fun σ : ℝ => dist (g (y, σ)) (g (z, σ))) (𝓝[>] (0 : ℝ))
        (𝓝 (dist (Ψ y) (Ψ z))) := (hΨ y hy).dist (hΨ z hz)
    exact le_of_tendsto htend hbound
  exact (Work.NN.Final.uniformContinuousOn_of_holder hβ hC0 hΨholder).continuousOn

end Work.NN.DiscRadial
