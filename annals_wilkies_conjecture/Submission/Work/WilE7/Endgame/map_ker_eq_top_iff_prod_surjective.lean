import Mathlib

namespace Work.WilE7.Endgame

theorem map_ker_eq_top_iff_prod_surjective {V Z W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Z] [Module ℝ Z] [AddCommGroup W] [Module ℝ W]
    (J : V →ₗ[ℝ] Z) (A : V →ₗ[ℝ] W) (hJ : J.range = ⊤) :
    (LinearMap.ker J).map A = ⊤ ↔ Function.Surjective (J.prod A) := by
  constructor
  · -- If A maps the kernel of J onto W, then given (z, w) pick v₀ with J v₀ = z,
    -- then adjust by an element of the kernel to hit w.
    intro h
    rintro ⟨z, w⟩
    have hz : z ∈ J.range := by rw [hJ]; exact Submodule.mem_top
    obtain ⟨v₀, hv₀⟩ := hz
    have hw : w - A v₀ ∈ (LinearMap.ker J).map A := by rw [h]; exact Submodule.mem_top
    rw [Submodule.mem_map] at hw
    obtain ⟨k, hk, hkA⟩ := hw
    rw [LinearMap.mem_ker] at hk
    refine ⟨v₀ + k, ?_⟩
    rw [LinearMap.prod_apply]
    simp [hv₀, hk, hkA]
  · -- Conversely, surjectivity of J.prod A gives a preimage of (0, w) in the kernel.
    intro h
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨v, hv⟩ := h (0, w)
    rw [Submodule.mem_map]
    refine ⟨v, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      have := congr_arg Prod.fst hv
      simpa [LinearMap.prod_apply] using this
    · have := congr_arg Prod.snd hv
      simpa [LinearMap.prod_apply] using this

end Work.WilE7.Endgame
