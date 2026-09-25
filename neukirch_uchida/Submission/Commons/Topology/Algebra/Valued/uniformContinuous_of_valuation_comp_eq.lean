import Mathlib.Topology.Algebra.Valued.ValuationTopology

namespace Commons.Topology.Algebra.Valued

open Filter

set_option linter.style.haveILetI false in
/-- If a ring endomorphism `f` preserves a valuation `v` (i.e. `v (f x) = v x` for all `x`),
then `f` is uniformly continuous for the uniform structure induced by `v`.

This is the natural "valuations are preserved, so is the uniformity" statement: the uniformity
of `Valued.mk' v` has a basis of entourages `{p | v.restrict (p.2 - p.1) < γ}`, and `f` sends
`y - x` to `f y - f x = f (y - x)` whose `v`-value is unchanged. -/
theorem uniformContinuous_of_valuation_comp_eq {R : Type*} [Ring R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (f : R →+* R)
    (hf : ∀ x : R, v (f x) = v x) :
    @UniformContinuous R R (Valued.mk' v).toUniformSpace (Valued.mk' v).toUniformSpace f := by
  letI : Valued R Γ₀ := Valued.mk' v
  have hres : ∀ x : R, (Valued.v : Valuation R Γ₀).restrict (f x)
      = (Valued.v : Valuation R Γ₀).restrict x :=
    fun x => (Valuation.restrict_inj (Valued.v : Valuation R Γ₀)).mpr (hf x)
  rw [UniformContinuous]
  refine (Valued.hasBasis_uniformity R Γ₀).tendsto_iff (Valued.hasBasis_uniformity R Γ₀) |>.mpr ?_
  intro γ _
  refine ⟨γ, trivial, ?_⟩
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [← map_sub, hres]
  exact hx

end Commons.Topology.Algebra.Valued