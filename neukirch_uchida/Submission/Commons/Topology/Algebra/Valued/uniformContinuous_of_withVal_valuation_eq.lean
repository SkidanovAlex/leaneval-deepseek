import Mathlib.Topology.Algebra.Valued.WithVal

namespace Commons.Topology.Algebra.Valued


/-- A ring automorphism of `WithVal v` that preserves the valuation is uniformly continuous
for the uniform structure induced by that valuation. -/
theorem uniformContinuous_of_withVal_valuation_eq {R : Type*} [Ring R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (f : WithVal v ≃+* WithVal v)
    (hf : ∀ x : WithVal v, WithVal.valuation v (f x) = WithVal.valuation v x) :
    UniformContinuous (f : WithVal v → WithVal v) := by
  -- view `f` as an additive monoid hom so that we may apply
  -- `uniformContinuous_of_continuousAt_zero`
  let g : WithVal v →+ WithVal v := f.toAddEquiv.toAddMonoidHom
  have hgc : (g : WithVal v → WithVal v) = f := rfl
  rw [← hgc]
  apply uniformContinuous_of_continuousAt_zero
  -- it remains to see that `g` is continuous at `0`
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero (WithVal v) Γ₀).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal v) Γ₀)]
  intro γ _
  -- the basic neighbourhood of `0` with radius `γ` is mapped into itself
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hfx : Valued.v (g x) = Valued.v x := by
    change WithVal.valuation v (g x) = WithVal.valuation v x
    simp only [hgc]
    exact hf x
  rw [Valuation.restrict_lt_iff_lt_embedding, hfx]
  rwa [Valuation.restrict_lt_iff_lt_embedding] at hx

end Commons.Topology.Algebra.Valued