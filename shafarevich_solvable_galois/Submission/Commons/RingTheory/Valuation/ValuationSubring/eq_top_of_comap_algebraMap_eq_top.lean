import Mathlib.RingTheory.Valuation.LocalSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

/-- **A valuation subring containing a field that the ambient field is algebraic over is
everything.**  If `A : ValuationSubring K'` contains the image of `F` (equivalently
`A.comap (algebraMap F K') = ⊤`) and `K'` is algebraic over `F`, then `A = ⊤`. -/
theorem eq_top_of_comap_algebraMap_eq_top {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    (A : ValuationSubring K') (halg : Algebra.IsAlgebraic F K')
    (h : A.comap (algebraMap F K') = ⊤) : A = ⊤ := by
  -- The image of `F` is contained in `A`.
  have hFA : ∀ f : F, algebraMap F K' f ∈ A.toSubring := fun f =>
    (ValuationSubring.mem_comap).mp (by
      have : f ∈ A.comap (algebraMap F K') := by rw [h]; exact ValuationSubring.mem_top f
      exact this)
  -- The induced ring homomorphism `F → A`.
  let ψ : F →+* ↥A.toSubring := (algebraMap F K').codRestrict A.toSubring hFA
  -- Every element of `K'` is integral over `A`: it is integral over `F ⊆ A` (`F` is a field
  -- and `K'` is algebraic over `F`), and integrality descends along the composite
  -- `F → A → K'`.
  have key : ∀ x : K', IsIntegral F x → IsIntegral ↥A.toSubring x := fun x hx =>
    IsIntegral.map_of_comp_eq ψ (RingHom.id K') (RingHom.ext fun f => rfl) hx
  -- A valuation subring is a maximal local subring, hence integrally closed in `K'`;
  -- so every element of `K'` lies in `A`.
  refine le_antisymm (ValuationSubring.le_top A) ?_
  intro x _
  exact LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring
    (key x (halg.isAlgebraic x).isIntegral)

end Commons.RingTheory.Valuation.ValuationSubring