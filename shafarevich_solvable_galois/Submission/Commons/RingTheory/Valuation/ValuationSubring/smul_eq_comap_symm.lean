import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

open scoped Pointwise

/-- The image of a valuation subring `A` of a field `K` under a ring automorphism `g` of `K`
is the preimage `A.comap g.symm`. -/
theorem smul_eq_comap_symm {K : Type*} [Field K] (g : K ≃+* K) (A : ValuationSubring K) :
    g • A = A.comap (g.symm : K →+* K) := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_comap]
  constructor
  · rintro ⟨s, hs, rfl⟩
    change g.symm (g s) ∈ A
    rw [RingEquiv.symm_apply_apply]
    exact hs
  · intro h
    exact ⟨g.symm x, h, g.apply_symm_apply x⟩

end Commons.RingTheory.Valuation.ValuationSubring