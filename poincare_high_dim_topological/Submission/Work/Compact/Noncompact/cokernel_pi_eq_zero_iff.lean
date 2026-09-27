import Mathlib

namespace Work.Compact.Noncompact

open CategoryTheory Limits ModuleCat

/-- In the category of `ℤ`-modules, the cokernel projection of `f : M ⟶ N` kills an element
`x : N` exactly when `x` lies in the range of the underlying linear map of `f`. -/
theorem cokernel_pi_eq_zero_iff {M N : ModuleCat ℤ} (f : M ⟶ N) (x : N) :
    (CategoryTheory.Limits.cokernel.π f) x = 0 ↔ x ∈ LinearMap.range f.hom := by
  have h := ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv_apply (f := f) x
  rw [← h]
  have hinj : Function.Injective (ModuleCat.cokernelIsoRangeQuotient f).inv := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  constructor
  · intro hx
    have h0 : (Submodule.Quotient.mk x : N ⧸ LinearMap.range f.hom) = 0 :=
      hinj (by rw [hx, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  · intro hx
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero]

end Work.Compact.Noncompact
