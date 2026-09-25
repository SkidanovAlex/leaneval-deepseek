import Mathlib

namespace Work.CMRealSubfield.RealSubfield

open NumberField

theorem finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal (K : Type*) [Field K]
    [NumberField K] [NumberField.IsTotallyReal K] :
    Module.finrank ℚ (NumberField.maximalRealSubfield K) = Module.finrank ℚ K := by
  rw [NumberField.IsTotallyReal.maximalRealSubfield_eq_top]
  refine LinearEquiv.finrank_eq ?_
  exact { Subfield.topEquiv.toEquiv with
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl }

end Work.CMRealSubfield.RealSubfield
