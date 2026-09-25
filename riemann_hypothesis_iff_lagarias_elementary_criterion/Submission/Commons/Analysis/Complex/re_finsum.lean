import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Complex.Basic

namespace Commons.Analysis.Complex

theorem re_finsum {f : ℂ → ℂ} (hf : (Function.support f).Finite) :
    (finsum f).re = finsum (fun u : ℂ => (f u).re) := by
  simpa using AddMonoidHom.map_finsum Complex.reAddGroupHom hf

end Commons.Analysis.Complex