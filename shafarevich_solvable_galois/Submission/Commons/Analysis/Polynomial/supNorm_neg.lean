import Mathlib.Analysis.Polynomial.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

/-- Negating a polynomial does not change its sup-norm: `supNorm` is the
supremum of the norms of the coefficients, and `‖-a‖ = ‖a‖`. -/
lemma supNorm_neg {K : Type*} [SeminormedRing K] (p : Polynomial K) :
    (-p).supNorm = p.supNorm := by
  rw [_root_.Polynomial.supNorm_eq_iSup, _root_.Polynomial.supNorm_eq_iSup]
  simp only [_root_.Polynomial.coeff_neg, norm_neg]

end Commons.Analysis.Polynomial