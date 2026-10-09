import Mathlib.Analysis.Polynomial.Norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

/-- Coefficients of close polynomials are close in the reverse-triangle form:
a coefficient of `f` exceeds the corresponding coefficient of `g` by at most
the sup-norm distance of `f` and `g`. -/
lemma norm_coeff_ge_sub_supNorm {K : Type*} [NormedField K] (f g : Polynomial K) (i : ℕ) :
    ‖f.coeff i‖ - (f - g).supNorm ≤ ‖g.coeff i‖ := by
  have hsub : ‖f.coeff i - g.coeff i‖ ≤ (f - g).supNorm := by
    simpa [Polynomial.coeff_sub] using (f - g).le_supNorm i
  have hrev : ‖f.coeff i‖ - ‖g.coeff i‖ ≤ ‖f.coeff i - g.coeff i‖ :=
    norm_sub_norm_le _ _
  linarith

end Commons.Analysis.Polynomial
