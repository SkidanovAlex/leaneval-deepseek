import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Algebra.Polynomial.Degree.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Polynomial

/-- If `g` has degree at most that of `f`, and the leading coefficient of `f` is not too small
(norm at least `ε`), then `g` cannot drop below the degree of `f`: the difference `f - g` has, at
the index `f.natDegree`, the coefficient `f.coeff f.natDegree`, whose norm is at least `ε` and
therefore cannot be strictly bounded by the sup norm of `f - g`. -/
lemma natDegree_eq_of_supNorm_lt {K : Type*} [NormedField K] (f g : Polynomial K) (ε : ℝ)
    (hg : g.natDegree ≤ f.natDegree) (hε0 : 0 < ε) (hA : ε ≤ ‖f.coeff f.natDegree‖)
    (hlt : (f - g).supNorm < ε) : g.natDegree = f.natDegree := by
  refine le_antisymm hg ?_
  by_contra h
  rw [not_le] at h
  -- At the top index of `f`, the coefficient of `f - g` is that of `f`.
  have hc : (f - g).coeff f.natDegree = f.coeff f.natDegree :=
    Polynomial.coeff_sub_eq_left_of_lt (p := f) (q := g) h
  -- But the sup norm bounds every coefficient norm by `(f - g).supNorm < ε`.
  have h1 : ‖(f - g).coeff f.natDegree‖ ≤ (f - g).supNorm := (f - g).le_supNorm f.natDegree
  have h2 : ‖(f - g).coeff f.natDegree‖ < ε := lt_of_le_of_lt h1 hlt
  rw [hc] at h2
  linarith

end Commons.FieldTheory.Polynomial