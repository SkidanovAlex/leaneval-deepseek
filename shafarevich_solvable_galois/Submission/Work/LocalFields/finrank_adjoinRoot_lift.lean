import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.LocalFieldAPI
import Submission.Work.LocalFields.irreducible_map_of_irreducible_reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

/-- If `f` is a monic polynomial over the ring of integers `𝒪[k]` of a local field `k`
(whose reduction modulo the maximal ideal is irreducible), then adjoining a root of `f`
to `k` produces a `k`-algebra of dimension `f.natDegree`.

The irreducibility hypothesis is not needed for the *dimension* statement: the dimension of
`AdjoinRoot g` over a field equals `g.natDegree` for any monic `g` (a power basis is given by
`1, X, …, X ^ (deg g - 1)`), and here `deg (f.map (algebraMap 𝒪[k] k)) = deg f` because
`f` is monic.  The hypothesis is kept because it is what the caller has available. -/
theorem finrank_adjoinRoot_lift {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k]
    {f : Polynomial (Valued.integer k)} (hf : f.Monic)
    (h : Irreducible (f.map (IsLocalRing.residue (Valued.integer k)))) :
    Module.finrank k (AdjoinRoot (f.map (algebraMap (Valued.integer k) k))) =
      f.natDegree := by
  have hne : f.map (algebraMap (Valued.integer k) k) ≠ 0 := (hf.map _).ne_zero
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne), AdjoinRoot.powerBasis_dim hne]
  exact Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff _
    (by rw [hf.leadingCoeff]; exact isUnit_one)

end Work.LocalFields
