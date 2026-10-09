import Mathlib
import Submission.Work.SSGRoute.ELFImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- The `p`-torsion of the units of a local field is finite.

The units `u` of the local field `K_w` with `u ^ p = 1` are exactly the `p`-th roots of unity in
the field `K_w`, i.e. the roots of `X ^ p - 1`; since `K_w` is a field, a nonzero polynomial of
degree `p` has at most `p` roots there, so this set is finite (indeed of cardinality at most `p`).

Formally we use Mathlib's `rootsOfUnity p K_w`, a subgroup of `K_wˣ` whose finiteness is already
established for any domain, and transport it across the defining equivalence of `mem_rootsOfUnity`.
-/
theorem localField_units_pTorsion_finite (K : Type) [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) [Fact p.Prime] :
    Finite {u : (NK.GlobalCFT.Place.localField K w)ˣ // u ^ p = 1} := by
  refine Finite.of_injective
    (fun u : {u : (NK.GlobalCFT.Place.localField K w)ˣ // u ^ p = 1} =>
      (⟨u.1, (mem_rootsOfUnity p u.1).2 u.2⟩ :
        rootsOfUnity p (NK.GlobalCFT.Place.localField K w))) ?_
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  exact Subtype.ext (Subtype.ext_iff.mp h)

end Work.SSGRoute
