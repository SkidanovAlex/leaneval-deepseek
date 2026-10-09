import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.NormGroupTransport
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- The norm subgroup `N_{L/k} C_L` of the idèle class group of `k` is insensitive to replacing the
finite extension `L` by an isomorphic one: for a `k`-algebra equivalence `e : L ≃ₐ[k] L'` the two
norm subgroups coincide.

This is immediate from the transport of the norm subgroup along the idèle class group isomorphism
`ideleClassEquiv (RingEquiv.refl k)` attached to `e`: applying it to `L` itself (with `eL = refl`)
shows that it fixes `N_{L/k} C_L`, while applying it to `e` shows that it carries `N_{L/k} C_L` onto
`N_{L'/k} C_{L'}`. -/
theorem mem_normClassSubgroup_iff_of_algEquiv {k L L' : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra k L] [Algebra k L']
    [FiniteDimensional k L] [FiniteDimensional k L'] (e : L ≃ₐ[k] L')
    (q : NK.GlobalCFT.IdeleClassGroup k) :
    q ∈ NK.GlobalCFT.Idele.normClassSubgroup k L ↔
      q ∈ NK.GlobalCFT.Idele.normClassSubgroup k L' := by
  have h1 := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
    (RingEquiv.refl k) (RingEquiv.refl L) (fun x => rfl)
  have h2 := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
    (RingEquiv.refl k) e.toRingEquiv (fun x => by simpa using e.commutes x)
  have h : NK.GlobalCFT.Idele.normClassSubgroup k L =
      NK.GlobalCFT.Idele.normClassSubgroup k L' := h1.symm.trans h2
  rw [h]

end Work.SSGRoute.Sha2Lib
