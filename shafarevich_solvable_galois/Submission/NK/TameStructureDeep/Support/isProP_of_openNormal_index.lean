import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.Nat.Prime.Defs
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Support

/-- **A compact totally disconnected group all of whose open normal subgroups have `p`-power
index is pro-`p`** in the finite-quotient sense `NK.LocalTame.IsProP p G`: every normal subgroup
of finite index has `p`-power index.

The mathematical content is the classical fact that a pro-`p` group is `ℓ`-divisible for every
prime `ℓ ≠ p` (equivalently: it has no quotient of order `ℓ`); this is proved in
`Submission/Work/TameStructureDeep/Support/isProP_of_openNormal_index_prime.lean`, whose headline
`isProP_of_openNormal_index_prime` has exactly this statement.  We record it here under the
requested name, so that downstream modules can refer to it as
`NK.TameStructureDeep.Support.isProP_of_openNormal_index`. -/
theorem isProP_of_openNormal_index {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {p : ℕ}
    (hp : p.Prime)
    (h : ∀ U : OpenNormalSubgroup G, ∃ k : ℕ, U.toSubgroup.index = p ^ k) :
    NK.LocalTame.IsProP p G :=
  isProP_of_openNormal_index_prime hp h

end NK.TameStructureDeep.Support
