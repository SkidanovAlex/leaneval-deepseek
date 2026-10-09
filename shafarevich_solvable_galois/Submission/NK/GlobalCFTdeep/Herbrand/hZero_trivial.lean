import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ĥ⁰(G, ℤ) = ℤ/|G|`: the degree-zero Herbrand numerator of the trivial module

For a finite group `G` acting trivially on `ℤ`, the invariants are all of `ℤ` and the norm is
multiplication by `|G|`, so

  `Ĥ⁰(G, ℤ) = ℤ^G ⧸ N(ℤ) = ℤ ⧸ |G|ℤ`,

whose cardinality is `|G|`.  In the notation of the deep chapter this is

  `hZero (Rep.trivial ℤ G ℤ) = Nat.card G`.

The computation `ℤ ⧸ |G|ℤ ≅ ℤ/|G|`, together with the identification
`Ĥ⁰(M) ≅ M^G ⧸ N(M)`, is already available in the commons as
`NU.natCard_tateCohomology_zero_trivial`, so the proof is a change of notation.
-/

namespace NK.GlobalCFTdeep.Herbrand

theorem hZero_trivial (G : Type) [Group G] [Fintype G] :
    hZero (Rep.trivial ℤ G ℤ) = Nat.card G := by
  rw [hZero_def]
  exact NU.natCard_tateCohomology_zero_trivial G

end NK.GlobalCFTdeep.Herbrand
