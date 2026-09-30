import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for Linnik's lemma (well-conditioned count)

Power sums and elementary symmetric functions of a tuple of integers, as used in the
formalisation of `Work.BMF.linnik_bound`.
-/

namespace Work.BMF

/-- The `j`-th power sum `∑ i, (a i) ^ j` of a tuple of integers. -/
def pw {k : ℕ} (a : Fin k → ℤ) (j : ℕ) : ℤ := ∑ i, (a i) ^ j

/-- The `j`-th elementary symmetric function of a tuple of integers, i.e. the sum of the
products `∏ i ∈ s, a i` over all `j`-element subsets `s` of the index set. -/
def esymm {k : ℕ} (a : Fin k → ℤ) (j : ℕ) : ℤ :=
  ∑ s ∈ Finset.powersetCard j (Finset.univ : Finset (Fin k)), ∏ i ∈ s, a i

@[simp] lemma esymm_zero {k : ℕ} (a : Fin k → ℤ) : esymm a 0 = 1 := by
  simp [esymm]

/-- The elementary symmetric functions of a tuple are the multiset elementary symmetric
functions of its multiset of values. -/
lemma esymm_eq_multiset_esymm {k : ℕ} (a : Fin k → ℤ) (j : ℕ) :
    esymm a j = (Finset.univ.val.map a).esymm j := by
  rw [Finset.esymm_map_val]
  rfl

end Work.BMF
