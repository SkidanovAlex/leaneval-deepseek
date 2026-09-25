import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Simple

namespace Commons.GroupTheory.QuotientGroup

/-- A maximal (coatom) normal subgroup has simple quotient.  (Only this forward direction holds: quotient-simple does not imply subgroup-maximal, only normal-maximal; see `isSimpleGroup_quotient_iff_maximal_normal`.) -/
theorem isSimpleGroup_quotient_of_coatom {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hco : IsCoatom N) : IsSimpleGroup (G ⧸ N) := by
  rw [isSimpleGroup_iff]
  constructor
  · exact QuotientGroup.nontrivial_iff.mpr (IsCoatom.ne_top hco)
  · intro H hH
    -- `H` is a normal subgroup of the quotient; pull it back to `G`.
    have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have hNle : N ≤ H.comap (QuotientGroup.mk' N) := by
      intro x hx
      have hx1 : (QuotientGroup.mk' N) x = 1 := by
        simpa using (QuotientGroup.eq_one_iff x).mpr hx
      change (QuotientGroup.mk' N) x ∈ H
      rw [hx1]
      exact Subgroup.one_mem H
    -- By coatomality the pullback is either all of `G` or `N` itself.
    have hcases : H.comap (QuotientGroup.mk' N) = ⊤ ∨ H.comap (QuotientGroup.mk' N) = N :=
      (IsCoatom.le_iff hco).mp hNle
    rcases hcases with htop | hN
    · right
      -- Pullback is `⊤`, so `H` is the whole quotient.
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj H, htop]
      exact Subgroup.map_top_of_surjective (QuotientGroup.mk' N) hsurj
    · left
      -- Pullback is `N` (the kernel), so `H` is trivial.
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj H, hN]
      simp

end Commons.GroupTheory.QuotientGroup