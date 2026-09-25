import Mathlib.Algebra.Group.Subgroup.Order

namespace Commons.GroupTheory.Subgroup

/-- The image of a maximal subgroup under a surjective homomorphism whose kernel it contains is maximal. -/
theorem isCoatom_map_of_ker_le {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {M : Subgroup G} (hM : IsCoatom M)
    (hker : f.ker ≤ M) : IsCoatom (M.map f) := by
  constructor
  · intro htop
    exact hM.1 (Subgroup.map_injective_of_ker_le (f := f) hker le_top (by
      rw [htop, Subgroup.map_top_of_surjective f hf]))
  · intro N hlt
    have hKtop : N.comap f = ⊤ := by
      apply hM.2
      refine lt_of_le_of_ne ?_ ?_
      · exact (Subgroup.map_le_iff_le_comap).mp (le_of_lt hlt)
      · intro heq
        have : M.map f = N := by
          calc
            M.map f = (N.comap f).map f := by rw [heq]
            _ = N := Subgroup.map_comap_eq_self_of_surjective hf N
        exact (ne_of_lt hlt) this
    calc
      N = (N.comap f).map f := (Subgroup.map_comap_eq_self_of_surjective hf N).symm
      _ = ⊤ := by rw [hKtop, Subgroup.map_top_of_surjective f hf]

end Commons.GroupTheory.Subgroup
