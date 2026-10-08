import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

theorem sylow_map_eq_of_le {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (P : Sylow p ↥A) {R : Subgroup G} (hR : IsPGroup p R) (hRA : R ≤ A)
    (hle : (P : Subgroup ↥A).map A.subtype ≤ R) : R = (P : Subgroup ↥A).map A.subtype := by
  -- View `R` and `P` as subgroups of `A`.
  set P' : Subgroup ↥A := (P : Subgroup ↥A) with hP'
  set R' : Subgroup ↥A := R.comap A.subtype with hR'
  -- `R'` is a `p`-subgroup of `A` (pull back the `p`-group `R` along the injection `A ↪ G`).
  have hR'pg : IsPGroup p R' := hR.comap_subtype
  -- The assumption `P.map A.subtype ≤ R` says `P' ≤ R'`.
  have hP'le : P' ≤ R' := by
    intro x hx
    rw [hR']
    show A.subtype x ∈ R
    exact hle (Subgroup.mem_map_of_mem A.subtype hx)
  -- Maximality of the Sylow subgroup `P` forces `R' = P'`.
  have hR'eq : R' = P' := P.is_maximal' hR'pg hP'le
  -- Since `R ≤ A`, it is the image of its preimage `R'` under the subtype map.
  have hRmap : R = R'.map A.subtype := by
    rw [hR']
    exact (Subgroup.map_comap_eq_self (f := A.subtype) (H := R)
      (by rwa [Subgroup.range_subtype])).symm
  rw [hRmap, hR'eq, hP']

end Work.ZassenhausSuzuki.Odd
