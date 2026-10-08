import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A minimal normal `p`-subgroup is abelian

Let `G` be a finite group and `N ◁ G` a minimal normal subgroup which happens to be a
`p`-group for some prime `p`.  Then `N` is abelian.

The argument is the standard one: a minimal normal subgroup is *characteristically simple*,
i.e. has no nontrivial proper characteristic subgroup.  The centre `Z(N)` of `N` is a
characteristic subgroup of `N`, and since `N` is a normal subgroup of `G` it follows that
`Z(N)` is normal in `G`.  Minimality of `N` forces `Z(N) = 1` or `Z(N) = N`; but a nontrivial
finite `p`-group has nontrivial centre, so `Z(N) = N` and `N` is abelian.
-/

namespace Work.Fitting

theorem isMinimalNormal_isPGroup_commutative (p : ℕ) (G : Type*) [Group G] [Finite G]
    (hp : p.Prime) {N : Subgroup G} (h : Work.Fitting.IsMinimalNormal N) (hN : IsPGroup p ↥N) :
    IsMulCommutative ↥N := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNnorm, hNne, hNmin⟩ := h
  have : N.Normal := hNnorm
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
  -- The centre of `N`, pushed into `G`.
  set Z : Subgroup G := (Subgroup.center ↥N).map N.subtype with hZ
  -- `Z` is normal in `G`: it is the image of a characteristic subgroup of the normal
  -- subgroup `N`.
  have hZnorm : Z.Normal := by
    rw [hZ]
    exact ConjAct.normal_of_characteristic_of_normal
  have hZle : Z ≤ N := by rw [hZ]; exact Subgroup.map_subtype_le _
  -- `Z` is nontrivial because a nontrivial finite `p`-group has nontrivial centre.
  have hZne : Z ≠ ⊥ := by
    have hnt : Subgroup.center ↥N ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp (IsPGroup.center_nontrivial hN)
    rw [hZ]
    intro hbot
    apply hnt
    apply Subgroup.map_injective (Subgroup.subtype_injective N)
    rw [hbot, Subgroup.map_bot]
  -- Minimality of `N` forces `Z = N`.
  have hZN : Z = N := hNmin Z hZnorm hZle hZne
  -- Hence the centre of `N` is all of `N`.
  have hcenter : Subgroup.center ↥N = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective N)
    rw [← hZ, hZN, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.center_eq_top_iff.mp hcenter

end Work.Fitting
