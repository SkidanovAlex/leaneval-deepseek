import Mathlib
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.conj_mem_H_of_mem_Q`

In the split rank-one set-up (`IsSplitRankOne H Q t`) the non-identity elements of `Q` act
freely on `Ω ∖ {∞}`, `Ω = G ⧸ H` (`Work.ThmG.Q_smul_eq_self`).  Consequently, if
`x y x⁻¹ ∈ H` for some `1 ≠ y ∈ Q`, then `x` must stabilise the base point, i.e. `x ∈ H`:
otherwise `y` would fix the point `x⁻¹ • ∞ ≠ ∞`, forcing `y = 1`.

This is the group-theoretic transfer used repeatedly in Feit's argument: it converts
`H`-membership of an `H`-conjugate of a non-identity element of `Q` into membership of the
conjugating element in `H`.
-/

namespace Work.ZassenhausTwoGroup

theorem conj_mem_H_of_mem_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {y : G} (hy : y ∈ Q) (hy1 : y ≠ 1) :
    ∀ x : G, x * y * x⁻¹ ∈ H → x ∈ H := by
  intro x hmem
  by_contra hxH
  -- `x⁻¹ • ∞ ≠ ∞`
  have hxinv : x⁻¹ ∉ H := fun hinv => hxH (H.inv_mem_iff.mp hinv)
  have hω : x⁻¹ • Work.ThmG.basePt H ≠ Work.ThmG.basePt H := by
    rw [Work.ThmG.smul_basePt]
    exact (Work.ThmG.basePt_ne_iff H x⁻¹).mpr hxinv
  -- `y` fixes `x⁻¹ • ∞` because `x y x⁻¹ ∈ H`
  have hfix : y • (x⁻¹ • Work.ThmG.basePt H) = x⁻¹ • Work.ThmG.basePt H := by
    calc y • (x⁻¹ • Work.ThmG.basePt H)
        = (y * x⁻¹) • Work.ThmG.basePt H := by rw [← mul_smul]
      _ = (x⁻¹ * (x * y * x⁻¹)) • Work.ThmG.basePt H := by
            rw [show x⁻¹ * (x * y * x⁻¹) = y * x⁻¹ by group]
      _ = x⁻¹ • ((x * y * x⁻¹) • Work.ThmG.basePt H) := by rw [mul_smul]
      _ = x⁻¹ • Work.ThmG.basePt H := by
            rw [Work.ThmG.smul_basePt_of_mem H hmem]
  exact hy1 (Work.ThmG.Q_smul_eq_self h hy hfix hω)

end Work.ZassenhausTwoGroup
