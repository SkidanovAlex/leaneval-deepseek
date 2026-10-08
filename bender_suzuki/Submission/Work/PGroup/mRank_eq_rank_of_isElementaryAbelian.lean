import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.rank_eq_log_card_of_isElementaryAbelian
import Submission.Work.PGroup.rank_le_mRank
import Submission.Work.PGroup.exists_rank_eq_mRank

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped IsMulCommutative

namespace Work.PGroup

/-- For a finite elementary abelian `p`-subgroup `E`, the `p`-rank `m_p(E)` (the maximal
minimal number of generators of an elementary abelian `p`-subgroup of `E`) equals the minimal
number of generators of `E` itself.

There are two inequalities:

* `Group.rank E ≤ mRank p E` because `E`, viewed as the top subgroup of `↥E`, is an elementary
  abelian `p`-subgroup and `Group.rank ⊤ = Group.rank E`;
* `mRank p E ≤ Group.rank E` because every elementary abelian `p`-subgroup `F ≤ ↥E` satisfies
  `Group.rank F = log_p |F| ≤ log_p |E| = Group.rank E` (both `F` and `E` are `𝔽_p`-vector
  spaces of the corresponding dimension). -/
theorem mRank_eq_rank_of_isElementaryAbelian {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (E : Subgroup G) [Finite E] (hE : Work.PGroup.IsElementaryAbelian p E) :
    Work.PGroup.mRank p E = Group.rank E := by
  classical
  -- `E` itself is an `𝔽_p`-vector space, so `Group.rank E = log_p |E|`.
  have hlogE : Group.rank ↥E = Nat.log p (Nat.card ↥E) :=
    rank_eq_log_card_of_isElementaryAbelian (G := G) hp E hE
  -- The top subgroup of `↥E` is elementary abelian of exponent `p`.
  have hEtop : Work.PGroup.IsElementaryAbelian p (⊤ : Subgroup ↥E) := by
    constructor
    · rw [isMulCommutative_iff]
      intro a b
      exact Subgroup.topEquiv.injective (by
        rw [map_mul, map_mul]
        exact hE.mul_comm (Subgroup.topEquiv a) (Subgroup.topEquiv b))
    · intro x
      exact Subgroup.topEquiv.injective (by
        rw [map_pow, map_one]
        exact hE.pow_eq_one (Subgroup.topEquiv x))
  -- Lower bound: `E` is one of the elementary abelian `p`-subgroups over which `mRank` is taken.
  have hlower : Group.rank ↥E ≤ Work.PGroup.mRank p ↥E := by
    have h := rank_le_mRank (G := ↥E) (⊤ : Subgroup ↥E) hEtop
    rwa [Group.rank_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥E) ≃* ↥E)] at h
  -- Upper bound: `mRank` is attained, and any elementary abelian `p`-subgroup `F ≤ ↥E` has
  -- rank at most that of `E`.
  have hupper : Work.PGroup.mRank p ↥E ≤ Group.rank ↥E := by
    obtain ⟨F, hF, hFrank⟩ := exists_rank_eq_mRank (G := ↥E) p
    haveI : Finite ↥F :=
      Finite.of_injective (Subtype.val : ↥F → ↥E) Subtype.val_injective
    have hlogF : Group.rank ↥F = Nat.log p (Nat.card ↥F) :=
      rank_eq_log_card_of_isElementaryAbelian (G := ↥E) hp F hF
    have hcard : Nat.card ↥F ≤ Nat.card ↥E :=
      Nat.card_le_card_of_injective (Subtype.val : ↥F → ↥E) Subtype.val_injective
    calc Work.PGroup.mRank p ↥E = Group.rank ↥F := hFrank.symm
      _ = Nat.log p (Nat.card ↥F) := hlogF
      _ ≤ Nat.log p (Nat.card ↥E) := Nat.log_mono_right hcard
      _ = Group.rank ↥E := hlogE.symm
  exact le_antisymm hupper hlower

end Work.PGroup
