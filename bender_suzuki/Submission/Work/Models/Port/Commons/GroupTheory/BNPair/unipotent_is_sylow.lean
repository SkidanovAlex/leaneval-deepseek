import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.BNPair

/-- In a rank-one `BN`-pair with `B = U ⊔ T`, `U ⊓ T = ⊥`, `T` normalizing the `2`-group `U`
and `[G : B] = |U| + 1`, the unipotent subgroup `U` has odd index in `G`; equivalently `U` contains
a Sylow `2`-subgroup.  (`T` has odd order and `|U|` is a power of `2`, hence `|U|` is even and
`|U| + 1` is odd; the index `[G : U] = [G : B] · |T|` is a product of odd numbers.) -/
theorem unipotent_is_sylow {G : Type*} [Group G] [Finite G] (B U T : Subgroup G)
    (hB : B = U ⊔ T) (hUT : U ⊓ T = ⊥) (hTnU : T ≤ Subgroup.normalizer (U : Set G))
    (hUne : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hoddT : Odd (Nat.card T))
    (hindex : B.index = Nat.card U + 1) : ¬ 2 ∣ U.index := by
  -- `|U|` is a power of `2` and `U ≠ ⊥`, so it is even.
  have hUeven : Even (Nat.card U) := by
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hU2
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hUne ((Subgroup.card_eq_one).mp hn)
    rw [hn]
    exact Nat.even_pow.mpr ⟨by decide, hn0⟩
  -- `T` has odd order, so `2 ∤ |T|`.
  have hT : ¬ 2 ∣ Nat.card T := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hoddT
  -- `|U| + 1` is odd, so `2 ∤ [G : B]`.
  have hBidx : ¬ 2 ∣ B.index := by
    rw [hindex, ← even_iff_two_dvd, Nat.even_add_one]
    exact fun h => h hUeven
  exact Commons.GroupTheory.IsPGroup.not_dvd_index_of_eq_sup U T B hB hUT hTnU hU2 hT hBidx

end Commons.GroupTheory.BNPair
