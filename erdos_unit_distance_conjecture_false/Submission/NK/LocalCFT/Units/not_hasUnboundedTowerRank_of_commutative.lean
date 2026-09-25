import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
import Submission.NK.LocalCFT.Units.infinite_quot_powSubgroup_iff
import Submission.NK.LocalCFT.Units.natCard_quot_powSubgroup_le
import Submission.NK.LocalCFT.Units.numIndexSubgroups_eq_zero_of_infinite

/-!
# Commutative groups have bounded `ℓ`-tower rank

For a commutative group `G` the number of index-`ℓ` subgroups of a finite-index subgroup `V ≤ G`
is bounded independently of `V`: it equals the number of index-`ℓ` subgroups of the elementary
abelian `ℓ`-group `V ⧸ V ^ ℓ`, and

* if `G ⧸ G ^ ℓ` is finite then `V ⧸ V ^ ℓ` is finite of no larger cardinality, so the number of
  its index-`ℓ` subgroups is at most `2 ^ |G ⧸ G ^ ℓ|`;
* if `G ⧸ G ^ ℓ` is infinite then `V ⧸ V ^ ℓ` is infinite and an infinite group of exponent `ℓ`
  has either no or infinitely many index-`ℓ` subgroups, so the count is `0`.

Consequently `¬ HasUnboundedTowerRank ℓ G` for every commutative `G` and every `ℓ`.
-/

open scoped Classical

namespace NK.LocalCFT.Units

noncomputable section

/-- The number of index-`1` subgroups of a group is `1` (there is only `⊤`). -/
lemma numIndexSubgroups_one (V : Type*) [Group V] :
    NK.LocalAnabelian.numIndexSubgroups 1 V = 1 := by
  rw [NK.LocalAnabelian.numIndexSubgroups, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨⊤, Subgroup.index_top⟩⟩⟩
  exact (Subgroup.index_eq_one.mp a.2).trans (Subgroup.index_eq_one.mp b.2).symm

/-- **Index-`ℓ` subgroups of a commutative group and of its maximal elementary abelian
`ℓ`-quotient.**  Since `K.index = ℓ` forces `V ^ ℓ ≤ K`, index-`ℓ` subgroups of `V` are in
bijection with index-`ℓ` subgroups of `V ⧸ V ^ ℓ`. -/
lemma numIndexSubgroups_quot_powSubgroup (V : Type*) [CommGroup V] (ℓ : ℕ) :
    NK.LocalAnabelian.numIndexSubgroups ℓ V =
      NK.LocalAnabelian.numIndexSubgroups ℓ
        (V ⧸ (powMonoidHom ℓ : V →* V).range) := by
  rw [NK.LocalAnabelian.numIndexSubgroups, NK.LocalAnabelian.numIndexSubgroups]
  exact NK.LocalInputs.CommGroupRank.natCard_indexP_eq_natCard_quot_powSubgroup

/-- A finite group has at most `2 ^ |M|` subgroups of index `ℓ`. -/
lemma natCard_index_eq_le_two_pow (M : Type*) [Group M] [Finite M] (ℓ : ℕ) :
    Nat.card {K : Subgroup M // K.index = ℓ} ≤ 2 ^ Nat.card M := by
  refine (Nat.card_le_card_of_injective
    (fun K : {K : Subgroup M // K.index = ℓ} => (K.1 : Subgroup M))
    (fun a b h => Subtype.ext h)).trans ?_
  refine (Nat.card_le_card_of_injective
    (fun K : Subgroup M => (K : Set M))
    (fun a b h => Subgroup.ext (Set.ext_iff.mp h))).trans ?_
  show Nat.card (M → Prop) ≤ 2 ^ Nat.card M
  rw [Nat.card_fun]
  norm_num

/-- **The main bound.**  For a commutative group `G` and `2 ≤ ℓ`, the number of index-`ℓ`
subgroups of any finite-index subgroup `V ≤ G` is bounded by a constant depending only on `G`
and `ℓ`. -/
theorem numIndexSubgroups_le_of_commutative_bound {G : Type*} [CommGroup G] (ℓ : ℕ)
    (hℓ : 2 ≤ ℓ) :
    ∃ N : ℕ, ∀ V : Subgroup G, V.FiniteIndex →
      NK.LocalAnabelian.numIndexSubgroups ℓ V ≤ N := by
  classical
  rcases em (Infinite (G ⧸ (powMonoidHom ℓ : G →* G).range)) with hinf | hfin
  · refine ⟨0, fun V hV => ?_⟩
    have hVinf : Infinite (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range) :=
      (infinite_quot_powSubgroup_iff V hV ℓ).mpr hinf
    have hkill : ∀ x : (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range), x ^ ℓ = 1 := by
      intro x
      obtain ⟨v, rfl⟩ :=
        QuotientGroup.mk'_surjective (powMonoidHom ℓ : ↥V →* ↥V).range x
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_range.mpr ⟨v, rfl⟩
    have hz := numIndexSubgroups_eq_zero_of_infinite hℓ hkill hVinf
    rw [numIndexSubgroups_quot_powSubgroup ↥V ℓ]
    exact le_of_eq hz
  · refine ⟨2 ^ Nat.card (G ⧸ (powMonoidHom ℓ : G →* G).range), fun V hV => ?_⟩
    haveI : Finite (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range) :=
      not_infinite_iff_finite.mp fun hVinf =>
        hfin ((infinite_quot_powSubgroup_iff V hV ℓ).mp hVinf)
    have hle : Nat.card (↥V ⧸ (powMonoidHom ℓ : ↥V →* ↥V).range) ≤
        Nat.card (G ⧸ (powMonoidHom ℓ : G →* G).range) := natCard_quot_powSubgroup_le V hV ℓ
    rw [numIndexSubgroups_quot_powSubgroup ↥V ℓ]
    exact
      (natCard_index_eq_le_two_pow _ ℓ).trans (Nat.pow_le_pow_right (by norm_num) hle)

/-- **A commutative group has bounded `ℓ`-tower rank for every `ℓ`.** -/
theorem not_hasUnboundedTowerRank_of_commutative (G : Type*) [Group G] (ℓ : ℕ)
    (hcomm : ∀ x y : G, x * y = y * x) :
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ G := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  rcases lt_or_ge ℓ 2 with h2 | h2
  · interval_cases ℓ
    · -- `ℓ = 0`
      intro h
      obtain ⟨V, hVfin, ⟨k, hk⟩, hN⟩ := h (NK.LocalAnabelian.numIndexSubgroups 0 G)
      have hne : V.index ≠ 0 := Subgroup.finiteIndex_iff.mp hVfin
      have hk0 : k = 0 := by
        by_contra hk0
        exact hne (by rw [hk, zero_pow hk0])
      have htop : V = ⊤ := Subgroup.index_eq_one.mp (by rw [hk, hk0, pow_zero])
      have hVeq : NK.LocalAnabelian.numIndexSubgroups 0 V =
          NK.LocalAnabelian.numIndexSubgroups 0 G := by
        rw [htop]
        exact NK.LocalAnabelian.numIndexSubgroups_congr Subgroup.topEquiv 0
      omega
    · -- `ℓ = 1`
      intro h
      obtain ⟨V, -, -, hN⟩ := h 1
      rw [numIndexSubgroups_one] at hN
      omega
  · -- `2 ≤ ℓ`
    intro h
    obtain ⟨N, hN⟩ := numIndexSubgroups_le_of_commutative_bound (G := G) ℓ h2
    obtain ⟨V, hVfin, -, hNV⟩ := h N
    exact absurd hNV (not_lt.mpr (hN V hVfin))

end

end NK.LocalCFT.Units
