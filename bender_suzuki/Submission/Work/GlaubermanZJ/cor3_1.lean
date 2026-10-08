import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-! ## Bridges used by `cor3_1`

`IsMaxAbelianSubgroup` is phrased with the blueprint's elementwise abelianness predicate and an
*order-maximality* condition ("every abelian subgroup of `S` has order at most `Nat.card A`"),
whereas Thompson's replacement theorem `Work.PGroup.thompson_replacement` consumes the
`Work.PGroup` vocabulary (`IsMulCommutative` + `Nat.card A = maxAbelianOrder S`).  The two
lemmas below convert between the two descriptions. -/

/-- `A` is an abelian subgroup of `S` of maximal order iff `A ≤ S`, `A` is abelian and
`Nat.card A = maxAbelianOrder S`. -/
theorem isMaxAbelianSubgroup_iff {G : Type*} [Group G] (S A : Subgroup G) [Finite S] :
    IsMaxAbelianSubgroup S A ↔
      A ≤ S ∧ Submission.Blueprint.IsAbelianSubgroup A ∧
        Nat.card A = Work.PGroup.maxAbelianOrder S := by
  constructor
  · rintro ⟨hAS, hab, hmax⟩
    refine ⟨hAS, hab, le_antisymm ?_ ?_⟩
    · exact Work.PGroup.le_maxAbelianOrder S A hAS (isAbelianSubgroup_iff.mp hab)
    · rw [Work.PGroup.maxAbelianOrder]
      refine csSup_le ⟨1, ⊥, bot_le, ?_, Subgroup.card_bot⟩ ?_
      · exact IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
      · rintro n ⟨C, hCS, hCab, rfl⟩
        exact hmax C hCS (isAbelianSubgroup_iff.mpr hCab)
  · rintro ⟨hAS, hab, hcard⟩
    refine ⟨hAS, hab, ?_⟩
    intro C hCS hCab
    rw [hcard]
    exact Work.PGroup.le_maxAbelianOrder S C hCS (isAbelianSubgroup_iff.mp hCab)

/-- If `B ≤ N_G(A)` and `A` is abelian then `[B,A,A] = 1`: `B` normalizes `A` forces
`[B,A] ≤ A`, and `A` abelian kills `[A,A]`. -/
theorem commutator_commutator_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    (hA : Submission.Blueprint.IsAbelianSubgroup A)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : ⁅⁅B, A⁆, A⁆ = ⊥ := by
  have hBA' : ⁅B, A⁆ ≤ A := Subgroup.le_normalizer_iff_commutator_le_right.mp hBA
  have hle : ⁅⁅B, A⁆, A⁆ ≤ ⁅A, A⁆ := Subgroup.commutator_mono hBA' le_rfl
  have hbot : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hA x hx y hy).symm
  exact le_antisymm (hbot ▸ hle) bot_le

/-- **A maximal abelian subgroup of `S` normalized by `B`.**  For `S` a finite `p`-group with
`p` odd and `B` an abelian normal subgroup of `S`, `𝒜(S)` contains an element normalized by `B`.

This is the substance of Glauberman's Corollary 3.1.  The proof is the standard descent: starting
from any `A₀ ∈ 𝒜(S)`, if `B` does not normalize `A` then `A ≤ S ≤ N_G(B)` and `B ≰ N_G(A)`, so
Thompson's replacement theorem produces `A' ∈ 𝒜(S)` with `A ∩ B < A' ∩ B`; this strictly increases
`|A ∩ B|`, a bounded quantity, so the descent terminates. -/
theorem exists_maxAbelianSubgroup_le_normalizer {G : Type*} [Group G] (p : ℕ) (hp : p.Prime)
    (hpne : p ≠ 2) (S B : Subgroup G) [Finite S] (hS : IsPGroup p S) (hBS : B ≤ S)
    (hBab : Submission.Blueprint.IsAbelianSubgroup B)
    (hBn : S ≤ Subgroup.normalizer (B : Set G)) :
    ∃ A : Subgroup G, IsMaxAbelianSubgroup S A ∧ B ≤ Subgroup.normalizer (A : Set G) := by
  haveI hfinB : Finite ↥B :=
    Finite.of_injective (Subgroup.inclusion hBS) (Subgroup.inclusion_injective hBS)
  have hBcom : IsMulCommutative ↥B := isAbelianSubgroup_iff.mp hBab
  -- the descent, by strong induction on the strictly decreasing measure
  -- `Nat.card B + 1 - Nat.card (A ⊓ B)`
  have key : ∀ n : ℕ, ∀ A : Subgroup G, IsMaxAbelianSubgroup S A →
      Nat.card B + 1 - Nat.card ↥(A ⊓ B) = n →
      ∃ A' : Subgroup G, IsMaxAbelianSubgroup S A' ∧ B ≤ Subgroup.normalizer (A' : Set G) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih A hA heqn
    by_cases hN : B ≤ Subgroup.normalizer (A : Set G)
    · exact ⟨A, hA, hN⟩
    · obtain ⟨hAS, hAab, hAcard⟩ := (isMaxAbelianSubgroup_iff S A).mp hA
      have hAcom : IsMulCommutative ↥A := isAbelianSubgroup_iff.mp hAab
      have hAB : A ≤ Subgroup.normalizer (B : Set G) := hAS.trans hBn
      obtain ⟨A', hA'S, hA'com, hA'card, -, -, hA'lt⟩ :=
        Work.PGroup.thompson_replacement hp hpne S A B hS hAS hAcom hAcard hBS hBcom hAB hN
      have hA'max : IsMaxAbelianSubgroup S A' :=
        (isMaxAbelianSubgroup_iff S A').mpr ⟨hA'S, isAbelianSubgroup_iff.mpr hA'com, hA'card⟩
      haveI hfinA'B : Finite ↥(A' ⊓ B) :=
        Finite.of_injective (Subgroup.inclusion (inf_le_left.trans hA'S))
          (Subgroup.inclusion_injective _)
      have hcardlt : Nat.card ↥(A ⊓ B) < Nat.card ↥(A' ⊓ B) := by
        have hle : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(A' ⊓ B) := Subgroup.card_le_of_le hA'lt.le
        refine lt_of_le_of_ne hle ?_
        intro heq
        exact hA'lt.ne (Subgroup.eq_of_le_of_card_ge hA'lt.le heq.symm.le)
      have hdecr : Nat.card B + 1 - Nat.card ↥(A' ⊓ B) < n := by
        rw [← heqn]
        exact Nat.sub_lt_sub_left
          (lt_of_le_of_lt (Subgroup.card_le_of_le (inf_le_right : A ⊓ B ≤ B))
            (Nat.lt_succ_self _)) hcardlt
      exact ih _ hdecr A' hA'max rfl
  have hex : ∃ A : Subgroup G, IsMaxAbelianSubgroup S A := by
    obtain ⟨A, hAS, hAcom, hAcard⟩ := Work.PGroup.maxAbelianOrder_attained S
    exact ⟨A, (isMaxAbelianSubgroup_iff S A).mpr
      ⟨hAS, isAbelianSubgroup_iff.mpr hAcom, hAcard⟩⟩
  obtain ⟨A0, hA0⟩ := hex
  exact key _ A0 hA0 rfl

-- Glauberman 1968, Corollary 3.1 (a corollary of Thompson's replacement theorem,
-- delivered as `Work.PGroup.thompson_replacement`, which requires `p` prime and `p ≠ 2`):
-- if `B` is an abelian normal subgroup of the finite p-group `S`, there is `A ∈ 𝒜(S)`
-- (abelian of maximal order) with `B ≤ N(A)` and `[B,A,A] = 1`.
theorem cor3_1 {G : Type*} [Group G] (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2) (S B : Subgroup G)
    [Finite S] (hS : IsPGroup p S) (hB : B ≤ S)
    (hBab : Submission.Blueprint.IsAbelianSubgroup B)
    (hBn : S ≤ Subgroup.normalizer (B : Set G)) :
    ∃ A : Subgroup G, Work.GlaubermanZJ.IsMaxAbelianSubgroup S A ∧
      B ≤ Subgroup.normalizer (A : Set G) ∧ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  obtain ⟨A, hAmax, hAN⟩ :=
    exists_maxAbelianSubgroup_le_normalizer p hp hpne S B hS hB hBab hBn
  exact ⟨A, hAmax, hAN, commutator_commutator_eq_bot hAmax.2.1 hAN⟩

end Work.GlaubermanZJ
