import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_conj_of_prime_dvd
import Submission.Work.ZassenhausSuzuki.Odd.card_range_conj_eq_index_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of conjugates of a member of the Bender–Suzuki family

Let `G` be a finite group, `A` a subgroup lying in the Bender–Suzuki family
`ℱ = Work.ZassenhausSuzuki.Odd.IsCZ` (the centralisers of the non-involution strongly real
elements), and `kA A = [N_G(A) : A]`.  This module proves the counting identity

`(number of conjugates of A that lie in ℱ) * (|A| * [N_G(A) : A]) = |G|`

of Suzuki 1962 §10: since `ℱ` is closed under conjugation (`isCZ_conj`), the members of `ℱ`
conjugate to `A` are exactly the conjugates `g A g⁻¹` of `A`, and there are `[G : N_G(A)]` of
them (`card_range_conj_eq_index_normalizer`: orbit–stabilizer for the conjugation action).  The
index of a subgroup is multiplicative (`Subgroup.card_mul_index`), so

`[G : N_G(A)] * (|A| * [N_G(A) : A]) = [G : N_G(A)] * |N_G(A)| = |G|`.

The Suzuki hypothesis bundle `SzOddHyp` is not used in the proof: the identity is a general fact
about a subgroup and its conjugates.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki.Odd

open Submission.Blueprint

/-- `A`, regarded as a subgroup of its normaliser `N_G(A)`, has as many elements as `A`. -/
theorem card_subgroupOf_normalizer {G : Type} [Group G] (A : Subgroup G) :
    Nat.card ↥(A.subgroupOf (Subgroup.normalizer (A : Set G))) = Nat.card ↥A := by
  rw [← Subgroup.card_map_of_injective
      (f := (Subgroup.normalizer (A : Set G)).subtype)
      (K := A.subgroupOf (Subgroup.normalizer (A : Set G)))
      (Subgroup.subtype_injective _),
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Subgroup.le_normalizer]

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **The number of conjugates of a member of `ℱ`.**  If `A` lies in the Bender–Suzuki family,
then the members of the family conjugate to `A` are the `[G : N_G(A)]` conjugates of `A`, and

`[G : N_G(A)] * (|A| * [N_G(A) : A]) = |G|`. -/
theorem card_conjugates (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) {A : Subgroup G}
    (hA : Work.ZassenhausSuzuki.Odd.IsCZ A) :
    Nat.card {B : Subgroup G // Work.ZassenhausSuzuki.Odd.IsCZ B ∧
        ∃ g : G, B = Submission.Blueprint.conj g A}
      * (Nat.card ↥A * Work.ZassenhausSuzuki.Odd.kA A) = Nat.card G := by
  classical
  -- `ℱ` is closed under conjugation, so the members of `ℱ` conjugate to `A` are exactly the
  -- conjugates of `A`, i.e. the orbit of `A` under conjugation.
  have hcard : Nat.card {B : Subgroup G // IsCZ B ∧ ∃ g : G, B = conj g A}
      = Nat.card (Set.range (fun g : G => conj g A)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun B => ?_))
    exact ⟨fun hB => hB.2.imp (fun g hg => hg.symm),
      fun hB => ⟨hB.choose_spec ▸ isCZ_conj hA hB.choose,
        hB.imp (fun g hg => hg.symm)⟩⟩
  -- orbit–stabilizer: there are `[G : N_G(A)]` conjugates of `A`
  rw [hcard, card_range_conj_eq_index_normalizer]
  -- `|G| = [G : N_G(A)] * |N_G(A)|` and `|N_G(A)| = |A| * [N_G(A) : A]`
  rw [kA, ← Subgroup.index_mul_card (Subgroup.normalizer (A : Set G))]
  congr 1
  rw [← Subgroup.card_mul_index (A.subgroupOf (Subgroup.normalizer (A : Set G))),
    card_subgroupOf_normalizer]

end Work.ZassenhausSuzuki.Odd
