import Mathlib
import Submission.Work.CORE2B.four_subgroup_meets_pCore_two

/-!
# CORE2B — Bender 1981, Lemma 2.9: exclusion of the `D₁₆` case (iii)

Case (iii) of Bender's Lemma 2.9 (`T.d16`) for the soluble group `↥N` says that `O₂(N)` is a
Klein four-group and that `N/(O₂(N)O(N))` has order `3` or is dihedral of order `6`; in either
case `[(O₂(N)O(N)) : N]` divides `6`.  The counting lemma
`Work.CORE2B.four_subgroup_meets_pCore_two` (the `O₂`-half of Bender's Lemma 2.9) then forces
`V ⊓ O₂(N) ≠ ⊥` for any Klein four-group `V ≤ N`, contradicting the hypothesis `h1`.

The two ingredients are

* `(pCoreIn 2 N ⊔ oddCoreIn N).relIndex N = Nat.card (↥N ⧸ (pCore 2 ↥N ⊔ oddCore ↥N))`
  (`Subgroup.relIndex_map_map_of_injective` + `Subgroup.index_eq_card`), and
* `Nat.card (↥N ⧸ (pCore 2 ↥N ⊔ oddCore ↥N)) ∣ 6`, immediate from `hiii`
  (`DihedralGroup.nat_card` gives `|D₃| = 6`).
-/

namespace Work.CORE2B

open Subgroup

/-- **Bender 1981, Lemma 2.9, `D₁₆` case (iii) is impossible.**  If `V ≤ N` is a Klein
four-group, `O₂(N)` is a Klein four-group and `N/O₂(N)O(N)` has order `3` — or is dihedral of
order `6` — then `V` meets `O₂(N)` nontrivially; so `V ⊓ O₂(N) = ⊥` is contradictory. -/
theorem L29_d16_case_iii_excl {G : Type} [Group G] [Finite G] (N V : Subgroup G)
    (hVN : V ≤ N) (hV : Work.GW2.IsFourGroup V)
    (h1 : V ⊓ Work.GW2.pCoreIn 2 N = ⊥)
    (hiii : Work.GW2.IsFourGroup (Work.GW2.pCore 2 ↥N) ∧
      ((IsCyclic (↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) ∧
          Nat.card (↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) = 3) ∨
        Nonempty ((↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) ≃* DihedralGroup 3))) :
    False := by
  -- The relative index of `O₂(N)O(N)` in `N` is the order of the quotient `N/O₂(N)O(N)`.
  have hrel : (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N =
      Nat.card (↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) := by
    have hsup : Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N =
        Subgroup.map N.subtype (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N) := by
      rw [Work.GW2.pCoreIn, Work.GW2.oddCoreIn, Subgroup.map_sup]
    have htop : Subgroup.map N.subtype (⊤ : Subgroup ↥N) = N := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have h4 : (Subgroup.map N.subtype
          (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)).relIndex
          (Subgroup.map N.subtype (⊤ : Subgroup ↥N))
        = (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).relIndex (⊤ : Subgroup ↥N) :=
      Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective
    rw [htop, Subgroup.relIndex_top_right, Subgroup.index_eq_card] at h4
    rw [hsup]
    exact h4
  -- Case (iii) gives that this order divides `6`.
  have h6 : Nat.card (↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) ∣ 6 := by
    classical
    rcases hiii.2 with hcyc | hdih
    · exact hcyc.2.symm ▸ (by norm_num : (3 : ℕ) ∣ 6)
    · have e := Classical.choice hdih
      have hcard : Nat.card (↥N ⧸ (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)) = 6 := by
        rw [Nat.card_congr e.toEquiv]
        exact DihedralGroup.nat_card
      exact hcard.symm ▸ (by norm_num : (6 : ℕ) ∣ 6)
  -- The counting lemma contradicts `V ⊓ O₂(N) = ⊥`.
  exact four_subgroup_meets_pCore_two N V hVN hV (hrel.symm ▸ h6) h1

end Work.CORE2B
