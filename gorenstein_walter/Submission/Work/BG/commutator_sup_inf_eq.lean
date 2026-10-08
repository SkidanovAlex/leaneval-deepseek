import Mathlib
import Submission.Work.BG.commutator_sup_le_commutator_sup_sup
import Submission.Work.BG.inf_sup_eq_right_of_commute

namespace Work.BG

open scoped commutatorElement
open Subgroup

open Subgroup in
theorem commutator_sup_inf_eq {G : Type*} [Group G] (A C : Subgroup G)
    (hAC : ⁅A, C⁆ = ⊥) (hinf : A ⊓ C = ⊥) :
    (⁅A ⊔ C, A ⊔ C⁆) ⊓ C = ⁅C, C⁆ := by
  -- `A` and `C` commute elementwise.
  have hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a := by
    intro a ha c hc
    have h : a ∈ centralizer (C : Set G) := (commutator_eq_bot_iff_le_centralizer.mp hAC) ha
    exact (mem_centralizer_iff.mp h c hc).symm
  -- `⁅A, A⁆` meets `C` trivially, since `⁅A, A⁆ ≤ A` and `A ⊓ C = ⊥`.
  have hAinf : ⁅A, A⁆ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf (commutator_le_self A) le_rfl).trans hinf.le
  -- Hence `⁅A, A⁆` and `⁅C, C⁆` commute elementwise.
  have hcommK : ∀ p ∈ ⁅A, A⁆, ∀ q ∈ ⁅C, C⁆, p * q = q * p :=
    fun p hp q hq => hcomm p (commutator_le_self A hp) q (commutator_le_self C hq)
  -- The commutator subgroup of `A ⊔ C` is contained in `⁅A, A⁆ ⊔ ⁅C, C⁆`; intersecting
  -- with `C` hands back `⁅C, C⁆`, because `⁅A, A⁆` is disjoint from `C`.
  refine le_antisymm ?_ ?_
  · calc (⁅A ⊔ C, A ⊔ C⁆) ⊓ C
        ≤ (⁅A, A⁆ ⊔ ⁅C, C⁆) ⊓ C :=
          inf_le_inf_right C (commutator_sup_le_commutator_sup_sup A C hcomm)
      _ = ⁅C, C⁆ :=
          inf_sup_eq_right_of_commute ⁅A, A⁆ ⁅C, C⁆ C hcommK (commutator_le_self C) hAinf
  · exact le_inf (commutator_mono le_sup_right le_sup_right) (commutator_le_self C)

end Work.BG
