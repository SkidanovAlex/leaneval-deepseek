import Mathlib
import Submission.Work.ThompsonFrobenius.Minimal
import Submission.Work.ThompsonFrobenius.induced_isFpf
import Submission.Work.ThompsonFrobenius.Structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

/-- The cardinality of a proper quotient `G ⧸ N` is strictly smaller than `|G|`, for `N ≠ ⊥`. -/
theorem natCard_quotient_lt {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have h1 : Nat.card G = Nat.card (G ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN
  have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  calc Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N :=
        (Nat.lt_mul_iff_one_lt_right h3).mpr h2
    _ = Nat.card G := h1.symm

theorem invariant_normal_eq_bot_or_top {Q : Type} [Group Q] [Finite Q] {α : MulAut Q} (h : Work.ThompsonFrobenius.IsMinimalCounterexample Q α) {N : Subgroup Q} [N.Normal] (hN : Work.NPC.Fpf.IsInv α N) : N = ⊥ ∨ N = ⊤ := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  by_cases htop : N = ⊤
  · exact Or.inr htop
  exfalso
  -- `N` is a proper `α`-invariant subgroup, hence nilpotent.
  haveI hNilN : Group.IsNilpotent ↥N := h.invariant_nilpotent N hN htop
  -- The automorphism induced by `α` on `Q ⧸ N` is again fixed-point-free of prime order.
  have hβ := induced_isFpf (G := Q) (H := N) h.orderOf_prime (pow_orderOf_eq_one α) h.fpf hN htop
  have hord : orderOf (QuotientGroup.congr N N α (by simpa using hN.map_eq)) = orderOf α := hβ.1
  have hfpfβ : Work.NPC.Fpf.IsFpf (QuotientGroup.congr N N α (by simpa using hN.map_eq)) :=
    hβ.2
  -- `Q ⧸ N` is a smaller group admitting such an automorphism, hence nilpotent by induction.
  haveI hNilQ : Group.IsNilpotent (Q ⧸ N) :=
    h.below (Q ⧸ N) (QuotientGroup.congr N N α (by simpa using hN.map_eq))
      (natCard_quotient_lt N hbot) (hord ▸ h.orderOf_prime) hfpfβ
  -- So `Q` is solvable, and the delivered solvable case gives nilpotency, a contradiction.
  haveI : Group.IsSolvable Q := Group.isSolvable_of_subgroup_quotient N
  exact h.not_nilpotent (isNilpotent_of_fpf_of_solvable h.orderOf_prime h.fpf)

end Work.ThompsonFrobenius
