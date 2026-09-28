import Mathlib

/-!
# A Fubini/reindexing identity for nested `Finset` sums

For finsets `PF : Finset α`, `XF : Finset β` and two families `ZxA ZyA : α → Finset β` with
`ZxA a ⊆ XF` and `ZyA a ⊆ XF`, the triple sum grouped as `a → x → y` (with `x ∈ ZxA a`,
`y ∈ ZyA a` avoiding `x` and `-x`) can be regrouped as a sum over pairs `p ∈ XF × XF` with
`p.1 ≠ p.2` and `p.1 ≠ -p.2`, and then over the `a` with `p.1 ∈ ZxA a` and `p.2 ∈ ZyA a`.

This is the abstract combinatorial step in the proof that `D^mix` rewrites as a sum over pairs
`(x,y) ∈ Ω_{d,n}(B)`.
-/

set_option autoImplicit false

namespace Work.HP.DmixAux

/-- Reindexing a nested triple sum as a sum over pairs. -/
theorem TripleReindex {α β : Type*} [DecidableEq α] [DecidableEq β] [InvolutiveNeg β]
    (PF : Finset α) (XF : Finset β) (ZxA ZyA : α → Finset β)
    (hZx : ∀ a, ZxA a ⊆ XF) (hZy : ∀ a, ZyA a ⊆ XF) (g : α → β → ℝ) :
    (∑ a ∈ PF, ∑ x ∈ ZxA a, ∑ y ∈ (ZyA a).filter (fun y => y ≠ x ∧ y ≠ -x), g a y)
      = ∑ p ∈ (XF.product XF).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2),
          ∑ a ∈ PF.filter (fun a => p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a), g a p.2 := by
  have hneg : ∀ x y : β, (y ≠ -x) ↔ (x ≠ -y) := by
    intro x y
    have h : (y = -x) ↔ (x = -y) := by
      constructor <;> intro h <;> rw [h] <;> simp
    exact not_congr h
  have hZx_eq : ∀ a, ZxA a = XF.filter (fun x => x ∈ ZxA a) := by
    intro a
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hZx a h, h⟩, fun h => h.2⟩
  have hZy_eq : ∀ a x, (ZyA a).filter (fun y => y ≠ x ∧ y ≠ -x)
      = XF.filter (fun y => y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) := by
    intro a x
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hZy a h1, h1, Ne.symm h2, (hneg x y).mp h3⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h2, Ne.symm h3, (hneg x y).mpr h4⟩
  have stepA : (∑ a ∈ PF, ∑ x ∈ ZxA a, ∑ y ∈ (ZyA a).filter (fun y => y ≠ x ∧ y ≠ -x), g a y)
      = ∑ a ∈ PF, ∑ x ∈ XF.filter (fun x => x ∈ ZxA a),
          ∑ y ∈ XF.filter (fun y => y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y), g a y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr (hZx_eq a) fun x _ => ?_
    exact Finset.sum_congr (hZy_eq a x) fun y _ => rfl
  have stepB : (∑ a ∈ PF, ∑ x ∈ XF.filter (fun x => x ∈ ZxA a),
          ∑ y ∈ XF.filter (fun y => y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y), g a y)
      = ∑ a ∈ PF, ∑ x ∈ XF,
          if x ∈ ZxA a then
            (∑ y ∈ XF, if (y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0) else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ ZxA a
    · rw [if_pos hx, if_pos hx, Finset.sum_filter]
    · rw [if_neg hx, if_neg hx]
  have stepC : (∑ a ∈ PF, ∑ x ∈ XF,
          if x ∈ ZxA a then
            (∑ y ∈ XF, if (y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0) else 0)
      = ∑ a ∈ PF, ∑ x ∈ XF, ∑ y ∈ XF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ ZxA a
    · rw [if_pos hx]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h : (y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y)
      · rw [if_pos h, if_pos ⟨hx, h⟩]
      · rw [if_neg h, if_neg (fun hc => h hc.2)]
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg (fun hc => hx hc.1)]
  have stepD1 : (∑ a ∈ PF, ∑ x ∈ XF, ∑ y ∈ XF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0))
      = ∑ x ∈ XF, ∑ a ∈ PF, ∑ y ∈ XF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0) :=
    Finset.sum_comm
  have stepD2 : (∑ x ∈ XF, ∑ a ∈ PF, ∑ y ∈ XF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0))
      = ∑ x ∈ XF, ∑ y ∈ XF, ∑ a ∈ PF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have stepE : (∑ x ∈ XF, ∑ y ∈ XF, ∑ a ∈ PF,
          (if (x ∈ ZxA a ∧ y ∈ ZyA a ∧ x ≠ y ∧ x ≠ -y) then g a y else 0))
      = ∑ p ∈ XF.product XF, ∑ a ∈ PF,
          (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2) then g a p.2 else 0) :=
    (Finset.sum_product XF XF (fun p => ∑ a ∈ PF,
      (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2) then g a p.2 else 0))).symm
  have stepF : (∑ p ∈ XF.product XF, ∑ a ∈ PF,
          (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2) then g a p.2 else 0))
      = ∑ p ∈ (XF.product XF).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2), ∑ a ∈ PF,
          (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2) then g a p.2 else 0) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpn => ?_
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    intro hc
    exact hpn (Finset.mem_filter.mpr ⟨hp, hc.2.2⟩)
  rw [stepA, stepB, stepC, stepD1, stepD2, stepE, stepF]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  have h1 : (∑ a ∈ PF,
        (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2) then g a p.2 else 0))
      = ∑ a ∈ PF, (if (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a) then g a p.2 else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : (p.1 ∈ ZxA a ∧ p.2 ∈ ZyA a)
    · rw [if_pos ⟨h.1, h.2, hp.2.1, hp.2.2⟩, if_pos h]
    · rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩), if_neg h]
  rw [h1, ← Finset.sum_filter]

end Work.HP.DmixAux
