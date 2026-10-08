import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- `Q₀ = Inv(H) ∪ {1}` is, when the involutions of `H` commute pairwise, an elementary abelian
2-subgroup of `G`, equal to `Q₀sub H = ⟨Q₀⟩`; consequently `Q₀sub H` is a subgroup of exponent
`2`, abelian, normalised by `H`, and every one of its non-identity elements is an involution
of `H`.  (Peterfalvi II Ch. V §1: the involutions of `H` commute.) -/
theorem Q0sub_elementary {G : Type} [Group G] (H : Subgroup G) (hcomm : ∀ u ∈ Submission.Blueprint.involutions (H : Set G), ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u) : (∀ x ∈ Work.ThmF.Q0sub H, x * x = 1) ∧ (∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x) ∧ (∀ h ∈ H, ∀ x ∈ Work.ThmF.Q0sub H, h * x * h⁻¹ ∈ Work.ThmF.Q0sub H) ∧ (∀ x ∈ Work.ThmF.Q0sub H, x ≠ 1 → x ∈ Submission.Blueprint.involutions (H : Set G)) := by
  have hxx : ∀ x ∈ Work.ThmF.Q0 (H : Subgroup G), x * x = 1 := by
    intro x hx
    rw [Work.ThmF.mem_Q0_iff] at hx
    rcases hx with ⟨-, hxo⟩ | rfl
    · rw [← pow_two, ← hxo]; exact pow_orderOf_eq_one x
    · rw [mul_one]
  -- `Q₀ H` is closed under multiplication, inversion and contains `1`: it is a subgroup.
  let Qgrp : Subgroup G :=
    { carrier := Work.ThmF.Q0 (H : Subgroup G)
      one_mem' := Work.ThmF.one_mem_Q0 H
      mul_mem' := by
        intro x y hx hy
        rw [Work.ThmF.mem_Q0_iff] at hx hy ⊢
        rcases hy with ⟨hyH, hyo⟩ | hy1
        · rcases hx with ⟨hxH, hxo⟩ | hx1
          · by_cases hxy : x * y = 1
            · exact Or.inr hxy
            · refine Or.inl ⟨H.mul_mem hxH hyH, ?_⟩
              apply orderOf_eq_prime
              · have hc : Commute x y := hcomm x ⟨hxH, hxo⟩ y ⟨hyH, hyo⟩
                rw [Commute.mul_pow hc]
                rw [show x ^ 2 = 1 from by rw [← hxo]; exact pow_orderOf_eq_one x,
                    show y ^ 2 = 1 from by rw [← hyo]; exact pow_orderOf_eq_one y, mul_one]
              · exact hxy
          · subst hx1; exact Or.inl ⟨by simpa using hyH, by simpa using hyo⟩
        · subst hy1
          rcases hx with ⟨hxH, hxo⟩ | hx1
          · exact Or.inl ⟨by simpa using hxH, by simpa using hxo⟩
          · subst hx1; exact Or.inr (by simp)
      inv_mem' := by
        intro x hx
        rw [Work.ThmF.mem_Q0_iff] at hx ⊢
        rcases hx with ⟨hxH, hxo⟩ | hx1
        · refine Or.inl ⟨H.inv_mem hxH, ?_⟩
          rw [orderOf_inv, hxo]
        · subst hx1; exact Or.inr inv_one }
  -- `Q₀sub H = ⟨Q₀ H⟩` is the closure of a subgroup, hence equal to it.
  have hle1 : Work.ThmF.Q0sub H ≤ Qgrp := by
    rw [Work.ThmF.Q0sub]
    exact (Subgroup.closure_le Qgrp).mpr (fun x hx => hx)
  have hle2 : Qgrp ≤ Work.ThmF.Q0sub H := by
    intro x hx
    rw [Work.ThmF.Q0sub]
    exact Subgroup.subset_closure hx
  have hEq : (Work.ThmF.Q0sub H : Subgroup G) = Qgrp := le_antisymm hle1 hle2
  have hmem : ∀ x, x ∈ Work.ThmF.Q0sub H ↔ x ∈ Work.ThmF.Q0 (H : Subgroup G) := by
    intro x; rw [hEq]; exact Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; exact hxx x ((hmem x).mp hx)
  · intro x hx y hy
    have hx' : x ∈ Work.ThmF.Q0 (H : Subgroup G) := (hmem x).mp hx
    have hy' : y ∈ Work.ThmF.Q0 (H : Subgroup G) := (hmem y).mp hy
    rw [Work.ThmF.mem_Q0_iff] at hx' hy'
    rcases hx' with ⟨hxH, hxo⟩ | hx1
    · rcases hy' with ⟨hyH, hyo⟩ | hy1
      · exact hcomm x ⟨hxH, hxo⟩ y ⟨hyH, hyo⟩
      · subst hy1; rw [mul_one, one_mul]
    · subst hx1; rw [one_mul, mul_one]
  · intro h hh x hx
    apply (hmem _).mpr
    have hx' : x ∈ Work.ThmF.Q0 (H : Subgroup G) := (hmem x).mp hx
    rw [Work.ThmF.mem_Q0_iff] at hx' ⊢
    rcases hx' with ⟨hxH, hxo⟩ | hx1
    · refine Or.inl ⟨H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh), ?_⟩
      have hhconj : h * x * h⁻¹ = (MulAut.conj h) x := by rw [MulAut.conj_apply]
      rw [hhconj]
      exact (orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x).trans hxo
    · subst hx1; exact Or.inr (by group)
  · intro x hx hne
    have hx' : x ∈ Work.ThmF.Q0 (H : Subgroup G) := (hmem x).mp hx
    rw [Work.ThmF.mem_Q0_iff] at hx'
    rcases hx' with h | h
    · exact h
    · exact absurd h hne

end Work.ThmF.ChV12
