import Mathlib
import Submission.Work.CORE3.CosetInvCountAPI

/-!
# CORE3: `b₁` counts the involutions whose coset contains exactly one involution

Bender 1981 §3, pp. 223–224.  `bCount Hh 1` counts the nontrivial left cosets of `Hh` containing
exactly one involution.  The same number counts the *involutions* `y ∉ Hh` whose coset `y Hh`
contains exactly one involution (`cosetInvCount Hh y = 1`): the two sets are matched by
`y ↦ y Hh`.  This map is injective because a coset with a single involution determines that
involution (`cosetInvCount Hh y = 1` says the only involution of `y Hh` is `y`), and it is onto
because a coset with a single involution `x` is the coset of `x`.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- `bCount Hh 1` equals the number of involutions `y ∉ Hh` whose coset `y Hh` contains exactly
one involution. -/
theorem BCountOneEqNcardJ {G : Type} [Group G] [Finite G] (Hh : Subgroup G) :
    bCount Hh 1 =
      {y : G | orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1}.ncard := by
  classical
  have hb : bCount Hh 1 =
      ({c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧
        cosetInvCount Hh (Quotient.out c) = 1} : Set (G ⧸ Hh)).ncard := rfl
  rw [hb]
  refine (Set.ncard_congr
    (s := {y : G | orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1})
    (t := {c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧ cosetInvCount Hh (Quotient.out c) = 1})
    (fun y _ => QuotientGroup.mk y) ?_ ?_ ?_).symm
  · -- the coset of `y ∈ J` is nontrivial and contains a single involution
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    obtain ⟨hy2, hyHh, hyc⟩ := hy
    refine ⟨?_, ?_⟩
    · intro hcon
      exact hyHh ((mk_eq_one_iff Hh y).mp hcon)
    · have hrel : (Quotient.out (QuotientGroup.mk y))⁻¹ * y ∈ Hh :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk y))
      rw [cosetInvCount_congr Hh hrel]
      exact hyc
  · -- injectivity: two elements of `J` with the same coset coincide
    intro y y' hy hy' heq
    simp only [Set.mem_setOf_eq] at hy hy'
    obtain ⟨hy2, -, hyc⟩ := hy
    obtain ⟨hy'2, -, -⟩ := hy'
    have hrel : y⁻¹ * y' ∈ Hh := QuotientGroup.eq.mp heq
    obtain ⟨x, -, -, huniq⟩ := exists_forall_of_cosetInvCount_eq_one Hh hyc
    have h1 : y = x := huniq y hy2 (by rw [inv_mul_cancel]; exact Hh.one_mem)
    have h2 : y' = x := huniq y' hy'2 hrel
    rw [h1, h2]
  · -- surjectivity: the unique involution of a coset with one involution
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    obtain ⟨hcne, hcc⟩ := hc
    obtain ⟨x, hx2, hxg, -⟩ := exists_forall_of_cosetInvCount_eq_one Hh hcc
    have hmkx : QuotientGroup.mk x = c := by
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq]
      have hinv : x⁻¹ * Quotient.out c = ((Quotient.out c)⁻¹ * x)⁻¹ := by group
      rw [hinv]
      exact Hh.inv_mem hxg
    refine ⟨x, ?_, hmkx⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨hx2, ?_, ?_⟩
    · intro hxHh
      exact hcne (hmkx.symm ▸ (mk_eq_one_iff Hh x).mpr hxHh)
    · rw [← cosetInvCount_congr Hh hxg]
      exact hcc

end Work.CORE3
