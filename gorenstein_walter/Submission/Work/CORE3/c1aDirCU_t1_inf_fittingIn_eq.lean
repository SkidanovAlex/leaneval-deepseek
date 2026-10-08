import Mathlib
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.CORE3.c1aDirPcommF3

/-!
# `(C_U(t₁)) ∩ F(U) = O_3(U)` in Bender 1981 §3a

Bender 1981, §3, p. 223 (subcase `Ĥ = H`): with `U = O(H)`, `t₁ ∈ S − S₀` and `F_{3'}(U)`
inverted by `t₁`, the `t₁`-fixed part of the Fitting subgroup of `U` is exactly the `3`-core:

`(U ∩ C_G(t₁)) ∩ F(U) = O_3(U)`.

This is the "`C_U(t₁) = C_U(S) × O_p(U)`" display of Bender's §3a restricted to the Fitting
subgroup; it is the conjunct that pins down `B₁ ∩ K₂ = O_p(U)` in the `IsInternalDirect`
hypothesis of Theorem C.

Route.  `⊇` is immediate: `O_3(U) ≤ F(U)` (the prime cores lie in the Fitting subgroup) and
`O_3(U) ≤ C_G(t₁)` by `D.cent` (`p = 3`).  For `⊆`, take `x ∈ U ∩ C_G(t₁) ∩ F(U)`.  Since
`F(U) = F_{3'}(U) ⊔ O_3(U)` (nilpotent splitting at the prime `3`, `c1aFittingIn_eq_sup_three`),
write `x = a · b` with `a ∈ F_{3'}(U)`, `b ∈ O_3(U)`.  Conjugating by `t₁` multiplies the two
factors separately: `t₁ x t₁⁻¹ = a⁻¹ · b`, because `t₁` inverts `F_{3'}(U)` (the hypothesis
`hInv1`) and centralizes `O_3(U)` (`D.cent`).  But `t₁` centralizes `x`, so `a⁻¹ b = a b`,
i.e. `a⁻¹ = a` and `a² = 1`; as `a ∈ F_{3'}(U) ≤ U` and `U = O(H)` has odd order, `a = 1`
(`c1aEqOneOfMulSelfOdd`) and `x = b ∈ O_3(U)`.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.CORE3

open Subgroup

/-- Every element of the Fitting subgroup `F(K)` is a product of an element of the `3'`-part
`F_{3'}(K)` and an element of the `3`-core `O_3(K)`.

`F_{3'}(K) ⊔ O_3(K) = F(K)` (`c1aFittingIn_eq_sup_three`) and `O_3(K)` normalizes
`F_{3'}(K)` (both are subgroups of `K`, and `K ≤ N_G(F_{3'}(K))`), so the join is the
set-theoretic product. -/
private theorem c1aDirCU_fittingDecomp {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ∀ y ∈ Work.GW2.fittingIn K,
      ∃ a ∈ Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K, ∃ b ∈ Work.GW2.pCoreIn 3 K, y = a * b := by
  intro y hy
  have hKB : Work.GW2.pCoreIn 3 K ≤
      Subgroup.normalizer ((Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K : Subgroup G) : Set G) :=
    (c1aPcoreIn_le_self 3 K).trans (Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ) K)
  have hsup : (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K ⊔ Work.GW2.pCoreIn 3 K : Subgroup G) =
      Work.GW2.fittingIn K := (c1aFittingIn_eq_sup_three K).symm
  have hmem : y ∈ (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K : Set G) *
      ((Work.GW2.pCoreIn 3 K : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      (Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) K) (Work.GW2.pCoreIn 3 K) hKB, hsup]
    exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem c1aDirCU_t1_inf_fittingIn_eq (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case1aData B) (hp : D.p = 3)
    (hInv1 : Work.GW2.Inverts D.t1 (Work.GW2.fittingPiIn ({3}ᶜ) B.U)) :
    (B.U ⊓ Subgroup.centralizer ({D.t1} : Set G)) ⊓ Work.GW2.fittingIn B.U =
      Work.GW2.pCoreIn 3 B.U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUodd : Odd (Nat.card ↥(B.U)) := Work.CORE2A.bSetup_U_odd B
  -- `O_3(U) ≤ C_G(t₁)`, because `p = 3` and `D.cent` says `O_p(U) ≤ C_G(t₁)`.
  have hcent3 : Work.GW2.pCoreIn 3 B.U ≤ Subgroup.centralizer ({D.t1} : Set G) := hp ▸ D.cent
  have hleU : Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) B.U ≤ B.U :=
    (bfpf_fittingPiIn_le_fittingIn ({3}ᶜ : Set ℕ) B.U).trans (c1aFittingIn_le B.U)
  refine le_antisymm ?_ ?_
  · -- `(U ∩ C_G(t₁)) ∩ F(U) ≤ O_3(U)`
    intro x hx
    obtain ⟨⟨_hxU, hxC⟩, hxF⟩ := Subgroup.mem_inf.mp hx
    -- split `x = a · b`, `a ∈ F_{3'}(U)`, `b ∈ O_3(U)`
    obtain ⟨a, ha, b, hb, hab⟩ := c1aDirCU_fittingDecomp B.U x hxF
    have hbcent : D.t1 * b * D.t1⁻¹ = b := by
      have h := (Subgroup.mem_centralizer_iff.mp (hcent3 hb)) D.t1 (Set.mem_singleton D.t1)
      rw [show D.t1 * b = b * D.t1 from h]
      group
    -- `t₁` sends `x = a b` to `a⁻¹ b`
    have hconj : D.t1 * x * D.t1⁻¹ = a⁻¹ * b := by
      rw [hab, show D.t1 * (a * b) * D.t1⁻¹ =
        (D.t1 * a * D.t1⁻¹) * (D.t1 * b * D.t1⁻¹) from by group, hInv1 a ha, hbcent]
    -- `t₁` centralizes `x`
    have hxC' : D.t1 * x * D.t1⁻¹ = x := by
      have h := (Subgroup.mem_centralizer_iff.mp hxC) D.t1 (Set.mem_singleton D.t1)
      rw [show D.t1 * x = x * D.t1 from h]
      group
    -- so `a⁻¹ b = a b`, whence `a² = 1`, so `a = 1` (`a` lies in the odd-order `U`)
    have haeq : a⁻¹ = a := by
      have h : a⁻¹ * b = a * b := by rw [← hconj, hxC', hab]
      exact mul_right_cancel h
    have hasq : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [haeq]
        _ = 1 := mul_inv_cancel a
    have ha1 : a = 1 := c1aEqOneOfMulSelfOdd hUodd (hleU ha) hasq
    rw [show x = b from by rw [hab, ha1, one_mul]]
    exact hb
  · -- `O_3(U) ≤ (U ∩ C_G(t₁)) ∩ F(U)`
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨c1aPcoreIn_le_self 3 B.U hx, hcent3 hx⟩, c1aPcoreIn_le_fittingIn 3 B.U hx⟩

end Work.CORE3
