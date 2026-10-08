/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: `A / A²` is an irreducible `ξ`-module

Higman, *Suzuki 2-groups* (1963), §3.  For a `ξ`-invariant abelian normal subgroup `A` of a
Suzuki 2-group the quotient `A / A²` is isomorphic (via the `2 ^ (e-1)`-st power map, `2 ^ e`
being the exponent of `A`) to `A ∩ Ω₁(P)`, on which `ξ` acts transitively on the non-identity
elements.  Hence `A / A²` is irreducible: there is no `ξ`-invariant subgroup strictly between
`A²` and `A`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- `A ∩ Ω₁(P)` has no proper nontrivial `ξ`-invariant subgroup. -/
theorem inf_omega1_eq_bot_or_top (h : IsSuzuki2Grp P) {A S : Subgroup P}
    (hS : S ≤ A ⊓ (omega1 P : Subgroup P))
    (hSin : S.map (h.xi : MulAut P).toMonoidHom = S) :
    S = ⊥ ∨ S = A ⊓ (omega1 P : Subgroup P) := by
  rcases eq_or_ne S ⊥ with hbot | hne
  · exact Or.inl hbot
  right
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hxS : (x : P) ∈ S := x.2
  have hx1' : (x : P) ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hx2 : orderOf (x : P) = 2 := by
    have hd : orderOf (x : P) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp (Subgroup.mem_inf.mp (hS hxS)).2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1'
    · exact h2
  have hpres : ∀ k : ℕ, ∀ y : P, y ∈ S → (h.xi ^ k) y ∈ S := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have hz : (h.xi ^ k) y ∈ S := ih y hy
      have hgoal : (h.xi ^ (k + 1)) y = h.xi.toMonoidHom ((h.xi ^ k) y) := by
        rw [pow_succ', MulAut.mul_apply]; rfl
      rw [hgoal]
      have hmem : h.xi.toMonoidHom ((h.xi ^ k) y) ∈ S.map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hSin] at hmem
  refine le_antisymm hS ?_
  rintro y hy
  rcases eq_or_ne y 1 with rfl | hy1
  · exact S.one_mem
  · have hy2 : orderOf y = 2 := by
      have hd : orderOf y ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp (Subgroup.mem_inf.mp hy).2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h2
    obtain ⟨k, hk⟩ := h.trans (x : P) y hx2 hy2
    rw [← hk]
    exact hpres k (x : P) hxS

/-- **No `ξ`-invariant subgroup strictly between `A²` and `A`.** -/
theorem xi_invariant_eq_powSub_two_or_self (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : IsXiAbelNormal h A) (hDA : D ≤ A) (hD2 : powSub A 2 ≤ D)
    (hDin : D.map (h.xi : MulAut P).toMonoidHom = D) :
    D = powSub A 2 ∨ D = A := by
  classical
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · -- then `A = ⊥` and both are trivial
    have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hh := he1 x hx
      simpa [he0] using hh
    left
    have hDbot : D = ⊥ := le_bot_iff.mp (hDA.trans (le_of_eq hbot))
    rw [hDbot, hbot]
    exact le_antisymm bot_le (powSub_le (by norm_num : 0 < 2))
  · set k : ℕ := 2 ^ (e - 1) with hk
    have hk2 : k * 2 = 2 ^ e := by
      rw [hk, ← pow_succ]
      congr 1
      omega
    -- the `k`-th power map on `A` lands in `Ω₁`
    have hpow_omega : ∀ x ∈ A, x ^ k ∈ omega1 P := by
      intro x hx
      rw [h.mem_omega1, ← pow_mul, hk2]
      exact he1 x hx
    -- `S = D ^ k` is a `ξ`-invariant subgroup of `A ∩ Ω₁`
    have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x :=
      fun x hx y hy => hA.abelian x (hDA hx) y (hDA hy)
    have hSsub : powSub D k ≤ A ⊓ (omega1 P : Subgroup P) := by
      intro y hy
      obtain ⟨x, hxD, hyx⟩ := (mem_powSub_iff hDab).mp hy
      rw [← hyx]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem A (hDA hxD) k, hpow_omega x (hDA hxD)⟩
    have hSin : (powSub D k).map (h.xi : MulAut P).toMonoidHom = powSub D k :=
      map_powSub (h.xi : MulAut P) hDin k
    rcases inf_omega1_eq_bot_or_top h hSsub hSin with hSbot | hStop
    · -- then `D ⊆ A²`
      left
      refine le_antisymm ?_ hD2
      intro x hx
      have hxk : x ^ k ∈ powSub D k := pow_mem_powSub hx
      rw [hSbot] at hxk
      simp only [Subgroup.mem_bot] at hxk
      exact (hkey x (hDA hx)).mpr hxk
    · -- then `D = A`
      right
      refine le_antisymm hDA ?_
      intro a ha
      have hak : a ^ k ∈ A ⊓ (omega1 P : Subgroup P) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem A ha k, hpow_omega a ha⟩
      rw [← hStop] at hak
      obtain ⟨d, hdD, hd⟩ := (mem_powSub_iff hDab).mp hak
      have hmem : d⁻¹ * a ∈ powSub A 2 := by
        rw [hkey _ (A.mul_mem (A.inv_mem (hDA hdD)) ha)]
        have hcomm : Commute d⁻¹ a := hA.abelian d⁻¹ (A.inv_mem (hDA hdD)) a ha
        rw [hcomm.mul_pow k, inv_pow, hd, inv_mul_cancel]
      have : a = d * (d⁻¹ * a) := by group
      rw [this]
      exact D.mul_mem hdD (hD2 hmem)

end Work.Higman
